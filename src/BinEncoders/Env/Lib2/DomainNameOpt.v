Require Import
        Bedrock.Word
        Coq.Strings.Ascii
        Coq.Strings.String.

Require Import
        Fiat.Computation.Core
        Fiat.Computation.FixComp
        Fiat.Computation.Notations
        Fiat.Examples.DnsServer.Packet
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.FixStringOpt
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.AsciiOpt.

Section DomainName.
  Context {B : Type}. (* bin type *)
  Context {cache : Cache}.
  Context {cache_inv : CacheDecode -> Prop}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  (* The terminal character for domain names is the byte of all zeros. *)
  Definition terminal_char : ascii := zero.
  Definition pointerT := word 6.

  Context {cacheAdd : CacheAdd cache (string * pointerT)}.
  Context {cacheGet : CacheGet cache string pointerT}.
  Context {cachePeek : CachePeek cache pointerT}.

  Variable cacheGet_OK :
    forall env p domain,
      cache_inv env
      -> getD env p = Some domain
      -> ValidDomainName domain /\ (String.length domain > 0)%nat .

  Variable cacheAdd_OK :
    forall env p domain,
      cache_inv env
      -> (ValidDomainName domain /\ String.length domain > 0)%nat
        -> cache_inv (addD env (domain, p)).
  Open Scope comp_scope.

  Import FixComp.LeastFixedPointFun.
  Print LeastFixedPoint.

  Definition encode_DomainName_Spec (domain : DomainName) (env : CacheEncode)
    : Comp (B * CacheEncode) :=
    LeastFixedPoint
      (fDom := [DomainName; CacheEncode])
      (fun encode_DomainName_Spec domain env =>
    If (string_dec domain "") Then
         encode_ascii_Spec terminal_char env
    Else
    (Ifopt (getE env domain) as position Then
        b <- {b : bool | True};
          If b Then (* Nondeterministically pick whether to use a cached value. *)
             (encode_word_Spec position env)
             Else (`(label, domain') <- { labeldomain' |
                                          domain = (fst labeldomain') ++ (snd labeldomain')
                                          /\ ValidLabel (fst labeldomain')
                                          /\ (forall label' post',
                                                 domain = label' ++ post'
                                                 -> ValidLabel label'
                                                 -> String.length label' <= String.length (fst labeldomain'))}%string%nat;
                     `(lenb, env') <- encode_word_Spec (natToWord 8 (String.length label)) env;
                     `(labelb, env') <- encode_string_Spec label env';
                     `(domainb, env') <- encode_DomainName_Spec domain' env';
                     ret (transform (transform lenb labelb) domainb, addE env (domain, peekE env)))
             Else
             (`(label, domain') <- { labeldomain' |
                                          domain = (fst labeldomain') ++ (snd labeldomain')
                                          /\ ValidLabel (fst labeldomain')
                                          /\ (forall label' post',
                                                 domain = label' ++ post'
                                                 -> ValidLabel label'
                                                 -> String.length label' <= String.length (fst labeldomain'))}%string%nat;
                     `(lenb, env') <- encode_word_Spec (natToWord 8 (String.length label)) env;
                     `(labelb, env') <- encode_string_Spec label env';
                     `(domainb, env') <- encode_DomainName_Spec domain' env';
                     ret (transform (transform lenb labelb) domainb, addE env (domain, peekE env))))) domain env.

  (* Decode now uses a measure on the length of B *)

  Lemma lt_B_trans :
    forall b
           (b1 : {b' : B | le_B b' b})
           (b2 : {b' : B | lt_B b' (` b1)})
           (b3 : {b' : B | lt_B b' (` b2)}),
      lt_B (` b3) b.
  Proof.
    intros; destruct b1; destruct b2; destruct b3; simpl in *.
    unfold le_B, lt_B in *; omega.
  Qed.

  Lemma n_eq_0_lt :
    forall n,
      n <> wzero 6
      -> (0 < wordToNat n)%nat.
  Proof.
    induction n; unfold wzero; simpl.
    - congruence.
    - destruct b; simpl; try omega.
      intros.
      assert (n0 <> wzero n) by
          (intro; subst; apply H; f_equal).
      apply IHn in H0.
      omega.
  Qed.

  Definition decode_DomainName (b : B) (env : CacheDecode):
    option (DomainName * B * CacheDecode).
    refine (Fix well_founded_lt_b
           (fun _ => CacheDecode -> option (DomainName * B * CacheDecode))
      (fun b rec cd =>
         `(labelheader, b1, env') <- Decode_w_Measure_le (decode_word (sz := 2)) b env _;
           If (weq labelheader WO~1~1) (* It's a pointer! *)
           Then (`(ps, b2, env') <- Decode_w_Measure_le (decode_word (sz := 6)) (proj1_sig b1) env' _;
               match getD cd ps with
                 | Some EmptyString => None (* bogus *)
                 | Some domain => Some (domain, proj1_sig b2, env')
                 | None => None (* bogus *)
                 end)
           Else (If (weq labelheader WO~0~0) Then (* It's a length octet *)
         (`(labellength, b2, env') <- Decode_w_Measure_lt (decode_word (sz := 6)) (proj1_sig b1) env' _;
            match (weq labellength (wzero 6)) with (* It's the terminal character. *)
              | left _ => Some (EmptyString, proj1_sig b2, env')
              | right _ =>
             (`(label, b3, env') <- Decode_w_Measure_lt (decode_string (wordToNat labellength))
               (proj1_sig b2) env' _;
              `(domain, b4, e3) <- rec (proj1_sig b3) _ env';
              Some (label ++ domain, b4, addD env' (label ++ domain, peekD env))) end)
         Else None))%string b env);
      try solve [intros; unfold decode_word; eapply decode_word_lt; eauto];
      try solve [intros; eapply decode_word_le; eauto].
    intros; eapply decode_string_lt; try eapply H.
    apply n_eq_0_lt; eauto.
    apply lt_B_trans.
  Defined.

  Theorem DomainName_decode_correct :
    encode_decode_correct_f
      cache transformer
      (fun domain => ValidDomainName domain /\ (String.length domain > 0)%nat)
      encode_DomainName_Spec decode_DomainName cache_inv.
  Proof.
    unfold encode_decode_correct_f; split.
    { intros env xenv xenv' l l' ext Eeq Ppredh Penc;
      subst.
      unfold decode_DomainName in *; simpl in *.
      unfold encode_DomainName_Spec in Penc.
      generalize dependent l';
        generalize dependent env;
        generalize dependent xenv;
        generalize ext; generalize dependent xenv';
          induction l; intros; simpl in *.
      { unfold Bind2 in *; computes_to_inv; subst.
        destruct v; destruct v0.
        injections.
        destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 ext0) Eeq I Penc) as [? [? ?]]; subst.
        rewrite <- transform_assoc.
        rewrite Coq.Init.Wf.Fix_eq; simpl.
        let H' := fresh in
        destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
          rewrite H'; simpl; clear H'.
          destruct (proj1 A_decode_pf _ _ _ _ _ ext0 H0 A_predicate_halt Penc') as [? [? ?]]; subst.
          let H' := fresh in
          destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (A_halt_dec A_halt); simpl; eexists; eauto.
          congruence.
          intros.
          apply functional_extensionality; intros.
          repeat (f_equal; repeat (apply functional_extensionality; intros)).
      }
      destruct (getE env (a :: l)) eqn: ?.
      rewrite Coq.Init.Wf.Fix_eq; simpl.
      computes_to_inv.
      destruct v; simpl in Penc'.
      { (* Case where the encoder decided to use compression. *)
        destruct (P_predicate_dec p); simpl in Penc';
        unfold Bind2 in Penc'; computes_to_inv; injections;
        subst; destruct v; destruct v0.
        - destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 ext0) Eeq I Penc') as [? [? ?]]; subst.
          rewrite <- transform_assoc; simpl;
            let H' := fresh in
            destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
              rewrite H'; simpl; clear H'.
          destruct (proj1 P_decode_pf _ _ _ _ _ ext0 H0 p0 Penc'') as [? [? ?]];
           let H' := fresh in
            destruct (Decode_w_Measure_le_eq _ _ _ P_decode_le H1) as [? H'];
              rewrite H'; simpl; clear H'.
          eapply get_correct in Heqo; eauto; rewrite Heqo.
          eauto.
        - destruct v1.
          destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0))
                          Eeq I Penc') as [? [? ?]]; subst.
          rewrite <- !transform_assoc; simpl.
          let H' := fresh in
          destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (proj1 A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (Ppredh _ (or_introl _ eq_refl))) Penc'') as [? [? ?]]; subst.
          let H' := fresh in
          destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (A_halt_dec a); simpl.
          elimtype False; apply (proj2 (Ppredh _ (or_introl _ eq_refl)));
            eauto.
          eapply (fun H => IHl H _ ext0) in Penc'''; intros.
          destruct_ex; intuition.
          rewrite H4; simpl.
          eexists; intuition eauto.
          erewrite peek_correct.
          eapply add_correct.
          eauto.
          eauto.
          eapply Ppredh; eauto.
          eauto.
      }
      {
        unfold Bind2 in Penc'; computes_to_inv; injections;
        subst; destruct v; destruct v0; destruct v1.
        - destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0)) Eeq I Penc') as [? [? ?]]; subst.
          rewrite <- !transform_assoc; simpl.
          let H' := fresh in
          destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (proj1 A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (Ppredh _ (or_introl _ eq_refl))) Penc'') as [? [? ?]]; subst.
          let H' := fresh in
          destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
            rewrite H'; simpl; clear H'.
          destruct (A_halt_dec a); simpl.
          elimtype False; apply (proj2 (Ppredh _ (or_introl _ eq_refl)));
            eauto.
          eapply (fun H => IHl H _ ext0) in Penc'''; intros.
          destruct_ex; intuition.
          rewrite H4; simpl.
          eexists; intuition eauto.
          erewrite peek_correct.
          eapply add_correct.
          eauto.
          eauto.
          eauto.
          eauto.
      }
      intros.
      apply functional_extensionality; intros.
      repeat (f_equal; repeat (apply functional_extensionality; intros)).
      - rewrite Coq.Init.Wf.Fix_eq; simpl.
        unfold Bind2 in Penc; computes_to_inv; injections;
          subst; destruct v; destruct v0; destruct v1;
            simpl in *.
        destruct (proj1 X_decode_pf _ _ _ _ _ (transform b0 (transform b1 ext0))
                        Eeq I Penc) as [? [? ?]]; subst.
        rewrite <- !transform_assoc; simpl.
        let H' := fresh in
        destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le H) as [? H'];
          rewrite H'; simpl; clear H'.
        destruct (proj1 A_decode_pf _ _ _ _ _ (transform b1 ext0) H0 (proj1 (Ppredh _ (or_introl _ eq_refl))) Penc') as [? [? ?]]; subst.
        let H' := fresh in
        destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt H1) as [? H'];
          rewrite H'; simpl; clear H'.
        destruct (A_halt_dec a); simpl.
        elimtype False; apply (proj2 (Ppredh _ (or_introl _ eq_refl)));
          eauto.
        eapply (fun H => IHl H _ ext0) in Penc''; intros; eauto.
        destruct_ex; intuition.
        rewrite H4; simpl.
        eexists; intuition eauto.
        erewrite peek_correct.
        eapply add_correct.
        eauto.
        eauto.
        intros.
        apply functional_extensionality; intros.
        repeat (f_equal; repeat (apply functional_extensionality; intros)).
    }
    { unfold decode_list_step, encode_list_step_Spec.
      intros env env' xenv' data bin;
        revert env env' xenv' data.
      eapply (@well_founded_induction _ _ well_founded_lt_b) with
      (a := bin); intros.
      rewrite Coq.Init.Wf.Fix_eq in H2; simpl.
      destruct (X_decode x env')
        as [ [ [ [ | ] ?] ?] | ] eqn: Heqo; simpl in *;
        first [eapply (Decode_w_Measure_le_eq' _ _ _ X_decode_le) in Heqo;
               rewrite Heqo in H2; simpl in H2; discriminate
              | let H' := fresh in
                destruct (Decode_w_Measure_le_eq _ _ _ X_decode_le Heqo) as [? H'];
                rewrite H' in H2; simpl in *; clear H'].
      - destruct (P_decode b c)
          as [ [ [ ? ?] ?] | ] eqn: Heqo'; simpl in *;
          first [eapply (Decode_w_Measure_le_eq' _ _ _ P_decode_le) in Heqo';
               rewrite Heqo' in H2; simpl in H2; discriminate
              | let H' := fresh in
                destruct (Decode_w_Measure_le_eq _ _ _ P_decode_le Heqo') as [? H'];
                rewrite H' in H2; simpl in *; clear H'].
        destruct (getD env' p) eqn: ?; simpl in *; try discriminate.
        injections.
        destruct l; try discriminate; injections.
        eapply (proj2 X_decode_pf) in Heqo; destruct Heqo;
          destruct_ex; intuition eauto; subst;
            eapply (proj2 P_decode_pf) in Heqo'; destruct Heqo';
              destruct_ex; intuition eauto; subst.
        rewrite (proj2 (get_correct _ _ _ _ H0) Heqo0).
        eexists; eexists; intuition eauto.
        computes_to_econstructor.
        apply (@PickComputes _ _ true); eauto.
        simpl.
        destruct (P_predicate_dec p).
        repeat computes_to_econstructor; eauto.
        intuition.
        simpl; rewrite transform_assoc; reflexivity.
        pose proof (cacheGet_OK _ _ _ H1 Heqo0 _ H6); intuition.
        pose proof (cacheGet_OK _ _ _ H1 Heqo0 _ H6); intuition.
      - destruct (A_decode b c)
          as [ [ [ ? ?] ?] | ] eqn: Heqo'; simpl in *;
          first [eapply (Decode_w_Measure_lt_eq' _ _ _ A_decode_lt) in Heqo';
                 rewrite Heqo' in H2; simpl in H1; discriminate
                | let H' := fresh in
                  destruct (Decode_w_Measure_lt_eq _ _ _ A_decode_lt Heqo') as [? H'];
                  rewrite H' in H2; simpl in *; clear H'].
        eapply (proj2 X_decode_pf) in Heqo; eauto;
          destruct Heqo; destruct_ex;
            eauto; subst;
              eapply (proj2 A_decode_pf) in Heqo'; eauto;
                destruct Heqo'; destruct_ex;
                  eauto; subst; split_and; eauto.
        destruct (A_halt_dec a); simpl in *.
        + injections; simpl.
          intuition.
          eexists; eexists; intuition.
          computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
          unfold le_B in x0.
          simpl; rewrite transform_assoc; reflexivity.
          eauto.
        + match type of H2 with
            context [Fix well_founded_lt_b ?P ?f ?b ?c] =>
            destruct (Fix well_founded_lt_b P f b c)
              as [ [ [ ? ?] ?] | ] eqn: ?; simpl in *; try discriminate
          end.
          simpl in H2; injections.
          split.
          * eapply cacheAdd_OK.
            eapply H12 in Heqo; eauto.
            unfold le_B, lt_B in *; omega.
            simpl; intros; intuition subst; eauto.
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eapply H16; eauto.
            unfold le_B, lt_B in *; omega.
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eapply H16; eauto.
            unfold le_B, lt_B in *; omega.
          * destruct (getE env (a :: l)) eqn : ? .
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eexists; eexists; intuition eauto.
            computes_to_econstructor.
            apply (@PickComputes _ _ false); eauto.
            simpl.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            subst; rewrite !transform_assoc; reflexivity.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl.
            erewrite peek_correct; eauto.
            eapply add_correct; eauto.
            unfold le_B, lt_B in *; omega.
            eapply H14 in Heqo; eauto; destruct_ex; intuition.
            eexists; eexists; intuition eauto.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            computes_to_econstructor; eauto.
            subst; rewrite !transform_assoc; reflexivity.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl in *; intuition subst; eauto.
            eapply H6; eauto.
            simpl.
            erewrite peek_correct; eauto.
            eapply add_correct; eauto.
            unfold lt_B, le_B in *; rewrite !transform_measure.
            rewrite transform_measure in x1.
            omega.
      - intros; apply functional_extensionality; intros.
        repeat (f_equal; repeat (apply functional_extensionality; intros)).
        Grab Existential Variables.
        eauto.
    }
  Qed. *)
End DomainName.
