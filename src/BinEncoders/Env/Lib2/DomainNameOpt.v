Require Import
        Bedrock.Word
        Coq.Strings.Ascii
        Coq.Strings.String
        Coq.Logic.Eqdep_dec.

Require Import
        Fiat.Computation.Core
        Fiat.Computation.FixComp
        Fiat.Computation.Notations
        Fiat.Examples.DnsServer.Packet
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.FixStringOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.AsciiOpt.

Section DomainName.
  Context {B : Type}. (* bin type *)
  Context {cache : Cache}.
  Context {cache_inv : CacheDecode -> Prop}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  (* The terminal character for domain names is the byte of all zeros. *)
  Definition terminal_char : ascii := zero.
  Definition pointerT := (sig (wlt (natToWord 8 191)) * word 8)%type.
  Definition pointerT2Nat (p : pointerT) : nat :=
    ((wordToNat (proj1_sig (fst p)) - 192) * 256) + wordToNat (snd p).

  Lemma Nat2pointerT_pf :
    forall n,
      natToWord 8 191 < natToWord 8 (NPeano.modulo (NPeano.div n 256) 64 + 192).
  Proof.
    intros; apply WordFacts.natToWord_wlt.
    - simpl; apply Nomega.Nlt_in; simpl; compute; omega.
    - apply Nomega.Nlt_in.
      apply Lt.lt_le_trans with (m := 64 + 192);
        [ rewrite Nnat.Nat2N.id | compute; omega].
      apply Plus.plus_lt_compat_r.
      refine (proj2 (NPeano.mod_bound_pos _ _ _ _)); omega.
    - omega.
  Qed.

  Lemma div_eq: forall a b : nat,
      b <> 0
      -> b * NPeano.div a b = a - NPeano.modulo a b.
  Proof.
    intros; rewrite NPeano.Nat.mod_eq by assumption.
    rewrite sub_plus; try omega.
    apply NPeano.Nat.mul_div_le; auto.
  Qed.

  Definition Nat2pointerT (n : nat) : pointerT :=
    (exist _ _ (Nat2pointerT_pf n),
     natToWord 8 (NPeano.modulo n 256)).

  Lemma Nat2pointerT_pointerT2Nat :
    forall p, Nat2pointerT (pointerT2Nat p) = p.
  Proof.
    destruct p as [[upper_p upper_p_OK] lower_p].
    unfold pointerT2Nat; simpl.
    unfold Nat2pointerT; f_equal.
    assert ((natToWord 8 (NPeano.modulo (NPeano.div ((wordToNat upper_p - 192) * 256 + wordToNat lower_p) 256) 64 + 192)) = upper_p).
    - rewrite NPeano.Nat.div_add_l; auto with arith.
      rewrite NPeano.Nat.div_small, NPeano.Nat.add_0_r.
      rewrite NPeano.Nat.mod_eq by omega.
      replace (64 * NPeano.div (wordToNat upper_p - 192) 64) with 0.
      rewrite <- Minus.minus_n_O, NPeano.Nat.sub_add.
      apply natToWord_wordToNat.
      apply WordFacts.wordToNat_lt in upper_p_OK; eauto.
      rewrite div_eq by omega.
      apply WordFacts.wordToNat_lt in upper_p_OK; simpl in upper_p_OK.
      revert upper_p_OK; clear.
      shatter_word upper_p.
      abstract (destruct x; destruct x0; destruct x1; destruct x2;
                destruct x3; destruct x4; destruct x5; destruct x6; simpl;
                intro; try omega).
      apply wordToNat_bound.
    - generalize (Nat2pointerT_pf ((wordToNat upper_p - 192) * 256 + wordToNat lower_p));
        rewrite H; intros.
      f_equal.
      apply UIP_dec.
      decide equality.
    - rewrite Plus.plus_comm, NPeano.Nat.mod_add by omega.
      rewrite NPeano.Nat.mod_eq by omega.
      rewrite NPeano.Nat.div_small by apply wordToNat_bound.
      simpl mult; rewrite <- Minus.minus_n_O.
      apply natToWord_wordToNat.
  Qed.

  Lemma pointerT_eq_dec
    : forall p p' : pointerT, {p = p'} + {p <> p'}.
  Proof.
    intros.
    rewrite <- (Nat2pointerT_pointerT2Nat p), <- (Nat2pointerT_pointerT2Nat p').
    destruct (Peano_dec.eq_nat_dec (pointerT2Nat p) (pointerT2Nat p')).
    left; rewrite e; congruence.
    right; intro; apply n.
    rewrite !Nat2pointerT_pointerT2Nat in H; congruence.
  Qed.

  Lemma pointerT2Nat_Nat2pointerT :
    forall n,
      (n < pow2 14)%nat
      -> pointerT2Nat (Nat2pointerT n) = n.
  Proof.
    intros.
    unfold Nat2pointerT.
    unfold pointerT2Nat, fst, snd, proj1_sig.
    rewrite (NPeano.Nat.div_mod n 256) at 3 by omega.
    rewrite Mult.mult_comm.
    f_equal.
    - f_equal.
      rewrite wordToNat_natToWord_idempotent.
      rewrite NPeano.Nat.add_sub.
      rewrite NPeano.Nat.mod_eq by omega.
      replace (NPeano.div (NPeano.div n 256) 64) with 0.
      omega.
      rewrite NPeano.Nat.div_div by omega.
      replace (256 * 64) with (pow2 14) by reflexivity.
      symmetry; apply NPeano.Nat.div_small; auto.
      replace (Npow2 8) with (BinNat.N.of_nat 256) by reflexivity.
      eapply Nomega.Nlt_in.
      rewrite !Nnat.Nat2N.id.
      assert (64 <> 0) by omega.
      pose proof (NPeano.Nat.mod_upper_bound (NPeano.div n 256) _ H0).
      omega.
    - rewrite wordToNat_natToWord_idempotent; auto.
      replace (Npow2 8) with (BinNat.N.of_nat 256) by reflexivity.
      eapply Nomega.Nlt_in.
      rewrite !Nnat.Nat2N.id.
      apply NPeano.Nat.mod_upper_bound; omega.
  Qed.

  Lemma terminal_char_eq :
    forall x0, terminal_char = ascii_of_N (wordToN x0)
               -> x0 = wzero 8.
  Proof.
    intros.
    unfold terminal_char, zero in H.
    shatter_word x0.
    simpl in H.
    repeat (find_if_inside; simpl in H);
      try discriminate.
    reflexivity.
  Qed.

  Context {cacheGet : CacheGet cache string pointerT}.
  Context {cachePeek : CachePeek cache (option pointerT)}.
  Definition add_ptr_OK
             (t : string * pointerT)
             (ce : CacheEncode)
             (cd : CacheDecode) :=
    getD cd (snd t) = None.

  Context {cacheAdd : CacheAdd_Guarded cache add_ptr_OK}.

  (* Variable cacheGet_OK :
    cache_inv_Property
      cache_inv
      (fun P => forall env p domain,
           cache_inv env
           -> getD env p = Some domain
           -> ValidDomainName domain /\ (String.length domain > 0)%nat).

  Variable cacheAdd_OK :
    cache_inv_Property
      cache_inv
      (fun P => forall env p domain,
      cache_inv env
      -> (ValidDomainName domain /\ String.length domain > 0)%nat
        -> cache_inv (addD env (domain, p))). *)
  Open Scope comp_scope.

  Import FixComp.LeastFixedPointFun.

  Definition encode_DomainName_Spec (domain : DomainName) (env : CacheEncode)
    : Comp (B * CacheEncode) :=
    LeastFixedPoint
      (fDom := [DomainName; CacheEncode])
      (fun encode_DomainName_Spec domain env =>
    If (string_dec domain "") Then
         encode_ascii_Spec terminal_char env
    Else
    (position <- { position | forall p, position = Some p -> In p (getE env domain)};
    Ifopt position as position Then (* Nondeterministically pick whether to use a cached value. *)
             (`(ptr1b, env') <- encode_word_Spec (proj1_sig (fst position)) env;
              `(ptr2b, env') <- encode_word_Spec (snd position) env';
              ret (transform ptr1b ptr2b, env'))
    Else
    (`(label, domain') <- { labeldomain' |
                            (domain = (fst labeldomain') ++ String "." (snd labeldomain') \/ labeldomain' = (domain, ""))
                            /\ ValidLabel (fst labeldomain')
                            /\ (forall label' post',
                                   domain = label' ++ post'
                                   -> ValidLabel label'
                                   -> String.length label' <= String.length (fst labeldomain'))}%string%nat;
       `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
       `(labelb, env') <- encode_string_Spec label env';
       `(domainb, env') <- encode_DomainName_Spec domain' env';
       ret (transform (transform lenb labelb) domainb,
            (* If the pointer would overflow, don't record *)
            Ifopt peekE env as curPtr Then addE_G env' (domain, curPtr)
                                      Else env'
      )))) domain env.

  (* Decode now uses a measure on the length of B *)
  Lemma lt_B_trans :
    forall b
           (b1 : {b' : B | le_B b' b})
           (b3 : {b' : B | lt_B b' (` b1)}),
      lt_B (` b3) b.
  Proof.
    intros; destruct b1; destruct b3; simpl in *.
    unfold le_B, lt_B in *; omega.
  Qed.


  Lemma n_eq_0_lt :
    forall n,
      n <> wzero 8
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

  Lemma append_assoc :
    forall s1 s2 s3,
      (s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3)%string.
  Proof.
    induction s1; simpl; auto.
    intros; rewrite IHs1; reflexivity.
  Qed.

  Lemma length_append :
    forall s1 s2,
      String.length (s1 ++ s2) = String.length s1 + String.length s2.
  Proof.
    induction s1; simpl; eauto.
  Qed.

  Lemma ValidDomainName_app
    : forall label subdomain,
      ValidLabel label ->
      ValidDomainName (label ++ (String "." subdomain))
      -> ValidDomainName subdomain.
  Proof.
    unfold ValidDomainName; split; intros.
    - eapply H0; try eassumption.
      rewrite H1.
      change (String "." (pre ++ label0 ++ post)%string) with
      ((String "." pre) ++ label0 ++ post)%string.
      rewrite append_assoc.
      reflexivity.
    - destruct H0; subst.
      destruct (H2 (label ++ String "." pre)%string post) as [? [? [? ?] ] ].
      rewrite <- !append_assoc; f_equal.
      repeat split; eauto.
      intro; apply H5; subst.
      eexists; simpl; eauto.
      intro; apply H5; subst.
      destruct_ex; subst.
      eexists (label ++ String "." x)%string; simpl; eauto.
      rewrite <- !append_assoc; eauto.
  Qed.

  Lemma ValidLabel_OK_split
    : forall label subdomain subdomain',
      (label ++ String "." subdomain = label ++ "." ++ subdomain')%string
      -> subdomain = subdomain'.
  Proof.
    induction label; simpl; intros; try congruence.
    injection H; intros; eauto.
  Qed.

  Lemma index_correct'
    : forall s a n,
      index 0 (String a EmptyString) s = Some n
      -> exists s' s'',
        (s = s' ++ (String a EmptyString) ++ s''
         /\ String.length s' = n)%string
        /\ index 0 (String a EmptyString) s' = None.
  Proof.
    induction s; simpl; intros; try discriminate.
    destruct (ascii_dec a0 a).
    - destruct s; simpl in H; injections.
      eexists ""%string, ""%string; split; eauto.
      eexists ""%string, _; split; simpl; eauto.
    - destruct (index 0 (String a0 EmptyString) s) eqn: ?;
        injections; try discriminate.
      apply IHs in Heqo; destruct_ex; intuition; subst.
      eexists (String a _), _; simpl; split; eauto.
      destruct (ascii_dec a0 a); try congruence.
      rewrite H1; reflexivity.
  Qed.

  Lemma split_char_inj
    : forall s s' t t',
      (s ++ String "." s' = t ++ String "." t')%string
      -> index 0 "." s = None
      -> index 0 "." t = None
      -> s = t /\ s' = t'.
  Proof.
    induction s.
    - destruct t.
      + simpl; intros; injections; intuition eauto.
      + intros; simpl in H; injection H; intros; subst.
        simpl in H1.
        destruct t; simpl in H1; discriminate.
    - intros; destruct t.
      + simpl in H; injection H; intros; subst.
        simpl in H0; destruct s; simpl in H0; discriminate.
      + simpl in H; injection H; intros; subst.
        simpl in *; repeat find_if_inside; try discriminate.
        destruct (index 0 "." s) eqn: ?;
          destruct (index 0 "." t) eqn : ?; try discriminate.
        apply IHs in H2; eauto.
        intuition.
        congruence.
  Qed.

  Lemma index_app :
    forall s s' t,
      index 0 (String t EmptyString) s = None
      -> index 0 (String t EmptyString) s' = None
      -> index 0 (String t EmptyString) (s ++ s')%string = None.
  Proof.
    induction s; simpl; eauto; intros.
    destruct (ascii_dec t a); subst.
    destruct s; simpl in H; try discriminate.
    destruct (index 0 (String t ""%string) s) eqn: ?; try discriminate.
    rewrite IHs; eauto.
  Qed.

  Lemma ValidDomainName_app'
    : forall label subdomain (subdomainOK : subdomain <> EmptyString),
      ValidLabel label
      -> lt (String.length label) 64
      -> ValidDomainName subdomain
      -> ValidDomainName (label ++ (String "." subdomain)).
  Proof.
    unfold ValidDomainName; intros.
    split; [ intros ? ? ? label_eq [? ?] | ].
    - assert ((exists pre', pre' ++ label0 ++ post = subdomain) \/
              exists post', label = (pre ++ label0 ++ post'))%string.
      { destruct (index 0 "." pre) eqn:pre_eq.
        - apply index_correct' in pre_eq;
            destruct pre_eq as [s [s' [ [pre_eq s_len] s_OK ] ] ];
            subst.
          rewrite <- append_assoc in label_eq.
          simpl in label_eq.
          destruct H; eapply split_char_inj in label_eq; intuition.
          subst; eauto.
        - destruct (index 0 "." post) eqn:post_eq.
          apply index_correct' in post_eq;
            destruct post_eq as [t [t' [ [post_eq t_len] t_OK ] ] ];
            subst.
          rewrite append_assoc in label_eq.
          rewrite append_assoc in label_eq.
          destruct H; eapply split_char_inj in label_eq; intuition;
            subst.
          rewrite <- !append_assoc; eauto.
          eauto using index_app.
          assert (index 0 "." (label ++ String "." subdomain)%string = None)
            by (rewrite label_eq; eauto using index_app).
          eapply index_correct3 with (m := String.length label) in H4;
            try omega; try congruence.
          destruct label.
          elimtype False; destruct H; simpl in H5; omega.
          elimtype False; apply H4; clear.
          induction label; simpl.
          + destruct subdomain; simpl; reflexivity.
          + apply IHlabel.
      }
      destruct H4 as [ [pre' subdomain_eq] | [post' label_eq'] ].
      subst; eapply H1; unfold ValidLabel; eauto.
      subst.
      rewrite !length_append in H0; omega.
    - intros.
      assert ((label = pre) \/
              exists mid, pre = label ++ String "." mid)%string.
      { destruct (index 0 "." pre) eqn:pre_eq.
        - apply index_correct' in pre_eq;
            destruct pre_eq as [s [s' [ [pre_eq s_len] s_OK ] ] ];
            subst.
          rewrite <- append_assoc in H2.
          simpl in H2.
          destruct H; eapply split_char_inj in H2; intuition.
          subst; simpl; eauto.
        - destruct (index 0 "." post) eqn:post_eq.
          apply index_correct' in post_eq;
            destruct post_eq as [t [t' [ [post_eq t_len] t_OK ] ] ];
            subst.
          destruct H; eapply split_char_inj in H2; intuition;
            subst.
          destruct H.
          simpl in H2; eapply split_char_inj in H2; intuition eauto.
      }
      destruct H3; subst.
      + apply ValidLabel_OK_split in H2; subst; repeat split; auto.
        * destruct pre; try congruence.
          destruct H; simpl in *; omega.
        * intro; destruct H2; subst.
          destruct (proj2 H1 EmptyString x eq_refl);
            intuition.
        * intros [s' pre_eq]; subst.
          unfold ValidLabel in H; intuition.
          apply (index_correct3 _ (String.length s')) in H1.
          apply H1; simpl.
          clear; induction s'; simpl; eauto.
          congruence.
          omega.
      + destruct H3; subst.
        rewrite <- append_assoc in H2; simpl in H2.
        eapply (ValidLabel_OK_split label _ (x ++ String "." post)) in H2.
        pose proof (proj2 H1 _ _ H2); subst; eauto; repeat split;
          try solve [intuition].
        * destruct label; simpl; congruence.
        * intros [s' s'_eq].
          apply (proj2 (proj2 (proj2 H3))).
          generalize (proj1 (proj2 H3)).
          generalize s' x s'_eq; clear.
          induction label; simpl.
          induction s'; simpl; intros.
          destruct x; eauto; congruence.
          injection s'_eq; intros; eauto.
          destruct s'; simpl; intros.
          destruct label; discriminate.
          injection s'_eq; intro; eauto.
  Qed.

  Lemma ValidDomainName_Empty
    : ValidDomainName "".
  Proof.
    unfold ValidDomainName; split; intros.
    - destruct pre; try discriminate.
      destruct label; try discriminate.
      simpl; omega.
    - destruct pre; try discriminate.
  Qed.

  Lemma chomp_label_length
    : forall n label subdomain,
      (String.length (label ++ (String "." subdomain)) <= S n)%nat
      -> ValidLabel label
      -> (String.length subdomain <= n)%nat.
  Proof.
    destruct label.
    - unfold ValidLabel; simpl; intros; omega.
    - intro subdomain; rewrite length_append; simpl.
      omega.
  Qed.

  Definition decode_DomainName (b : B) (env : CacheDecode):
    option (DomainName * B * CacheDecode).
    refine (Fix well_founded_lt_b
           (fun _ => CacheDecode -> option (DomainName * B * CacheDecode))
      (fun b rec cd =>
         `(labelheader, b1, env') <- Decode_w_Measure_le (decode_word (sz := 8)) b cd _;
           match (wlt_dec (natToWord 8 191) labelheader) with (* It's a pointer! *)
           | left l  => (`(ps, b2, env') <- Decode_w_Measure_le (decode_word (sz := 8)) (proj1_sig b1) env' decode_word_le;
               match getD cd (exist _ _ l, ps) with
                 | Some EmptyString => None (* bogus *)
                 | Some domain => Some (domain, proj1_sig b2, env')
                 | None => None (* bogus *)
                 end)
           | right r => (If (wlt_dec labelheader (natToWord 8 64)) Then (* It's a length octet *)
         (match (weq labelheader (wzero 8)) with (* It's the terminal character. *)
              | left _ => Some (EmptyString, proj1_sig b1, env')
              | right n =>
             (`(label, b3, env') <- Decode_w_Measure_lt (decode_string (wordToNat labelheader))
               (proj1_sig b1) env' (decode_string_lt _ (n_eq_0_lt _ n));
              Ifopt (index 0 "." label) as _ Then None
              Else (`(domain, b4, e3) <- rec (proj1_sig b3) (lt_B_trans _ _ _) env';
              If (string_dec domain "") Then
                 Some (label, b4,
                       Ifopt (peekD cd) as curPtr Then addD_G e3 (label, curPtr)
                                                  Else e3)
                 Else Some (label ++ (String "." domain), b4,
                            Ifopt (peekD cd) as curPtr Then
                            addD_G e3 (label ++ (String "." domain), curPtr)
                            Else e3)
             )) end)
         Else None) end)%string b env);
    try exact decode_word_le;
      try exact decode_word_lt.
  Defined.

  Lemma decode_body_monotone
    : forall (x : B)
     (f g : forall y : B, lt_B y x -> CacheDecode -> option (DomainName * B * CacheDecode)),
   (forall (y : B) (p : lt_B y x), f y p = g y p) ->
   (fun cd : CacheDecode =>
    `(labelheader, b1, env') <- Decode_w_Measure_le decode_word x cd decode_word_le;
    match wlt_dec WO~1~0~1~1~1~1~1~1 labelheader with
    | left l => `(ps, b2, env'0) <- Decode_w_Measure_le decode_word (` b1) env' decode_word_le;
         match getD cd (exist _ labelheader l, ps) with
         | Some ""%string => None
         | Some (String _ _ as domain) => Some (domain, ` b2, env'0)
         | None => None
         end
    | right r => (If wlt_dec labelheader WO~0~1~0~0~0~0~0~0
          Then match weq labelheader (wzero 8) with
               | in_left => Some (""%string, ` b1, env')
               | right n =>
                   `(label, b3, env'0) <- Decode_w_Measure_lt
                                            (decode_string (wordToNat labelheader))
                                            (` b1) env'
                                            (decode_string_lt
                                               (wordToNat labelheader)
                                               (n_eq_0_lt labelheader n));
                    Ifopt (index 0 "." label) as _ Then None
                    Else (
                   `(domain, b4, e3) <- f (` b3) (lt_B_trans x b1 b3) env'0;
                   If (string_dec domain "") Then
                      Some (label, b4,
                            Ifopt (peekD cd) as curPtr Then addD_G e3 (label, curPtr)
                                                       Else e3)
                   Else Some (label ++ (String "." domain), b4,
                              Ifopt (peekD cd) as curPtr Then addD_G e3
                                                         (label ++ (String "." domain), curPtr)
                                                         Else e3))%string
               end Else None) end) =
   (fun cd : CacheDecode =>
      `(labelheader, b1, env') <- Decode_w_Measure_le decode_word x cd decode_word_le;
        match wlt_dec WO~1~0~1~1~1~1~1~1 labelheader with
        | left l => `(ps, b2, env'0) <- Decode_w_Measure_le decode_word (` b1) env' decode_word_le;
         match getD cd (exist _ _ l, ps) with
         | Some ""%string => None
         | Some (String _ _ as domain) => Some (domain, ` b2, env'0)
         | None => None
         end
        | right _ => (If wlt_dec labelheader WO~0~1~0~0~0~0~0~0
          Then match weq labelheader (wzero 8) with
               | in_left => Some (""%string, ` b1, env')
               | right n =>
                   `(label, b3, env'0) <- Decode_w_Measure_lt
                                            (decode_string (wordToNat labelheader))
                                            (` b1) env'
                                            (decode_string_lt
                                               (wordToNat labelheader)
                                               (n_eq_0_lt labelheader n));
                     Ifopt (index 0 "." label) as _ Then None
                     Else (
                     `(domain, b4, e3) <- g (` b3) (lt_B_trans x b1 b3) env'0;
                       If (string_dec domain "") Then
                          Some (label, b4, Ifopt (peekD cd) as curPtr Then addD_G e3 (label, curPtr)
                                                                                 Else e3)
                       Else Some (label ++ (String "." domain), b4,
                                  Ifopt (peekD cd) as curPtr Then addD_G e3
                                                             (label ++ (String "." domain), curPtr)
                                                             Else e3))%string
               end Else None) end).
  Proof.
    intros; apply functional_extensionality; intros.
    repeat (f_equal; apply functional_extensionality; intros).
    destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x1); simpl.
    repeat (f_equal; apply functional_extensionality; intros).
    destruct (wlt_dec x1 WO~0~1~0~0~0~0~0~0); simpl.
    destruct (weq x1 (wzero 8)).
    reflexivity.
    repeat (f_equal; apply functional_extensionality; intros).
    destruct (index 0 "." x4); simpl; eauto.
    rewrite H; reflexivity.
    reflexivity.
  Qed.

  Lemma encode_body_monotone
    : forall rec rec' : funType [DomainName; CacheEncode] (B * CacheEncode),
 refineFun rec rec' ->
 refineFun (fDom := [DomainName; CacheEncode])
   (fun (domain : DomainName) (env0 : CacheEncode) =>
    If string_dec domain "" Then encode_ascii_Spec terminal_char env0
    Else (
      position <- { position | forall p, position = Some p -> In p (getE env0 domain)};
        Ifopt position as position
          Then `(ptr1b, env') <- encode_word_Spec (proj1_sig (fst position)) env0;
                    `(ptr2b, env'0) <- encode_word_Spec (snd position) env';
                    ret (transform ptr1b ptr2b, env'0)
               Else (`(label, domain') <- {labeldomain' :
                                          string * string |
                                          (domain =
                                           (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                           labeldomain' = (domain, ""%string)) /\
                                          ValidLabel (fst labeldomain') /\
                                          (forall label' post' : string,
                                           domain = (label' ++ post')%string ->
                                           ValidLabel label' ->
                                           (String.length label' <=
                                            String.length (fst labeldomain'))%nat)};
                     `(lenb, env') <- encode_nat_Spec 8 (String.length label) env0;
                     `(labelb, env'0) <- encode_string_Spec label env';
                     `(domainb, env'1) <- rec domain' env'0;
                     ret
                       (transform (transform lenb labelb) domainb,
                        Ifopt peekE env0 as curPtr Then addE_G env'1 (domain, curPtr)
                                      Else env'1))))
   (fun (domain : DomainName) (env0 : CacheEncode) =>
    If string_dec domain "" Then encode_ascii_Spec terminal_char env0
    Else (
      position <- { position | forall p, position = Some p -> In p (getE env0 domain)};
        Ifopt position as position
               Then `(ptr1b, env') <- encode_word_Spec (proj1_sig (fst position)) env0;
                    `(ptr2b, env'0) <- encode_word_Spec (snd position) env';
                    ret (transform ptr1b ptr2b, env'0)
               Else (`(label, domain') <- {labeldomain' :
                                          string * string |
                                           (domain =
                                           (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                           labeldomain' = (domain, ""%string)) /\
                                          ValidLabel (fst labeldomain') /\
                                          (forall label' post' : string,
                                           domain = (label' ++ post')%string ->
                                           ValidLabel label' ->
                                           (String.length label' <=
                                            String.length (fst labeldomain'))%nat)};
                     `(lenb, env') <- encode_nat_Spec 8 (String.length label) env0;
                     `(labelb, env'0) <- encode_string_Spec label env';
                     `(domainb, env'1) <- rec' domain' env'0;
                     ret
                       (transform (transform lenb labelb) domainb,
                        Ifopt peekE env0 as curPtr Then addE_G env'1 (domain, curPtr)
                                      Else env'1)))).
  Proof.
    simpl; intros; unfold Bind2.
    apply General.refine_if; intros; rewrite H0; simpl.
    reflexivity.
    apply SetoidMorphisms.refine_bind.
    reflexivity.
    intro.
    apply SetoidMorphisms.refine_If_Opt_Then_Else_Proper.
    * intro; f_equiv; intro.
    * f_equiv; intro.
      unfold Bind2; f_equiv; intro.
      setoid_rewrite H; reflexivity.
  Qed.

  Lemma Decode_w_Measure_le_eq'
    : forall (A B : Type) (cache : Cache) (transformer : Transformer B)
             (A_decode : B -> CacheDecode -> option (A * B * CacheDecode))
             (b : B) (cd : CacheDecode)
             (A_decode_le : forall (b0 : B) (cd0 : CacheDecode) (a : A) (b' : B) (cd' : CacheDecode),
                 A_decode b0 cd0 = Some (a, b', cd') -> le_B b' b0)
             (a' : A) (b' : B) (cd' : CacheDecode)
             pf,
      Decode_w_Measure_le A_decode b cd A_decode_le = Some (a', pf, cd')
      -> A_decode b cd = Some (a', `pf , cd').
  Proof.
    unfold Decode_w_Measure_le; intros.
    revert pf H.
    generalize (A_decode_le b cd).
    destruct (A_decode b cd) as [ [ [? ?] ?] | ]; simpl; intros;
      try discriminate.
    injections; reflexivity.
  Qed.

  Lemma Decode_w_Measure_lt_eq'
    : forall (A B : Type) (cache : Cache) (transformer : Transformer B)
             (A_decode : B -> CacheDecode -> option (A * B * CacheDecode))
             (b : B) (cd : CacheDecode)
             (A_decode_lt : forall (b0 : B) (cd0 : CacheDecode) (a : A) (b' : B) (cd' : CacheDecode),
                 A_decode b0 cd0 = Some (a, b', cd') -> lt_B b' b0)
             (a' : A) (b' : B) (cd' : CacheDecode)
             pf,
      Decode_w_Measure_lt A_decode b cd A_decode_lt = Some (a', pf, cd')
      -> A_decode b cd = Some (a', `pf , cd').
  Proof.
    unfold Decode_w_Measure_lt; intros.
    revert pf H.
    generalize (A_decode_lt b cd).
    destruct (A_decode b cd) as [ [ [? ?] ?] | ]; simpl; intros;
      try discriminate.
    injections; reflexivity.
  Qed.

  Lemma append_EmptyString_r :
    forall l, l = ("" ++ l ++ "")%string.
  Proof.
    simpl.
    induction l; simpl; eauto.
    f_equal; eauto.
  Qed.

  Lemma NonEmpty_String_wordToNat
    : forall n s w,
      String.length s = wordToNat w
      -> w <> wzero n
      -> s <> ""%string.
  Proof.
    unfold not; intros; apply H0; subst.
    generalize (f_equal (natToWord n) H);
      rewrite natToWord_wordToNat; simpl; eauto.
  Qed.

  Lemma ValidLabel_split_char :
    forall s label subdomain subdomain',
      (s ++ String "." subdomain)%string = (label ++ subdomain')%string
      -> ValidLabel label
      -> le (String.length label) (String.length s).
  Proof.
    intros.
    destruct (index 0 "." s) eqn:pre_eq.
    apply index_correct' in pre_eq;
      destruct pre_eq as [s' [s'' [ [s_eq s'_len]  s'_OK] ] ];
      subst.
    destruct (index 0 "." subdomain') eqn:subdomain_eq.
    apply index_correct' in subdomain_eq;
      destruct subdomain_eq as [t' [t'' [ [t_eq t'_len]  t'_OK] ] ];
      subst.
    assert (label ++ t' = s')%string.
    rewrite <- !append_assoc in H; simpl in H.
    pose proof (split_char_inj s' (s'' ++ String "." subdomain) (label ++ t') t'').
    rewrite <- !append_assoc in H1; simpl in H1.
    destruct H0.
    apply H1 in H; eauto using index_app.
    destruct H; subst; eauto.
    apply (f_equal String.length) in H1;
      rewrite !length_append in *|-*; simpl in *.
    omega.
    assert (index 0 "." ((s' ++ "." ++ s'') ++ String "." subdomain)%string = None) by (rewrite H; destruct H0; apply index_app; eauto).
    destruct s'. simpl in H1.
    destruct s''; try solve [simpl in H1; discriminate].
    eapply index_correct3 with (m := S (String.length s')) in H1;
      try omega; try congruence.
    elimtype False; apply H1; clear.
    induction s'; simpl.
    destruct s''; simpl; reflexivity.
    assumption.
    destruct (index 0 "." subdomain') eqn:subdomain_eq.
    apply index_correct' in subdomain_eq;
      destruct subdomain_eq as [t' [t'' [ [t_eq t'_len]  t'_OK] ] ];
      subst.
    assert (label ++ t' = s)%string.
    simpl in H.
    pose proof (split_char_inj s subdomain (label ++ t') t'').
    rewrite <- !append_assoc in H1; simpl in H1.
    destruct H0.
    apply H1 in H; eauto using index_app.
    destruct H; subst; eauto.
    apply (f_equal String.length) in H1;
      rewrite !length_append in *|-*; simpl in *.
    omega.
    assert (index 0 "." (s ++ String "." subdomain)%string = None)
      by (rewrite H; destruct H0; apply index_app; eauto).
    destruct s. simpl in H1.
    destruct subdomain; try solve [simpl in H1; discriminate].
    eapply index_correct3 with (m := S (String.length s)) in H1;
      try omega; try congruence.
    elimtype False; apply H1; clear.
    induction s; simpl.
    destruct subdomain; simpl; reflexivity.
    assumption.
  Qed.

  Lemma ptr_eq : forall (p p' : {w : word 8 | wlt (natToWord 8 191) w}),
      proj1_sig p = proj1_sig p' -> p = p'.
  Proof.
    intros [p p_pf] [p' p'_pf]; simpl; intros; subst.
    f_equal.
    unfold wlt, BinNat.N.lt in *.
    apply UIP_dec.
    decide equality.
  Qed.

  Variable IndependentCaches :
    forall env p (b : nat),
      getD (addD env b) p = getD env p.
  Variable IndependentCaches' :
    forall env p (b : nat),
      getE (addE env b) p = getE env p.
  Variable IndependentCaches''' :
    forall env b,
      peekE (addE_G env b) = peekE env.

  Variable getDistinct :
    forall env l p p',
      p <> p'
      -> getD (addD_G env (l, p)) p' = getD env p'.
  Variable getDistinct' :
    forall env l p p' l',
      In p (getE (addE_G env (l', p')) l)
      -> p = p' \/ In p (getE env l).

  Variable addPeekSome :
    forall env n m,
      peekD env = Some m
      -> (n + (pointerT2Nat m) < pow2 14)%nat
      -> exists p',
          peekD (addD env (n * 8)) = Some p'
          /\ pointerT2Nat p' = n + (pointerT2Nat m).
  Variable boundPeekSome :
    forall env n m m',
      peekD env = Some m
      -> peekD (addD env (n * 8)) = Some m'
      -> (n + (pointerT2Nat m) < pow2 14)%nat.
  Variable addPeekNone :
    forall env n,
      peekD env = None
      -> peekD (addD env n) = None.
  Variable addPeekNone' :
    forall env n m,
      peekD env = Some m
      -> ~ (n + (pointerT2Nat m) < pow2 14)%nat
      -> peekD (addD env (n * 8)) = None.
  Variable addZeroPeek :
    forall xenv,
      peekD xenv = peekD (addD xenv 0).

    Variable addPeekESome :
    forall env n m,
      peekE env = Some m
      -> (n + (pointerT2Nat m) < pow2 14)%nat
      -> exists p',
          peekE (addE env (n * 8)) = Some p'
          /\ pointerT2Nat p' = n + (pointerT2Nat m).
    Variable boundPeekESome :
    forall env n m m',
      peekE env = Some m
      -> peekE (addE env (n * 8)) = Some m'
      -> (n + (pointerT2Nat m) < pow2 14)%nat.
    Variable addPeekENone :
      forall env n,
        peekE env = None
        -> peekE (addE env n) = None.
    Variable addPeekENone' :
      forall env n m,
        peekE env = Some m
        -> ~ (n + (pointerT2Nat m) < pow2 14)%nat
        -> peekE (addE env (n * 8)) = None.
  Variable addZeroPeekE :
    forall xenv,
      peekE xenv = peekE (addE xenv 0).

  Arguments pow2 : simpl never.

  Lemma decode_word_add_ptr_OK
    : forall sz env xenv n env' b b' x x1 l,
      add_ptr_OK (l, n) env xenv
      -> decode_word (sz := sz) b xenv = Some (x, b', x1)
      -> add_ptr_OK (l, n) env' x1.
  Proof.
    intros.
    unfold decode_word in H0.
    destruct (decode_word' sz b); simpl in *; try discriminate.
    injections.
    unfold add_ptr_OK.
    rewrite IndependentCaches; eauto.
  Qed.

  Lemma decode_string_add_ptr_OK
    : forall n env xenv n' xenv'' b b' l l',
      add_ptr_OK (l', n') env xenv
      -> decode_string n b xenv = Some (l, b', xenv'')
      -> add_ptr_OK (l', n') env xenv''.
  Proof.
    unfold add_ptr_OK in *; induction n; simpl; intros.
    - injections; eauto.
      rewrite IndependentCaches; eauto.
    - apply DecodeBindOpt2_inv in H0;
        destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
      destruct (decode_string n x0 x1) eqn: ?; simpl in *; try discriminate.
      destruct p; destruct p; injections.
      eapply IHn in Heqo; eauto.
      unfold decode_ascii in H0.
      apply DecodeBindOpt2_inv in H0;
        destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
      unfold decode_word in H0.
      destruct (decode_word' 8 b); simpl in *; try discriminate; injections.
      rewrite IndependentCaches; eauto.
  Qed.

  Lemma encode_nat_add_ptr_OK
    : forall n env b b' env' p z,
      ~ In p (getE env z)
      -> computes_to (encode_nat_Spec n b env) (b', env')
      -> ~ In p (getE env' z).
  Proof.
    unfold encode_nat_Spec, encode_word_Spec; intros; computes_to_inv;
      injections; intro.
    rewrite IndependentCaches' in H0; eauto.
  Qed.

  Lemma encode_string_add_ptr_OK
    : forall s env b' env' p z,
      ~ In p (getE env z)
      -> computes_to (encode_string_Spec s env) (b', env')
      -> ~ In p (getE env' z).
  Proof.
    induction s; simpl; unfold encode_ascii_Spec, encode_word_Spec;
      intros; computes_to_inv; injections; try rewrite IndependentCaches'; eauto.
    unfold Bind2 in *; computes_to_inv; injections; simpl in *; eauto.
    destruct v0; simpl in *; eauto.
    eapply IHs in H0'.
    eassumption.
    unfold not; rewrite IndependentCaches'; eauto.
  Qed.

  Lemma addPeek :
    forall env n m,
      peekD env = Some m
      -> (peekD (addD env (n * 8)) = Some (Nat2pointerT (n + (pointerT2Nat m)))
          /\ n + (pointerT2Nat m) < pow2 14)%nat
         \/ peekD (addD env (n * 8)) = None.
  Proof.
    intros;
      destruct (Compare_dec.lt_dec (n + pointerT2Nat m) (pow2 14)).
    - left; pose proof (addPeekSome _ n _ H) as H'; eauto.
      destruct H' as [p' [H' H''] ]; eauto.
      split.
      * rewrite H', <- H''.
        f_equal.
        rewrite Nat2pointerT_pointerT2Nat; reflexivity.
      * eapply boundPeekSome; eauto.
    - right; eapply addPeekNone' in H; eauto.
  Qed.

  Lemma addPeekE :
    forall env n m,
      peekE env = Some m
      -> (peekE (addE env (n * 8)) = Some (Nat2pointerT (n + (pointerT2Nat m)))
          /\ n + (pointerT2Nat m) < pow2 14)%nat
         \/ peekE (addE env (n * 8)) = None.
  Proof.
    intros;
      destruct (Compare_dec.lt_dec (n + pointerT2Nat m) (pow2 14)).
    - left; pose proof (addPeekESome _ n _ H) as H'; eauto.
      destruct H' as [p' [H' H''] ]; eauto.
      split.
      * rewrite H', <- H''.
        f_equal.
        rewrite Nat2pointerT_pointerT2Nat; reflexivity.
      * eapply boundPeekESome; eauto.
    - right; eapply addPeekENone' in H; eauto.
  Qed.

  Lemma encode_nat_peekE
    : forall n env b b' env',
      computes_to (encode_nat_Spec n b env) (b', env')
      -> peekE env' = peekE (addE env n).
  Proof.
    unfold encode_nat_Spec, encode_word_Spec; intros; computes_to_inv;
    injections; reflexivity.
  Qed.

  Lemma encode_string_peekE
    : forall l env b' env',
      computes_to (encode_string_Spec l env) (b', env')
      -> peekE env' = peekE (addE env (String.length l * 8)).
  Proof.
    induction l; simpl; unfold encode_ascii_Spec, encode_word_Spec;
      intros; computes_to_inv; injections; eauto.
    unfold Bind2 in *; computes_to_inv; injections; simpl in *; eauto.
    destruct v0; simpl in *; eauto.
    eapply IHl in H'.
    rewrite H'.
    destruct (peekE env) eqn: ?.
    - destruct (addPeekE _ (1 + (String.length l)) _ Heqy) as [ [? ?] | ?].
      destruct (addPeekESome _ 1 _ Heqy) as [? [? ?] ] ; try omega.
      destruct (addPeekESome _ (String.length l) _ H1) as [? [? ?] ] ; try omega.
      + simpl in *; rewrite H, H3.
        f_equal.
        apply (f_equal Nat2pointerT) in H4.
        rewrite Nat2pointerT_pointerT2Nat in H4.
        apply (f_equal Nat2pointerT) in H2.
        rewrite Nat2pointerT_pointerT2Nat in H2.
        subst.
        rewrite pointerT2Nat_Nat2pointerT; auto.
        omega.
      + destruct (addPeekE _ 1 _ Heqy) as [ [? ?] | ?].
        * destruct (addPeekE _ (String.length l) _ H0) as [ [? ?] | ?].
          destruct (addPeekESome _ (S (String.length l)) _ Heqy) as [? [? ?] ].
          rewrite pointerT2Nat_Nat2pointerT in H2, H3; try omega.
          simpl in *; congruence.
          simpl in *; congruence.
        * eapply addPeekENone in H0; simpl in *; rewrite H, H0; auto.
    - rewrite !addPeekENone; auto.
  Qed.

  Lemma decode_word_peek_distinct
    : forall sz xenv xenv' b b' x,
      decode_word (sz := sz) b xenv = Some (x, b', xenv')
      -> peekD xenv' = peekD (addD xenv sz).
  Proof.
    intros.
    unfold decode_word in H.
    destruct (decode_word' sz b); simpl in *; try discriminate.
    injections.
    reflexivity.
  Qed.

  Lemma PeekCacheFixpoint_Overflow
    : forall
      (n : nat)
      (x6 : DomainName)
      (xenv'' : CacheEncode)
      (bin' : B)
      (xenv0 : CacheEncode)
      (x9 : string)
      (p0 : pointerT),
      (forall (env : CacheEncode) (p : string) (b : nat), getE (addE env b) p = getE env p) ->
      (forall (env : CacheEncode) (l : string) (p p' : pointerT) (l' : string),
          In p (getE (addE_G env (l', p')) l) -> p = p' \/ In p (getE env l)) ->
      (String.length x6 <= n)%nat ->
      LeastFixedPoint
        (fun (encode_DomainName_Spec : funType [DomainName; CacheEncode] (B * CacheEncode))
             (domain : DomainName) (env : CacheEncode) =>
           If string_dec domain "" Then encode_ascii_Spec terminal_char env
              Else (position <- {position : option ({x | WO~1~0~1~1~1~1~1~1 < x} * word 8) |
                        forall p : {x | WO~1~0~1~1~1~1~1~1 < x} * word 8,
                          position = Some p -> In p (getE env domain)};
            Ifopt position as position0
                                Then `(ptr1b, env') <- encode_word_Spec (` (fst position0)) env;
            `(ptr2b, env'0) <- encode_word_Spec (snd position0) env';
            ret (transform ptr1b ptr2b, env'0)
                Else (`(label, domain') <- {labeldomain' :
                                              string * string |
                                            (domain = (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                             labeldomain' = (domain, ""%string)) /\
                                            ValidLabel (fst labeldomain') /\
                                            (forall label' post' : string,
                                                domain = (label' ++ post')%string ->
                                                ValidLabel label' ->
                                                (String.length label' <= String.length (fst labeldomain'))%nat)};
                        `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
                        `(labelb, env'0) <- encode_string_Spec label env';
                        `(domainb, env'1) <- encode_DomainName_Spec domain' env'0;
                        ret
                          (transform (transform lenb labelb) domainb,
                           Ifopt peekE env as curPtr Then addE_G env'1 (domain, curPtr) Else env'1)))) x6 xenv''
        ↝ (bin', xenv0) ->
      peekE xenv'' = None
      -> peekE xenv0 = None.
  Proof.
    induction n; intros;
      apply (@unroll_LeastFixedPoint [DomainName; CacheEncode]
                                     (B * CacheEncode)%type _ encode_body_monotone) in H2;
      simpl in H2.
    - destruct x6; simpl in *.
      simpl in H2; computes_to_inv.
      unfold encode_ascii_Spec, encode_word_Spec in H2;
        computes_to_inv; subst; simpl in *; injections.
      eapply addPeekENone; eauto.
      elimtype False; omega.
    - destruct x6; simpl in *.
      + simpl in H2; computes_to_inv.
        unfold encode_ascii_Spec, encode_word_Spec in H2;
          computes_to_inv; subst; simpl in *; injections.
        eapply addPeekENone; eauto.
      + simpl in H2; computes_to_inv.
        destruct v; simpl in H2'; unfold Bind2 in *; computes_to_inv.
        * unfold encode_word_Spec in *;
            computes_to_inv; subst; simpl in *; injections.
          eapply addPeekENone; eauto.
        * destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
            destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
              simpl in *; injections.
          generalize H2'' H2'''.
          apply encode_nat_peekE in H2'';
            subst.
          apply encode_string_peekE in H2'''; subst; intros.
          rewrite H3; simpl.
          eapply addPeekENone in H3; rewrite H3 in H2''.
          eapply addPeekENone in H2''; rewrite H2'' in H2'''.
          eapply IHn in H2''''; eauto.
          destruct H2' as [ [? | ?] [? ?] ].
          generalize (f_equal String.length H4); simpl;
            rewrite !length_append; simpl; omega.
          injection H4; intros; subst.
          simpl; omega.
  Qed.

  Lemma InCacheFixpoint_Overflow
    : forall
      (n : nat)
      (x6 : DomainName)
      (xenv'' : CacheEncode)
      (bin' : B)
      (xenv0 : CacheEncode)
      (x9 : string)
      (p0 : pointerT),
      (forall (env : CacheEncode) (p : string) (b : nat), getE (addE env b) p = getE env p) ->
      (forall (env : CacheEncode) (l : string) (p p' : pointerT) (l' : string),
          In p (getE (addE_G env (l', p')) l) -> p = p' \/ In p (getE env l)) ->
      (String.length x6 <= n)%nat ->
      LeastFixedPoint
        (fun (encode_DomainName_Spec : funType [DomainName; CacheEncode] (B * CacheEncode))
             (domain : DomainName) (env : CacheEncode) =>
           If string_dec domain "" Then encode_ascii_Spec terminal_char env
              Else (position <- {position : option ({x | WO~1~0~1~1~1~1~1~1 < x} * word 8) |
                        forall p : {x | WO~1~0~1~1~1~1~1~1 < x} * word 8,
                          position = Some p -> In p (getE env domain)};
            Ifopt position as position0
                                Then `(ptr1b, env') <- encode_word_Spec (` (fst position0)) env;
            `(ptr2b, env'0) <- encode_word_Spec (snd position0) env';
            ret (transform ptr1b ptr2b, env'0)
                Else (`(label, domain') <- {labeldomain' :
                                              string * string |
                                            (domain = (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                             labeldomain' = (domain, ""%string)) /\
                                            ValidLabel (fst labeldomain') /\
                                            (forall label' post' : string,
                                                domain = (label' ++ post')%string ->
                                                ValidLabel label' ->
                                                (String.length label' <= String.length (fst labeldomain'))%nat)};
                        `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
                        `(labelb, env'0) <- encode_string_Spec label env';
                        `(domainb, env'1) <- encode_DomainName_Spec domain' env'0;
                        ret
                          (transform (transform lenb labelb) domainb,
                           Ifopt peekE env as curPtr Then addE_G env'1 (domain, curPtr) Else env'1)))) x6 xenv''
        ↝ (bin', xenv0) ->
      peekE xenv'' = None
      -> In p0 (getE xenv0 x9)
      -> In p0 (getE xenv'' x9).
  Proof.
    induction n; intros;
      apply (@unroll_LeastFixedPoint [DomainName; CacheEncode]
                                     (B * CacheEncode)%type _ encode_body_monotone) in H2;
      simpl in H2.
    - destruct x6; simpl in *.
      simpl in H2; computes_to_inv.
      unfold encode_ascii_Spec, encode_word_Spec in H2;
        computes_to_inv; subst; simpl in *; injections.
      rewrite H in H4; intuition.
      elimtype False; omega.
    - destruct x6; simpl in *.
      + simpl in H2; computes_to_inv.
        unfold encode_ascii_Spec, encode_word_Spec in H2;
          computes_to_inv; subst; simpl in *; injections.
        rewrite H in H4; intuition.
      + simpl in H2; computes_to_inv.
        destruct v; simpl in H2'; unfold Bind2 in *; computes_to_inv.
        * unfold encode_word_Spec in *;
            computes_to_inv; subst; simpl in *; injections.
          rewrite !H in H4; eauto.
        * destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
            destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
              simpl in *; injections.
          rewrite H3 in H4; simpl in H4.
          generalize H2'' H2'''.
          apply encode_nat_peekE in H2'';
            subst.
          apply encode_string_peekE in H2'''; subst; intros.
          eapply addPeekENone in H3; rewrite H3 in H2''.
          eapply addPeekENone in H2''; rewrite H2'' in H2'''.
          eapply IHn in H2''''; eauto.
          destruct (fun H => in_dec H p0 (getE xenv'' x9)); eauto.
          apply pointerT_eq_dec.
          eapply encode_nat_add_ptr_OK in n0; eauto.
          eapply encode_string_add_ptr_OK in n0; eauto; intuition.
          destruct H2' as [ [? | ?] [? ?] ].
          generalize (f_equal String.length H5); simpl;
            rewrite !length_append; simpl; omega.
          injection H5; intros; subst.
          simpl; omega.
  Qed.



  Lemma PeekCacheFixpoint
    : forall
      (n : nat)
      (x6 : DomainName)
      (xenv'' : CacheEncode)
      (bin' : B)
      (xenv0 : CacheEncode)
      (x9 : string)
      (p' p : pointerT),
      (forall (env : CacheEncode) (p : string) (b : nat), getE (addE env b) p = getE env p) ->
      (forall (env : CacheEncode) (l : string) (p p' : pointerT) (l' : string),
          In p (getE (addE_G env (l', p')) l) -> p = p' \/ In p (getE env l)) ->
      (String.length x6 <= n)%nat ->
      LeastFixedPoint
        (fun (encode_DomainName_Spec : funType [DomainName; CacheEncode] (B * CacheEncode))
             (domain : DomainName) (env : CacheEncode) =>
           If string_dec domain "" Then encode_ascii_Spec terminal_char env
              Else (position <- {position : option ({x | WO~1~0~1~1~1~1~1~1 < x} * word 8) |
                        forall p : {x | WO~1~0~1~1~1~1~1~1 < x} * word 8,
                          position = Some p -> In p (getE env domain)};
            Ifopt position as position0
                                Then `(ptr1b, env') <- encode_word_Spec (` (fst position0)) env;
            `(ptr2b, env'0) <- encode_word_Spec (snd position0) env';
            ret (transform ptr1b ptr2b, env'0)
                Else (`(label, domain') <- {labeldomain' :
                                              string * string |
                                            (domain = (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                             labeldomain' = (domain, ""%string)) /\
                                            ValidLabel (fst labeldomain') /\
                                            (forall label' post' : string,
                                                domain = (label' ++ post')%string ->
                                                ValidLabel label' ->
                                                (String.length label' <= String.length (fst labeldomain'))%nat)};
                        `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
                        `(labelb, env'0) <- encode_string_Spec label env';
                        `(domainb, env'1) <- encode_DomainName_Spec domain' env'0;
                        ret
                          (transform (transform lenb labelb) domainb,
                           Ifopt peekE env as curPtr Then addE_G env'1 (domain, curPtr) Else env'1)))) x6 xenv''
        ↝ (bin', xenv0) ->
      peekE xenv'' = Some p ->
      peekE xenv0 = Some p' ->
      (pointerT2Nat p <= pointerT2Nat p')%nat.
  Proof.
    induction n; intros;
      apply (@unroll_LeastFixedPoint [DomainName; CacheEncode]
                                     (B * CacheEncode)%type _ encode_body_monotone) in H2;
      simpl in H2.
    - destruct x6; simpl in *.
      simpl in H2; computes_to_inv.
      unfold encode_ascii_Spec, encode_word_Spec in H2;
        computes_to_inv; subst; simpl in *; injections.
      apply (addPeekE _ 1) in H3; destruct H3 as [ [? ?] | ? ];
        simpl in *; rewrite H2 in H4; try discriminate.
      injections.
      rewrite pointerT2Nat_Nat2pointerT; eauto.
      elimtype False; omega.
    - destruct x6; simpl in *.
      + simpl in H2; computes_to_inv.
        unfold encode_ascii_Spec, encode_word_Spec in H2;
          computes_to_inv; subst; simpl in *; injections.
        apply (addPeekE _ 1) in H3; destruct H3 as [ [? ?] | ? ];
          simpl in *; rewrite H2 in H4; try discriminate.
        injections.
        rewrite pointerT2Nat_Nat2pointerT; eauto.
      + simpl in H2; computes_to_inv.
        destruct v; simpl in H2'; unfold Bind2 in *; computes_to_inv.
        * unfold encode_word_Spec in *;
            computes_to_inv; subst; simpl in *; injections.
          apply (addPeekE _ 1) in H3; destruct H3 as [ [? ?] | ? ];
            simpl in *.
          apply (addPeekE _ 1) in H3; destruct H3 as [ [? ?] | ? ];
            simpl in *; rewrite H3 in H4; try discriminate.
          injections.
          rewrite pointerT2Nat_Nat2pointerT; eauto.
          rewrite pointerT2Nat_Nat2pointerT; eauto.
          apply (addPeekENone _ 8) in H3; rewrite H3 in H4; discriminate.
        * destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
            destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
              simpl in *; injections.
          destruct H2' as [ ? [? ?] ].
          destruct (peekE xenv'') eqn: ?; simpl in *; eauto;
            try discriminate; injections.
          apply encode_nat_peekE in H2''.
          apply encode_string_peekE in H2'''.
          apply (addPeekE _ 1) in Heqy; destruct Heqy as [ [? ?] | ? ];
            simpl in H3; rewrite H3 in H2''; try discriminate; injections.
          eapply (addPeekE) in H2''; destruct H2'' as [ [? ?] | ? ];
            simpl in H9; rewrite H9 in H2'''; try discriminate; injections.
          etransitivity.
          2: eapply IHn in H2''''; eauto.
          rewrite pointerT2Nat_Nat2pointerT; eauto.
          rewrite pointerT2Nat_Nat2pointerT; eauto.
          omega.
          intuition.
          generalize (f_equal String.length H11); simpl;
            rewrite !length_append; simpl; omega.
          injections; simpl; omega.
          rewrite IndependentCaches''' in H4; auto.
          eapply PeekCacheFixpoint_Overflow in H2''''; eauto.
          rewrite IndependentCaches''', H2'''' in H4; discriminate.
          eapply addPeekENone in H2''; rewrite H2'' in H2'''.
          eapply PeekCacheFixpoint_Overflow in H2''''; eauto.
          rewrite IndependentCaches''', H2'''' in H4; discriminate.
  Qed.

  Lemma InCacheFixpoint
    : forall
      (n : nat)
      (x6 : DomainName)
      (xenv'' : CacheEncode)
      (bin' : B)
      (xenv0 : CacheEncode)
      (x9 : string)
      (p0 : pointerT),
      (forall (env : CacheEncode) (p : string) (b : nat), getE (addE env b) p = getE env p) ->
      (forall (env : CacheEncode) (l : string) (p p' : pointerT) (l' : string),
          In p (getE (addE_G env (l', p')) l) -> p = p' \/ In p (getE env l)) ->
      (String.length x6 <= n)%nat ->
      LeastFixedPoint
        (fun (encode_DomainName_Spec : funType [DomainName; CacheEncode] (B * CacheEncode))
             (domain : DomainName) (env : CacheEncode) =>
           If string_dec domain "" Then encode_ascii_Spec terminal_char env
              Else (position <- {position : option ({x | WO~1~0~1~1~1~1~1~1 < x} * word 8) |
                        forall p : {x | WO~1~0~1~1~1~1~1~1 < x} * word 8,
                          position = Some p -> In p (getE env domain)};
            Ifopt position as position0
                                Then `(ptr1b, env') <- encode_word_Spec (` (fst position0)) env;
            `(ptr2b, env'0) <- encode_word_Spec (snd position0) env';
            ret (transform ptr1b ptr2b, env'0)
                Else (`(label, domain') <- {labeldomain' :
                                              string * string |
                                            (domain = (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                             labeldomain' = (domain, ""%string)) /\
                                            ValidLabel (fst labeldomain') /\
                                            (forall label' post' : string,
                                                domain = (label' ++ post')%string ->
                                                ValidLabel label' ->
                                                (String.length label' <= String.length (fst labeldomain'))%nat)};
                        `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
                        `(labelb, env'0) <- encode_string_Spec label env';
                        `(domainb, env'1) <- encode_DomainName_Spec domain' env'0;
                        ret
                          (transform (transform lenb labelb) domainb,
                           Ifopt peekE env as curPtr Then addE_G env'1 (domain, curPtr) Else env'1)))) x6 xenv''
        ↝ (bin', xenv0) ->
      In p0 (getE xenv0 x9) ->
      (forall p',
          ~ In p0 (getE xenv'' x9) ->
          peekE xenv'' = Some p'
          -> (pointerT2Nat p' <= pointerT2Nat p0)%nat)
      /\ (peekE xenv'' = None -> In p0 (getE xenv'' x9)).
  Proof.
    induction n; intros;
      apply (@unroll_LeastFixedPoint [DomainName; CacheEncode]
                                     (B * CacheEncode)%type _ encode_body_monotone) in H2;
      simpl in H2.
    - destruct x6; simpl in *.
      simpl in H2; computes_to_inv.
      unfold encode_ascii_Spec, encode_word_Spec in H2;
        computes_to_inv; subst; simpl in *; injections.
      rewrite H in H3; intuition.
      elimtype False; omega.
    - destruct x6; simpl in *.
      + simpl in H2; computes_to_inv.
        unfold encode_ascii_Spec, encode_word_Spec in H2;
          computes_to_inv; subst; simpl in *; injections.
        rewrite H in H3; intuition.
      + simpl in H2; computes_to_inv.
        destruct v; simpl in H2'; unfold Bind2 in *; computes_to_inv.
        * unfold encode_word_Spec in *;
            computes_to_inv; subst; simpl in *; injections.
          rewrite !H in H3; eauto.
          intuition.
        * destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
            destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
              simpl in *; injections.
          destruct H2' as [ ? [? ?] ].
          destruct (peekE xenv'') eqn: ?; simpl in *; eauto.
          split; intros.
          apply H0 in H3; destruct H3.
          injections; intros; subst.
          auto with arith.
          eapply IHn in H2''''; eauto.
          destruct H2''''.
          eapply encode_nat_add_ptr_OK in H7; eauto.
          eapply encode_string_add_ptr_OK in H7; eauto.
          apply encode_nat_peekE in H2''; subst.
          apply encode_string_peekE in H2'''; subst.
          apply (addPeekE _ 1) in Heqy; destruct Heqy as [ [? ?] | ? ].
          simpl in H11; rewrite H11 in H2''; injections.
          eapply (addPeekE) in H2''; destruct H2'' as [ [? ?] | ? ].
          rewrite H8 in H2'''.
          apply H9 in H2'''; eauto.
          rewrite !pointerT2Nat_Nat2pointerT in H2'''; eauto.
          omega.
          simpl in H4; rewrite H8 in H2'''.
          intuition.
          simpl in H11; rewrite H11 in H2''.
          eapply addPeekENone in H2''; rewrite H2'' in H2'''.
          intuition.
          intuition.
          generalize (f_equal String.length H9); simpl;
            rewrite !length_append; simpl; omega.
          injections; simpl; omega.
          congruence.
          split; intros. try congruence.
          generalize H2'' H2'''.
          apply encode_nat_peekE in H2''; subst.
          apply encode_string_peekE in H2'''; subst; intros.
          eapply addPeekENone in Heqy; rewrite Heqy in H2''.
          eapply addPeekENone in H2''; rewrite H2'' in H2'''.
          eapply InCacheFixpoint_Overflow in H2''''; eauto.
          destruct (fun H => in_dec H p0 (getE xenv'' x9)); eauto.
          apply pointerT_eq_dec.
          eapply encode_nat_add_ptr_OK in n0; eauto.
          eapply encode_string_add_ptr_OK in n0; eauto; intuition.
  Qed.

  Lemma decode_string_peek_distinct
    : forall n xenv xenv' b b' l,
      decode_string n b xenv = Some (l, b', xenv')
      -> peekD xenv' = peekD (addD xenv (n * 8)).
  Proof.
    induction n; simpl; intros.
    - injections; eauto.
    - apply DecodeBindOpt2_inv in H;
        destruct H as [? [? [? [? ?] ] ] ]; injections; subst.
      destruct (decode_string n x0 x1) eqn: ?; simpl in *; try discriminate.
      destruct p; destruct p; injections.
      unfold decode_ascii in H.
      apply DecodeBindOpt2_inv in H;
        destruct H as [? [? [? [? ?] ] ] ]; injections; subst.
      eapply decode_word_peek_distinct in H; eauto.
      eapply IHn in Heqo; eauto; rewrite Heqo.
      destruct (peekD xenv) eqn: peekD_eq.
      + destruct (Compare_dec.lt_dec (1 + n + pointerT2Nat p) (pow2 14)).
        * destruct (addPeekSome _ 1 _ peekD_eq) as [p' [? ?] ]; try omega.
          simpl in H0; rewrite H0 in H.
          destruct (addPeekSome _ n _ H) as [p'' [? ?] ]; try omega.
          destruct (addPeekSome _ (S n) _ peekD_eq) as [p''' [? ?] ]; try omega.
          simpl in H4; rewrite H4.
          rewrite H1 in H3.
          simpl in H2; rewrite H2.
          f_equal.
          rewrite <- Nat2pointerT_pointerT2Nat, H5.
          rewrite <- (Nat2pointerT_pointerT2Nat p''), H3.
          f_equal.
          omega.
        * destruct (Compare_dec.lt_dec (1 + pointerT2Nat p) (pow2 14)).
          { destruct (addPeekSome _ 1 _ peekD_eq) as [p' [? ?] ];
              try omega.
            pose proof (addPeekNone' xenv (S n)) as H'; simpl in H'; erewrite H';
              eauto; clear H'.
            simpl in H0; rewrite H0 in H; eauto.
            eapply addPeekNone'; eauto.
            rewrite H1.
            simpl; omega.
          }
          { rewrite addPeekNone; auto.
            pose proof (addPeekNone' xenv (S n)) as H'; simpl in H'; erewrite H';
              eauto; clear H'.
            rewrite H.
            eapply (addPeekNone' _ 1); eauto.
          }
      + rewrite !addPeekNone; auto.
        rewrite H.
        apply addPeekNone; eauto.
  Qed.

  Lemma cache_inv_add_ptr_OK
    (P_OK :
             cache_inv_Property
               cache_inv
               (fun P =>
                  (forall env (p : pointerT) domain,
                    P env
                    -> getD env p = Some domain
                    -> ValidDomainName domain /\ (String.length domain > 0)%nat)
                  /\ (forall env p domain,
                         P env
                         -> (ValidDomainName domain /\ String.length domain > 0)%nat
                         -> getD env p = None
                         -> (forall p', peekD env = Some p'
                                        -> lt (pointerT2Nat p) (pointerT2Nat p'))
                         -> P (addD_G env (domain, p)))
                  /\ (forall (b : nat) (cd : CacheDecode),
                    P cd
                    -> P (addD cd b))
                  /\ (forall p (cd : CacheDecode) domain,
                         P cd
                         -> getD cd p = Some domain
                         -> forall p',
                             peekD cd = Some p'
                             -> lt (pointerT2Nat p) (pointerT2Nat p'))
          ))
    : forall env envE p domain,
      cache_inv env
      -> Equiv envE env
      -> peekD env = Some p
      -> add_ptr_OK (domain, p) envE env.
  Proof.
    unfold cache_inv_Property, add_ptr_OK in *; simpl; intros.
    destruct (getD env p) eqn: ?; eauto.
    eapply (proj2 (proj2 (proj2 P_OK))) in Heqo; eauto.
    omega.
  Qed.

  Theorem DomainName_decode_correct
          (P_OK :
             cache_inv_Property
               cache_inv
               (fun P =>
                  (forall env (p : pointerT) domain,
                    P env
                    -> getD env p = Some domain
                    -> ValidDomainName domain /\ (String.length domain > 0)%nat)
                  /\ (forall env p domain,
                         P env
                         -> (ValidDomainName domain /\ String.length domain > 0)%nat
                         -> getD env p = None
                         -> (forall p', peekD env = Some p'
                                        -> lt (pointerT2Nat p) (pointerT2Nat p'))
                         -> P (addD_G env (domain, p)))
                  /\ (forall (b : nat) (cd : CacheDecode),
                    P cd
                    -> P (addD cd b))
                  /\ (forall p (cd : CacheDecode) domain,
                         P cd
                         -> getD cd p = Some domain
                         -> forall p',
                             peekD cd = Some p'
                             -> lt (pointerT2Nat p) (pointerT2Nat p'))
          ))
    :
    encode_decode_correct_f
      cache transformer
      (fun domain => ValidDomainName domain)
      (fun s b => True)
      encode_DomainName_Spec decode_DomainName cache_inv.
  Proof.
    unfold encode_decode_correct_f; split.
    { intros env xenv xenv' l l' ext ? Eeq Valid_data
             Ppred_rest Penc.
      unfold decode_DomainName in *; simpl in *.
      unfold encode_DomainName_Spec in Penc.
      assert (exists xenv'0 : CacheDecode,
     Fix well_founded_lt_b (fun _ : B => CacheDecode -> option (DomainName * B * CacheDecode))
       (fun (b0 : B) (rec : forall y : B, lt_B y b0 -> CacheDecode -> option (DomainName * B * CacheDecode)) (cd : CacheDecode) =>
        `(labelheader, b1, env') <- Decode_w_Measure_le decode_word b0 cd decode_word_le;
        match wlt_dec WO~1~0~1~1~1~1~1~1 labelheader with
        | left l0 =>
            `(ps, b2, env'0) <- Decode_w_Measure_le decode_word (` b1) env' decode_word_le;
            match getD cd (exist (wlt WO~1~0~1~1~1~1~1~1) labelheader l0, ps) with
            | Some ""%string => None
            | Some (String _ _ as domain) => Some (domain, ` b2, env'0)
            | None => None
            end
        | in_right =>
            If wlt_dec labelheader WO~0~1~0~0~0~0~0~0
            Then match weq labelheader (wzero 8) with
                 | in_left => Some (""%string, ` b1, env')
                 | right n =>
                     `(label, b3, env'0) <- Decode_w_Measure_lt
                                              (decode_string (wordToNat labelheader))
                                              (` b1) env'
                                              (decode_string_lt (wordToNat labelheader) (n_eq_0_lt labelheader n));
                     Ifopt index 0 "." label as _ Then None
                     Else (`(domain, b4, e3) <- rec (` b3) (lt_B_trans b0 b1 b3) env'0;
                           If string_dec domain "" Then
                              Some (label, b4,
                                    Ifopt (peekD cd) as curPtr Then addD_G e3 (label, curPtr)
                                                               Else e3)
                           Else Some
                           ((label ++ String "." domain)%string, b4,
                            Ifopt (peekD cd) as curPtr Then addD_G e3 ((label ++ String "." domain)%string, curPtr)
                                                       Else e3))
                 end Else None
        end) (transform l' ext) xenv = Some (l, ext, xenv'0) /\
     Equiv xenv' xenv'0 /\ cache_inv xenv'0).
      simpl in *.
      generalize dependent l';
        generalize dependent env;
        generalize dependent xenv;
        generalize ext; generalize dependent xenv'.
      generalize (Le.le_refl (String.length l)) as le_n.
      remember (String.length l) as n.
      rewrite Heqn at 1.
      clear Heqn; generalize dependent l.
      induction n; intros; simpl in *.
      destruct l; simpl in *; try omega.
      { apply (unroll_LeastFixedPoint (fDom := [DomainName; CacheEncode]) (fCod := (B * CacheEncode))) in Penc; auto using encode_body_monotone; simpl in Penc.
         destruct (proj1 (Ascii_decode_correct (proj1 (proj2 (proj2 P_OK))))
                        _ _ _ _ _ ext0 env_OK Eeq I I Penc) as [? [? [? x2_OK] ] ].
        apply DecodeBindOpt2_inv in H0;
          destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
        eexists; repeat split.
        + unfold encode_ascii_Spec, encode_word_Spec in Penc;
          computes_to_inv; subst; simpl in *; injections.
          rewrite Init.Wf.Fix_eq; auto using decode_body_monotone; simpl.
          match goal with
            |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
            destruct (Decode_w_Measure_le_eq x y z m H0) as [? H2];
              rewrite H2
          end.
          apply terminal_char_eq in H5; rewrite H5.
          reflexivity.
        + auto.
        (* + erewrite peek_correct by eauto.
          eapply add_peekD_OK with (domain := ""%string) in Eeq; unfold add_ptr_OK in *; eauto.
          unfold decode_word in H0.
          destruct (decode_word' 8 (transform l' x1)); simpl in *; try discriminate.
          injections; rewrite IndependentCaches; eauto. *)
        + eauto.
        + unfold Frame.monotonic_function; simpl.
          intros; eapply encode_body_monotone; assumption.
      }
      { apply (unroll_LeastFixedPoint (fDom := [DomainName; CacheEncode]) (fCod := (B * CacheEncode))) in Penc;
        try solve [unfold Frame.monotonic_function; simpl;
                   intros; eapply encode_body_monotone; assumption];
        auto using encode_body_monotone.
        { destruct (string_dec l ""); simpl in Penc.
          (* Base case for domain name. *)
          - destruct (proj1 (Ascii_decode_correct (proj1 (proj2 (proj2 P_OK))))
                            _ _ _ _ _ ext0 env_OK Eeq I I Penc) as [? [? [? xenv_OK] ] ].
            apply DecodeBindOpt2_inv in H0;
              destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
            eexists; repeat split.
            + unfold encode_ascii_Spec, encode_word_Spec in Penc;
                computes_to_inv; subst; simpl in *; injections.
              rewrite Init.Wf.Fix_eq; auto using decode_body_monotone; simpl.
              match goal with
                |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
                destruct (Decode_w_Measure_le_eq x y z m H0) as [? H2];
                  rewrite H2
              end.
              apply terminal_char_eq in H5; rewrite H5.
              reflexivity.
            + assumption.
            + assumption.
          - simpl in Penc; computes_to_inv.
            destruct v as [ [ptr1 ptr2] | ]; simpl in Penc'; computes_to_inv.
            { (* Encoder used compression. *)
              simpl in Penc'; unfold Bind2 in Penc'; computes_to_inv.
              destruct v as [b xenv'']; destruct v0 as [b' xenv'''];
                simpl in *; injections.
              unfold encode_word_Spec in Penc', Penc'';
                  computes_to_inv; subst; simpl in *; injections.
                eexists; repeat split.
                rewrite Init.Wf.Fix_eq; simpl.
              + match goal with
                  |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
                  pose proof (Decode_w_Measure_le_eq x y z m)
                end.
                simpl in H0;
                  unfold decode_word at 1 in H0;
                  rewrite <- transform_assoc,
                  <- transformer_dequeue_word_eq_decode_word',
                  transformer_dequeue_encode_word' in H0;
                  simpl in H0;
                  destruct (H0 _ _ _ (eq_refl _)) as [? H']; clear H0.
                rewrite <- transform_assoc, H'; simpl.
                destruct (wlt_dec WO~1~0~1~1~1~1~1~1 (proj1_sig ptr1)); simpl.
                * match goal with
                    |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
                    pose proof (Decode_w_Measure_le_eq x y z m)
                  end.
                  simpl in H0; unfold decode_word at 1 in H0;
                    rewrite <- transformer_dequeue_word_eq_decode_word' in H0.
                  rewrite transformer_dequeue_encode_word' in H0.
                  simpl in H0;
                    destruct (H0 _ _ _ (eq_refl _)) as [? H'']; clear H0;
                      rewrite H''; clear H''; simpl.
                  rewrite <- (ptr_eq ptr1 (exist _ _ w)).
                  replace (getD xenv (ptr1, ptr2)) with (Some l).
                  destruct l; try congruence.
                  reflexivity.
                  pose proof (Penc _ (refl_equal _)) as GetPtr.
                  eapply get_correct in GetPtr; eauto;
                    unfold DomainName, pointerT in *;
                    simpl; reflexivity.
                  reflexivity.
                * destruct ptr1 as [ptr1 ptr1_OK].
                  simpl in *.
                  elimtype False; apply n1; eauto.
              + intros; apply functional_extensionality; intros.
                repeat (f_equal; apply functional_extensionality; intros).
                destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x1); simpl.
                repeat (f_equal; apply functional_extensionality; intros).
                destruct (wlt_dec x1 WO~0~1~0~0~0~0~0~0); simpl.
                destruct (weq x1 (wzero 8)).
                reflexivity.
                repeat (f_equal; apply functional_extensionality; intros).
                rewrite H0; reflexivity.
                reflexivity.
              + repeat apply add_correct; eauto.
              + eapply P_OK. eapply P_OK; eassumption .
            }
          { (* Encoder did not to compress *)
            simpl in Penc'; unfold Bind2 in Penc'; computes_to_inv.
            destruct Penc' as [l_eq [label1_OK label1_OK'] ].
            destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
              destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
                simpl in *; injections.
            destruct l_eq as [l_eq' | l_eq'].
            - destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) I Eeq H I Penc'') as [xenv4 [? xenv_eqv] ].
            pose proof ((proj1 Valid_data) ""%string label1 _ l_eq' label1_OK).
            unfold pow2; omega.
            destruct (fun H => proj1 (String_decode_correct (P := fun _ => True) (fun _ _ _ => I) (String.length label1)) _ _ _ _ _ (transform b3 ext0) I (proj1 xenv_eqv) H I Penc''') as [xenv6 [? xenv6_eqv] ]; eauto.
            pose proof (fun a b c d e =>
                          InCacheFixpoint (String.length label2) _ _ _ _ a b c d e Penc'''')
                 as xenv'0_OK.
            pose proof (fun n p z q m o n' => PeekCacheFixpoint n _ _ _ _ p z q m o n' Penc'''')
              as p_bnd.
            pose proof (fun n p z q m o => PeekCacheFixpoint_Overflow n _ _ _ _ p z q m o Penc'''')
              as p_bnd'.
            eapply IHn in Penc''''.
            destruct Penc'''' as [xenv7 [? [? xenv7_OK] ] ].
            eexists; split.
            rewrite Init.Wf.Fix_eq; auto using decode_body_monotone; simpl.
            + match goal with
                |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
                pose proof (Decode_w_Measure_le_eq x y z m)
              end.
              simpl in H4;
                unfold decode_word at 1 in H4.
              rewrite <- !transform_assoc in H4.
              unfold decode_nat in H0.
              apply DecodeBindOpt2_inv in H0;
                destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
              unfold decode_word in H0.
              destruct (decode_word' 8 (transform b' (transform b'' (transform b3 ext0)))); simpl in H0; try discriminate; injections.
              simpl in H4.
              destruct (H4 _ _ _ (eq_refl _)).
              rewrite <- !transform_assoc, H0; simpl; clear H0.
              pose proof ((proj1 Valid_data) ""%string label1 _ (eq_refl _) label1_OK) as w';
                rewrite H8 in w'.
              destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x); simpl;
                try (elimtype False;
                     apply WordFacts.wordToNat_lt in w; simpl in w; omega).
              destruct (wlt_dec x WO~0~1~0~0~0~0~0~0); simpl.
              * destruct (weq x (wzero 8)).
                subst; simpl in H8.
                destruct label1; simpl in H8; try discriminate.
                unfold ValidLabel in label1_OK; simpl in label1_OK; omega.
                match goal with
                  |- context [Decode_w_Measure_lt ?x ?y ?z ?m] =>
                  pose proof (Decode_w_Measure_lt_eq x y z m)
                end.
                simpl in H0; rewrite H8 in H1; rewrite H1 in H0.
                destruct (H0 _ _ _ (eq_refl _)).
                rewrite H5; simpl; rewrite H2.
                destruct label1_OK as [H6' _]; rewrite H6';
                  simpl.
                destruct (string_dec label2 ""); simpl;
                  try reflexivity.
                generalize (proj2 Valid_data label1 label2 (eq_refl _)); intros;
                  rewrite e in H6; intuition.
              * destruct n2.
                rewrite <- natToWord_wordToNat;
                  rewrite <- (natToWord_wordToNat x).
                apply WordFacts.natToWord_wlt.
                simpl.
                apply Nomega.Nlt_in.
                rewrite Nnat.Nat2N.id; etransitivity; eauto.
                simpl. unfold BinPos.Pos.to_nat; simpl.
                revert w' n1; clear.
                intros; omega.
                apply Nomega.Nlt_in.
                simpl. unfold BinPos.Pos.to_nat; simpl.
                revert w' n1; clear; intros; omega.
                revert w' n1; clear; intros; simpl; omega.
            + split.
              erewrite l_eq', peek_correct by eauto.
              destruct (peekD xenv) eqn: peekD_eq.
              simpl; apply add_correct_G; eauto.
              intuition.
              apply DecodeBindOpt2_inv in H0;
                destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
              pose proof (fun s => cache_inv_add_ptr_OK P_OK _ _ _ s env_OK Eeq peekD_eq) as Q.
              pose proof (decode_word_peek_distinct _ _ _ _ _ _ H0) as P.
              pose proof (decode_string_peek_distinct _ _ _ _ _ _ H1) as P'.
              eapply decode_word_add_ptr_OK in H0; eauto.
              eapply decode_string_add_ptr_OK in H1; eauto.
                            assert (forall p', peekD xenv6 = Some p'
                                 -> (pointerT2Nat p < pointerT2Nat p')%nat) as P3.
              { clear H0 H1.
                intros.
                apply (addPeek _ 1) in peekD_eq;
                  destruct peekD_eq as [ [peekD_eq peekD_bnd] | peekD_eq];
                  simpl in peekD_eq; rewrite peekD_eq in P.
                eapply (addPeek _ (String.length label1)) in P;
                  destruct P as [ [P P_bnd] | P];
                  rewrite P in P';
                  rewrite P' in H0; try discriminate.
                injection H0; intro H4'; rewrite <- H4'.
                rewrite pointerT2Nat_Nat2pointerT by auto.
                rewrite pointerT2Nat_Nat2pointerT by auto.
                omega.
                rewrite addPeekNone in P' by auto.
                congruence.
              }
              unfold add_ptr_OK in *; simpl in *;
                revert addPeekSome addPeekNone addZeroPeek addPeekNone' getDistinct IndependentCaches
                       boundPeekSome H2 H1 P P' P3; generalize xenv env p peekD_eq ; clear.
              generalize (transform b3 ext0); intros b xenv env p peekD_eq.
              revert label2 xenv6 xenv7 ext0 x1.
              generalize env xenv (String.length label1); clear.
              eapply (@well_founded_induction _ _ well_founded_lt_b) with
              (a := b); intros.
              rewrite Coq.Init.Wf.Fix_eq in H2; auto using decode_body_monotone; simpl.
              apply DecodeBindOpt2_inv in H2;
                destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
              destruct (wlt_dec  WO~1~0~1~1~1~1~1~1 x0); simpl in H2.
              * (* The decoded word was a pointer. *)
                symmetry in H2; apply DecodeBindOpt2_inv in H2;
                  destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
                match type of H3 with
                | context [getD ?env' ?w] => destruct (getD env' w) eqn:getD_eq;
                                               try discriminate
                end.
                destruct s; try discriminate; injections.
                eapply Decode_w_Measure_le_eq' in H2.
                eapply Decode_w_Measure_le_eq' in H0.
                unfold decode_word in H0.
                destruct (decode_word' 8 x); simpl in *; try discriminate; injections.
                unfold decode_word in H2.
                destruct (decode_word' 8 (projT1 x2)); simpl in *; try discriminate; injections.
                repeat match type of H2 with
                       | context [dequeue_opt ?b] => destruct (dequeue_opt b) as [ [? ?] | ]; simpl in H2; try discriminate
                       end.
                injections.
                rewrite !IndependentCaches; eauto.
                repeat match type of H2 with
                       | context [dequeue_opt ?b] => destruct (dequeue_opt b) as [ [? ?] | ]; simpl in H2; try discriminate
                       end.
                injections.
                rewrite !IndependentCaches; eauto.
                eauto.
                eauto.
              * destruct (wlt_dec x0 WO~0~1~0~0~0~0~0~0); simpl in H2; try discriminate.
                destruct (weq x0 (wzero 8)); simpl in H2.
                injections.
                eapply Decode_w_Measure_le_eq' in H0.
                unfold decode_word in H0.
                destruct (decode_word' 8 x); simpl in *; try discriminate; injections.
                rewrite IndependentCaches; eauto.
                eauto.
                symmetry in H2; apply DecodeBindOpt2_inv in H2;
                  destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
                destruct (index 0 "." x4); simpl in H3; try discriminate.
                match type of H3 with
                | context [Fix well_founded_lt_b ?H' ?H0' ?H1' ?H2' ] =>
                  destruct (Fix well_founded_lt_b H' H0' H1' H2') as [ [ [? ?] ?] | ] eqn:rec; simpl in H3;
                    try discriminate
                end.
                eapply Decode_w_Measure_le_eq' in H0; eauto.
                eapply Decode_w_Measure_lt_eq' in H2; eauto.
                pose proof (decode_word_peek_distinct _ _ _ _ _ _ H0) as P''.
                pose proof (decode_string_peek_distinct _ _ _ _ _ _ H2) as P'''.
                assert (getD x6 p = None) by
                    (revert IndependentCaches H0 H2 H1 env; clear; intros;
                     eapply decode_word_add_ptr_OK with (env := env) (env' := env) in H0; eauto;
                     eapply decode_string_add_ptr_OK with (env := env) in H2; eauto).
                simpl in P'''.
                destruct (string_dec d ""); simpl in H3; injections;
                  eapply (H) with (x1 := x3) (xenv := xenv6) in rec; eauto using lt_B_trans.
                destruct (peekD xenv6) eqn: ?; simpl; eauto.
                rewrite getDistinct; eauto.
                intro; subst; generalize (P3 _ (eq_refl _)); omega.
                intros.
                destruct (peekD xenv6) eqn: peekD_eq; simpl; eauto.
                pose proof (P3 _ (eq_refl _)).
                eapply (addPeek _ 1) in peekD_eq;
                  destruct peekD_eq as [ [peekD_eq peekD_bnd] | peekD_eq];
                  simpl in peekD_eq; rewrite peekD_eq in P''.
                apply (addPeek _ (wordToNat x0)) in P'';
                  destruct P'' as [ [P'' P''_bnd] | P''];
                  rewrite P'' in P'''; rewrite P''' in H3;
                    try discriminate.
                injection H3; intro H'; rewrite <- H'.
                rewrite pointerT2Nat_Nat2pointerT by auto.
                rewrite pointerT2Nat_Nat2pointerT by auto.
                omega.
                rewrite addPeekNone in P''' by auto;
                  rewrite P''' in H3; congruence.
                rewrite P''' in H3.
                rewrite addPeekNone in H3; try discriminate.
                rewrite P'', addPeekNone; eauto.
                destruct (peekD xenv6) eqn: ?; simpl; eauto.
                rewrite getDistinct; eauto.
                intro; subst; generalize (P3 _ (eq_refl _)); omega.
                intros.
                destruct (peekD xenv6) eqn: peekD_eq; simpl; eauto.
                pose proof (P3 _ (eq_refl _)).
                eapply (addPeek _ 1) in peekD_eq;
                  destruct peekD_eq as [ [peekD_eq peekD_bnd] | peekD_eq];
                  simpl in peekD_eq; rewrite peekD_eq in P''.
                apply (addPeek _ (wordToNat x0)) in P'';
                  destruct P'' as [ [P'' P''_bnd] | P''];
                  rewrite P'' in P'''; rewrite P''' in H3;
                    try discriminate.
                injection H3; intro H'; rewrite <- H'.
                rewrite pointerT2Nat_Nat2pointerT by auto.
                rewrite pointerT2Nat_Nat2pointerT by auto.
                omega.
                rewrite addPeekNone in P''' by auto;
                  rewrite P''' in H3; congruence.
                rewrite P''' in H3.
                rewrite addPeekNone in H3; try discriminate.
                rewrite P'', addPeekNone; eauto.
              * simpl; intuition eauto.
              * destruct (peekD xenv) eqn: ?; simpl; eauto.
                apply P_OK; intuition eauto.
                rewrite <- l_eq'; eauto.
                rewrite !length_append; simpl; omega.
                destruct (getD xenv7 p) eqn: ?; auto.
                rewrite get_correct in Heqo; eauto.
                eapply xenv'0_OK in Heqo; intuition eauto.
                assert (~ In p (getE env s)).
                { rewrite <- get_correct by eauto; intro.
                  eapply P_OK in Heqy; eauto.
                  omega.
                }
                pose proof (encode_nat_peekE _ _ _ _ _ Penc'').
                pose proof (encode_string_peekE _ _ _ _ Penc''').
                eapply encode_nat_add_ptr_OK in Penc''; eauto.
                eapply encode_string_add_ptr_OK in Penc'''; eauto.
                destruct (peekE xenv'''') eqn: ?; intuition.
                pose proof (H8 _ Penc''' (eq_refl _)).
                erewrite <- peek_correct in Heqy by eauto.
                apply (addPeekE _ 1) in Heqy; destruct Heqy as [ [? ?] | ? ].
                simpl in H14; rewrite H14 in H11; injections.
                eapply (addPeekE) in H11; destruct H11 as [ [? ?] | ? ];
                  rewrite H11 in H12.
                injections.
                rewrite !pointerT2Nat_Nat2pointerT in H13; eauto.
                omega.
                congruence.
                rewrite addPeekENone in H12. congruence.
                simpl in H14; rewrite H14 in H11; auto.
                apply DecodeBindOpt2_inv in H0;
                  destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
                eapply decode_word_peek_distinct in H0.
                eapply decode_string_peek_distinct in H1.
                eapply (addPeek _ 1) in Heqy;
                  destruct Heqy as [ [peekD_eq peekD_bnd] | peekD_eq];
                  simpl in peekD_eq; rewrite peekD_eq in H0.
                apply (addPeek _ (String.length label1)) in H0;
                  destruct H0 as [ [P'' P''_bnd] | P''];
                  rewrite P'' in H1.
                apply Lt.lt_le_trans with
                  (m := pointerT2Nat (Nat2pointerT (String.length label1 + (S (pointerT2Nat p))))).
                  rewrite pointerT2Nat_Nat2pointerT; try omega.
                  rewrite pointerT2Nat_Nat2pointerT in P''_bnd; try omega.
                  eapply  p_bnd; eauto.
                  erewrite peek_correct; eauto.
                  rewrite H1, pointerT2Nat_Nat2pointerT; eauto.
                  erewrite peek_correct; eauto.
                  erewrite <- peek_correct in H8; eauto.
                  erewrite p_bnd' in H8; eauto.
                  discriminate.
                  erewrite peek_correct; eauto.
                  erewrite <- peek_correct in H8 by eauto.
                  erewrite p_bnd' in H8; eauto; try discriminate.
                  erewrite peek_correct by eassumption.
                  rewrite H1; eauto.
            + subst; eauto using ValidDomainName_app.
            + subst; eauto using chomp_label_length.
            + destruct (fun H H' => proj2 (Nat_decode_correct (P := cache_inv) 8 H') _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H H0) as [xenv'' [? xenv''_eqv] ]; eauto.
              unfold cache_inv_Property in *; intuition.
              destruct (fun H H' => proj2 (String_decode_correct (P := cache_inv) H' (String.length label1)) _ _ _ _ _ (transform b3 ext0) (proj1 xenv_eqv) H H1) as [xenv10 [? xenv10_eqv] ]; intuition eauto.
              unfold cache_inv_Property in *; intuition.
            + intuition.
            - injections.
              destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) I Eeq H I Penc'') as [xenv4 [? [xenv_eqv _] ] ].
              pose proof (proj1 Valid_data ""%string l ""%string (append_EmptyString_r _) label1_OK).
              unfold pow2; simpl; omega.
              destruct (fun H H' => proj1 (String_decode_correct (P := fun _ => True) (fun _ _ _ => I) (String.length l)) _ xenv4 _ _ _ (transform b3 ext0) I H' H I Penc''') as [xenv6 [? [xenv6_eqv _] ] ]; eauto.
              intuition.
              simpl in Penc''''.
              pose proof (fun a b c d e =>
                            InCacheFixpoint (String.length "") _ _ _ _ a b c d e Penc'''')
                as xenv'0_OK.
              pose proof (fun n p z q m o n' => PeekCacheFixpoint n _ _ _ _ p z q m o n' Penc'''')
              as p_bnd.
            pose proof (fun n p z q m o => PeekCacheFixpoint_Overflow n _ _ _ _ p z q m o Penc'''')
              as p_bnd'.
              eapply IHn in Penc''''.
              destruct Penc'''' as [xenv7 [? [? xenv7_OK] ] ].
              eexists; split.
              rewrite Init.Wf.Fix_eq; auto using decode_body_monotone; simpl.
              match goal with
                |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
                pose proof (Decode_w_Measure_le_eq x y z m)
              end.
              simpl in H4;
                unfold decode_word at 1 in H4.
              rewrite <- !transform_assoc in H4.
              unfold decode_nat in H0.
              apply DecodeBindOpt2_inv in H0;
                destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
              unfold decode_word in H0.
              destruct (decode_word' 8 (transform b' (transform b'' (transform b3 ext0)))); simpl in H0; try discriminate; injections.
              simpl in H4.
              destruct (H4 _ _ _ (eq_refl _)).
              rewrite <- !transform_assoc, H0; simpl; clear H0.
              pose proof (proj1 Valid_data ""%string l _ (append_EmptyString_r _) label1_OK) as w';
                rewrite H8 in w'.
              destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x); simpl;
                try (elimtype False; apply WordFacts.wordToNat_lt in w; simpl in w; omega).
              destruct (wlt_dec x WO~0~1~0~0~0~0~0~0); simpl.
              destruct (weq x (wzero 8)).
              subst; simpl in H8.
              destruct l; simpl in H8; try discriminate.
              unfold ValidLabel in label1_OK; simpl in label1_OK; omega.
              match goal with
                |- context [Decode_w_Measure_lt ?x ?y ?z ?m] =>
                pose proof (Decode_w_Measure_lt_eq x y z m)
              end.

              simpl in H0; rewrite H8 in H1; rewrite H1 in H0.
              destruct (H0 _ _ _ (eq_refl _)).
              rewrite H5; simpl; rewrite H2.
              destruct label1_OK as [H6' _]; rewrite H6';
                simpl.
              reflexivity.
              unfold not in n2.
              assert (WO~0~1~0~0~0~0~0~0 < x \/ WO~0~1~0~0~0~0~0~0 = x)
                by (destruct (weq WO~0~1~0~0~0~0~0~0 x); eauto using le_neq_lt).
              destruct H0; eauto.
              generalize (WordFacts.wordToNat_lt H0); simpl; omega.
              generalize (f_equal (@wordToNat 8) H0); simpl; omega.
              split. erewrite peek_correct; eauto.
              destruct (peekD xenv) eqn: ?; simpl; intuition eauto.
              apply add_correct_G; intuition eauto.
              { unfold decode_nat in H0.
                apply DecodeBindOpt2_inv in H0;
                  destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
                pose proof (cache_inv_add_ptr_OK P_OK _ _ _ l env_OK Eeq Heqy) as Q.
              pose proof (decode_word_peek_distinct _ _ _ _ _ _ H0) as P.
              pose proof (decode_string_peek_distinct _ _ _ _ _ _ H1) as P'.
              eapply decode_word_add_ptr_OK with (env := env) (env' := env) in H0; eauto.
                eapply decode_string_add_ptr_OK with (env := env)  in H1; eauto.
                unfold add_ptr_OK in *; simpl in *; revert getDistinct IndependentCaches H2 H1.
                (*remember ""%string as s'; rewrite Heqs'; rewrite <- Heqs' at 1. *)
                generalize env; clear.
                generalize (transform b3 ext0) ; intro.
                revert xenv6 xenv7 ext0 .
                eapply (@well_founded_induction _ _ well_founded_lt_b) with
                (a := b); intros.
                rewrite Coq.Init.Wf.Fix_eq in H2; auto using decode_body_monotone; simpl.
                apply DecodeBindOpt2_inv in H2;
                  destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
                destruct (wlt_dec  WO~1~0~1~1~1~1~1~1 x0); simpl in H2.
                * (* The decoded word was a pointer. *)
                  symmetry in H2; apply DecodeBindOpt2_inv in H2;
                    destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
                  match type of H3 with
                  | context [getD ?env' ?w] => destruct (getD env' w) eqn:getD_eq;
                                                 try discriminate
                    end.
                  destruct s; try discriminate; injections.
                * destruct (wlt_dec x0 WO~0~1~0~0~0~0~0~0); simpl in H2; try discriminate.
                  destruct (weq x0 (wzero 8)); simpl in H2.
                  injections.
                  eapply Decode_w_Measure_le_eq' in H0; eauto.
                  eapply decode_word_add_ptr_OK with (env := env) (env' := env) in H0; eauto.
                  eapply Decode_w_Measure_le_eq' in H0; eauto.
                  (*eapply decode_word_add_ptr_OK in H2; eauto. *)
                  symmetry in H2; apply DecodeBindOpt2_inv in H2;
                    destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
                  destruct (index 0 "." x3); simpl in H3; try discriminate.
                  match type of H3 with
                  | context [Fix well_founded_lt_b ?H' ?H0' ?H1' ?H2' ] =>
                    destruct (Fix well_founded_lt_b H' H0' H1' H2') as [ [ [? ?] ?] | ] eqn:rec; simpl in H3;
                      try discriminate
                  end.
                  eapply Decode_w_Measure_lt_eq' in H2; eauto.
                  (*eapply decode_string_add_ptr_OK in H4; eauto. *)
                  destruct (string_dec d ""); simpl in H3; injections.
                  elimtype False.
                  { apply n0.
                    assert (wordToNat x0 = 0).
                    { generalize H2; clear.
                      destruct (wordToNat x0); simpl; auto.
                      intros.
                      apply DecodeBindOpt2_inv in H2; destruct_ex;
                        intuition;
                        symmetry in H1;
                        apply DecodeBindOpt2_inv in H1; destruct_ex;
                          intuition.
                      congruence.
                    }
                    pose proof (f_equal (natToWord 8) H3).
                    rewrite natToWord_wordToNat in H4;
                      rewrite H4.
                    reflexivity.
                  }
                  elimtype False.
                  generalize H6; clear; induction x3;
                    simpl; try congruence.
                }
              { destruct (peekD xenv) eqn:? ; simpl; eauto.
                apply P_OK; intuition eauto.
                destruct l; simpl; intuition.
                destruct (getD xenv7 p) eqn: ?; auto.
                rewrite get_correct in Heqo; eauto.
                eapply xenv'0_OK in Heqo; intuition eauto.
                assert (~ In p (getE env s)).
                { rewrite <- get_correct by eauto; intro.
                  eapply P_OK in Heqy; eauto.
                  omega.
                }
                pose proof (encode_nat_peekE _ _ _ _ _ Penc'').
                pose proof (encode_string_peekE _ _ _ _ Penc''').
                eapply encode_nat_add_ptr_OK in Penc''; eauto.
                eapply encode_string_add_ptr_OK in Penc'''; eauto.
                destruct (peekE xenv'''') eqn: ?; intuition.
                pose proof (H4 _ Penc''' (eq_refl _)).
                erewrite <- peek_correct in Heqy by eauto.
                apply (addPeekE _ 1) in Heqy; destruct Heqy as [ [? ?] | ? ].
                simpl in H10; rewrite H10 in H7; injections.
                eapply (addPeekE) in H7; destruct H7 as [ [? ?] | ? ];
                  rewrite H7 in H8.
                injections.
                rewrite !pointerT2Nat_Nat2pointerT in H9; eauto.
                omega.
                congruence.
                rewrite addPeekENone in H8. congruence.
                simpl in H10; rewrite H10 in H7; auto.
                apply DecodeBindOpt2_inv in H0;
                  destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
                eapply decode_word_peek_distinct in H0.
                eapply decode_string_peek_distinct in H1.
                eapply (addPeek _ 1) in Heqy;
                  destruct Heqy as [ [peekD_eq peekD_bnd] | peekD_eq];
                  simpl in peekD_eq; rewrite peekD_eq in H0.
                apply (addPeek _ (String.length l)) in H0;
                  destruct H0 as [ [P'' P''_bnd] | P''];
                  rewrite P'' in H1.
                apply Lt.lt_le_trans with
                  (m := pointerT2Nat (Nat2pointerT (String.length l + (S (pointerT2Nat p))))).
                rewrite pointerT2Nat_Nat2pointerT; try omega.
                rewrite pointerT2Nat_Nat2pointerT in P''_bnd; try omega.
                eapply  p_bnd; eauto.
                erewrite peek_correct; eauto.
                rewrite H1, pointerT2Nat_Nat2pointerT; eauto.
                erewrite peek_correct; eauto.
                erewrite <- peek_correct in H4; eauto.
                erewrite p_bnd' in H4; eauto.
                discriminate.
                erewrite peek_correct; eauto.
                erewrite <- peek_correct in H4 by eauto.
                erewrite p_bnd' in H4; eauto; try discriminate.
                erewrite peek_correct by eassumption.
                rewrite H1; eauto.
              }
              * unfold ValidDomainName; split; intros.
                destruct pre; simpl in *; try discriminate.
                destruct label; simpl in *; try discriminate.
                omega.
                destruct pre; simpl in *; try discriminate.
              * simpl; omega.
              * destruct (fun H H' => proj2 (Nat_decode_correct (P := cache_inv) 8 H') _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H H0) as [xenv'' [? xenv''_eqv] ]; eauto.
              unfold cache_inv_Property in *; intuition.
              destruct (fun H H' => proj2 (String_decode_correct (P := cache_inv) H' (String.length l)) _ _ _ _ _ (transform b3 ext0) xenv_eqv H H1) as [xenv10 [? xenv10_eqv] ]; intuition eauto.
              unfold cache_inv_Property in *; intuition.
              * intuition.
          }
        }
      }
      destruct_ex; intuition; eauto. }
    {
      unfold decode_DomainName, encode_DomainName_Spec;
        intros env env' xenv' data bin;
        revert env env' xenv' data.

      eapply (@well_founded_induction _ _ well_founded_lt_b) with
      (a := bin); intros.
      rewrite Coq.Init.Wf.Fix_eq in H2; auto using decode_body_monotone; simpl.
      apply DecodeBindOpt2_inv in H2;
        destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
      destruct (wlt_dec (natToWord 8 191) x0); simpl in H3.
      - (* The decoded word was a pointer. *)
        symmetry in H3; apply DecodeBindOpt2_inv in H3;
          destruct H3 as [? [? [? [? ?] ] ] ]; injections; subst.
        match type of H4 with
        | context [getD ?env' ?w] => destruct (getD env' w) eqn:getD_eq;
                                       try discriminate
        end.
        destruct s; try discriminate; injections.
        eapply Decode_w_Measure_le_eq' in H2.
        eapply Decode_w_Measure_le_eq' in H3.
        destruct (proj2 (Word_decode_correct (proj1 (proj2 (proj2 P_OK)))) _ _ _ _ _ _ H0 H1 H2) as
            [? [b' [xenv [enc_x0 [x_eq [_ xenv_eqv] ] ] ] ] ].
        destruct (proj2 (Word_decode_correct (proj1 (proj2 (proj2 P_OK))))
                        _ _ _ _ _ _ xenv_eqv H4 H3) as
            [? [b'' [xenv' [enc_x0' [x_eq' [_ xenv_eqv'] ] ] ] ] ].
        split; eauto; eexists _, _; split; eauto.
        apply (unroll_LeastFixedPoint'
                 (fDom := [DomainName; CacheEncode])
                 (fCod := (B * CacheEncode)%type));
          unfold Frame.monotonic_function; simpl;
            auto using encode_body_monotone.
        intros; eapply encode_body_monotone.
        simpl; auto.
        rewrite get_correct in getD_eq; eauto.
        computes_to_econstructor.
        apply (@PickComputes _ _ (Some (exist (wlt WO~1~0~1~1~1~1~1~1) x0 w, x3))); eauto.
        intros; injection H6; intro H7; rewrite <- H7; eauto.
        simpl.
        simpl; computes_to_econstructor; eauto.
        simpl; computes_to_econstructor; eauto.
        eauto.
        intuition eauto.
        rewrite x_eq' in x_eq.
        simpl in *; rewrite <- transform_assoc; assumption.
        eapply P_OK; [ | eassumption ].
        assumption.
        assumption.
        assumption.
      - (* The decoded word was a length octet. *)
        destruct (wlt_dec x0 WO~0~1~0~0~0~0~0~0); try discriminate;
          simpl in H3.
        destruct (weq x0 (wzero 8)); simpl in H3.
        + (* This is the terminal character. *)
          injections.
          eapply Decode_w_Measure_le_eq' in H2.
          destruct (proj2 (Word_decode_correct (proj1 (proj2 (proj2 P_OK)))) _ _ _ _ _ _ H0 H1 H2) as
              [? [b' [xenv [enc_x0 [x_eq [_ xenv_eqv] ] ] ] ] ]; split; eauto.
          eexists _, _; split; eauto.
          apply (unroll_LeastFixedPoint'
                   (fDom := [DomainName; CacheEncode])
                   (fCod := (B * CacheEncode)%type));
            auto using encode_body_monotone.
          unfold Frame.monotonic_function; simpl;
            intros; eapply encode_body_monotone; assumption.
          simpl.
          econstructor.
          unfold encode_word_Spec in enc_x0; computes_to_inv;
            injection enc_x0; intros.
          rewrite <- H5 in x_eq.
          rewrite H4.
          repeat split; auto using ValidDomainName_Empty.
          intros; destruct pre; destruct label; try discriminate.
          simpl; omega.
          intros; destruct pre; try discriminate.
          intros; destruct pre; try discriminate.
          intros; destruct pre; try discriminate.
          intros; destruct pre; try discriminate.
          auto.
        + symmetry in H3; apply DecodeBindOpt2_inv in H3;
            destruct H3 as [? [? [? [? ?] ] ] ]; injections; subst.
          destruct (index 0 "." x3) as [? | ] eqn:x3_OK; simpl in H4; try discriminate.
          symmetry in H4; apply DecodeBindOpt2_inv in H4;
            destruct H4 as [? [? [? [? ?] ] ] ]; injections; subst.
          apply Decode_w_Measure_le_eq' in H2.
          apply Decode_w_Measure_lt_eq' in H3.
          destruct (proj2 (Word_decode_correct (proj1 (proj2 (proj2 P_OK)))) _ _ _ _ _ _ H0 H1 H2) as
              [? [b' [xenv [enc_x0 [x_eq [? xenv_eqv] ] ] ] ] ]; eauto.
          destruct (fun H  => proj2 (String_decode_correct
                                       (P := cache_inv)
                                       (proj1 (proj2 (proj2 P_OK)))
                                       (wordToNat x0))
                                    _ _ _ _ _ _ xenv_eqv H H3) as
              [? [b'' [xenv'' [enc_x0' [x_eq' [? xenv_eqv'] ] ] ] ] ]; eauto.
          eapply H in H4; eauto.
          intuition.
          destruct H11 as [bin' [xenv0 [? [? [? ? ] ] ] ] ].
          destruct (string_dec x6 ""); simpl in *;
            injections.
          { injection H5; intros; rewrite H14.
            destruct (peekD env') eqn: ?; simpl in *; eauto.
            eapply P_OK; eauto.
            split.
            unfold ValidDomainName; split; intros.
            rewrite H17 in H9; generalize H9.
            rewrite !length_append; intros.
            generalize w.
            assert (le (String.length label) (wordToNat x0)) by omega.
            intros; etransitivity; eauto.
            eapply WordFacts.wordToNat_lt in w0; simpl in w0; omega.
            rewrite H17 in x3_OK.
            apply (index_correct3 _ (String.length pre)) in x3_OK.
            elimtype False;
              generalize x3_OK; clear.
            { induction pre; simpl.
              - unfold substring; destruct post; simpl; congruence.
              - destruct pre; simpl.
                unfold substring; destruct post; simpl; congruence.
                auto.
            }
            congruence.
            destruct x3; simpl.
            elimtype False; eapply NonEmpty_String_wordToNat; eauto.
            omega.
            destruct x3; simpl.
            elimtype False; eapply NonEmpty_String_wordToNat; eauto.
            omega.
            destruct (getD x8 p) eqn: ?; eauto.
            rewrite get_correct in Heqo; eauto.
            eapply InCacheFixpoint in H4; eauto.
            destruct H4.
            destruct (fun H => in_dec H p (getE xenv'' s)).
            apply pointerT_eq_dec.
            elimtype False.
            eapply encode_string_add_ptr_OK; eauto.
            unfold encode_word_Spec in enc_x0; computes_to_inv;
              injection enc_x0; intros H' H''; rewrite <- H', H'' in *.
            rewrite IndependentCaches'.
            intro.
            rewrite <- get_correct in H18; eauto.
            eapply (proj2 (proj2 (proj2 P_OK))) in H18; eauto.
            omega.
            eapply addPeek  with (n := 1) in Heqy;
              intuition eauto.
            apply decode_word_peek_distinct in H2.
            simpl in H19; rewrite H19 in H2.
            eapply decode_string_peek_distinct in H3; eauto.
            eapply addPeek with (n := wordToNat x0) in H2;
              intuition eauto.
            rewrite <- H3 in H2.
            erewrite <- peek_correct in H2; eauto.
            eapply (fun H => H4 _ H H2) in n1.
            rewrite !pointerT2Nat_Nat2pointerT in n1; eauto.
            omega.
            rewrite <- H3 in H18.
            erewrite <- peek_correct in H18; eauto.
            apply H17 in H18; intuition.
            apply decode_word_peek_distinct in H2.
            simpl in H18; rewrite H18 in H2.
            eapply decode_string_peek_distinct in H3; eauto.
            eapply addPeekNone with (n := wordToNat x0 * 8) in H2.
            rewrite <- H3 in H2.
            erewrite <- peek_correct in H2; eauto.
            intuition.
            intros.
            eapply decode_word_peek_distinct in H2.
            eapply decode_string_peek_distinct in H3.
            eapply (addPeek _ 1) in Heqy;
              destruct Heqy as [ [peekD_eq peekD_bnd] | peekD_eq];
              simpl in peekD_eq; rewrite peekD_eq in H2.
            apply (addPeek _ (wordToNat x0 )) in H2;
              destruct H2 as [ [P'' P''_bnd] | P''];
              rewrite P'' in H3.
            apply Lt.lt_le_trans with
            (m := pointerT2Nat (Nat2pointerT (wordToNat x0 + (S (pointerT2Nat p))))).
            rewrite pointerT2Nat_Nat2pointerT; try omega.
            rewrite pointerT2Nat_Nat2pointerT in P''_bnd; try omega.
            pose proof (fun n p z q m o n' => PeekCacheFixpoint n _ _ _ _ p z q m o n' H4)
              as p_bnd.
            eapply p_bnd; eauto.
            erewrite peek_correct; eauto.
            rewrite H3, pointerT2Nat_Nat2pointerT; eauto.
            erewrite peek_correct; eauto.
            erewrite <- peek_correct in H17; eauto.
            pose proof (fun n p z q m o => PeekCacheFixpoint_Overflow n _ _ _ _ p z q m o H4)
              as p_bnd'.
            erewrite p_bnd' in H17; eauto.
            discriminate.
            erewrite peek_correct; eauto.
            erewrite <- peek_correct in H17 by eauto.
            erewrite (fun n p z q m o => PeekCacheFixpoint_Overflow n _ _ _ _ p z q m o H4) in H17; eauto; try discriminate.
            erewrite peek_correct by eassumption.
            rewrite H3; eauto.
          }
          { injection H5; intros; rewrite H14.
            destruct (peekD env') eqn: ?; simpl in *; eauto.
            eapply P_OK; eauto.
            split.
            eapply ValidDomainName_app'; eauto.
            unfold ValidLabel; split; eauto.
            destruct x3; simpl; try omega.
            elimtype False; eapply NonEmpty_String_wordToNat; eauto.
            eapply WordFacts.wordToNat_lt in w; simpl in w; omega.
            destruct x3; simpl; omega.
            destruct (getD x8 p) eqn: ?; eauto.
            rewrite get_correct in Heqo; eauto.
            eapply InCacheFixpoint in H4; eauto.
            destruct H4.
            destruct (fun H => in_dec H p (getE xenv'' s)).
            apply pointerT_eq_dec .
            elimtype False.
            eapply encode_string_add_ptr_OK; eauto.
            unfold encode_word_Spec in enc_x0; computes_to_inv;
              injection enc_x0; intros H' H''; rewrite <- H', H'' in *.
            rewrite IndependentCaches'.
            intro.
            rewrite <- get_correct in H18; eauto.
            eapply (proj2 (proj2 (proj2 P_OK))) in H18; eauto.
            omega.
            eapply addPeek  with (n := 1) in Heqy;
              intuition eauto.
            apply decode_word_peek_distinct in H2.
            simpl in H19; rewrite H19 in H2.
            eapply decode_string_peek_distinct in H3; eauto.
            eapply addPeek with (n := wordToNat x0) in H2;
              intuition eauto.
            rewrite <- H3 in H2.
            erewrite <- peek_correct in H2; eauto.
            eapply (fun H => H4 _ H H2) in n2.
            rewrite !pointerT2Nat_Nat2pointerT in n2; eauto.
            omega.
            rewrite <- H3 in H18.
            erewrite <- peek_correct in H18; eauto.
            apply H17 in H18; intuition.
            apply decode_word_peek_distinct in H2.
            simpl in H18; rewrite H18 in H2.
            eapply decode_string_peek_distinct in H3; eauto.
            eapply addPeekNone with (n := wordToNat x0 * 8) in H2.
            rewrite <- H3 in H2.
            erewrite <- peek_correct in H2; eauto.
            intuition.
            intros.
            eapply decode_word_peek_distinct in H2.
            eapply decode_string_peek_distinct in H3.
            eapply (addPeek _ 1) in Heqy;
              destruct Heqy as [ [peekD_eq peekD_bnd] | peekD_eq];
              simpl in peekD_eq; rewrite peekD_eq in H2.
            apply (addPeek _ (wordToNat x0 )) in H2;
              destruct H2 as [ [P'' P''_bnd] | P''];
              rewrite P'' in H3.
            apply Lt.lt_le_trans with
            (m := pointerT2Nat (Nat2pointerT (wordToNat x0 + (S (pointerT2Nat p))))).
            rewrite pointerT2Nat_Nat2pointerT; try omega.
            rewrite pointerT2Nat_Nat2pointerT in P''_bnd; try omega.
            pose proof (fun n p z q m o n' => PeekCacheFixpoint n _ _ _ _ p z q m o n' H4)
              as p_bnd.
            eapply p_bnd; eauto.
            erewrite peek_correct; eauto.
            rewrite H3, pointerT2Nat_Nat2pointerT; eauto.
            erewrite peek_correct; eauto.
            erewrite <- peek_correct in H17; eauto.
            pose proof (fun n p z q m o => PeekCacheFixpoint_Overflow n _ _ _ _ p z q m o H4)
              as p_bnd'.
            erewrite p_bnd' in H17; eauto.
            discriminate.
            erewrite peek_correct; eauto.
            erewrite <- peek_correct in H17 by eauto.
            erewrite (fun n p z q m o => PeekCacheFixpoint_Overflow n _ _ _ _ p z q m o H4) in H17; eauto; try discriminate.
            erewrite peek_correct by eassumption.
            rewrite H3; eauto.
          }
          destruct H11 as [bin' [xenv0 [? [? [? ? ] ] ] ] ].
          eexists _, _; split; eauto.
          apply (unroll_LeastFixedPoint'
                   (fDom := [DomainName; CacheEncode])
                   (fCod := (B * CacheEncode)%type));
            auto using encode_body_monotone.
          unfold Frame.monotonic_function; simpl;
            intros; eapply encode_body_monotone; assumption.
          simpl.
          destruct (string_dec (x3 ++ x6) ""); simpl.
          destruct x3; simpl in e; try discriminate.
          elimtype False; eapply NonEmpty_String_wordToNat; eauto.
          destruct (string_dec x6 ""); simpl in *;
            injections.
          { injection H5; intros; try subst data.
            destruct (string_dec x3 ""); simpl.
            subst x3; subst x6; simpl in *; congruence.
            injection H5; intros Eq_1 Eq_2; rewrite Eq_1, Eq_2 in *; clear Eq_1 Eq_2.
            computes_to_econstructor.
            apply (@PickComputes _ _ None); intros; try discriminate; eauto.
            simpl.
            computes_to_econstructor.
            apply (@PickComputes _ _ (x3, x6)); simpl; intuition eauto.
            subst x6; eauto.
            unfold ValidLabel.
            split.
            eauto.
            destruct x3; simpl.
            elimtype False; eapply NonEmpty_String_wordToNat; eauto.
            omega.
            rewrite H16, length_append; omega.
            computes_to_econstructor; simpl.
            unfold encode_nat_Spec;
              rewrite H9, natToWord_wordToNat; eauto.
            computes_to_econstructor; simpl; eauto.
            computes_to_econstructor; simpl; eauto.
          }
          { injection H5; intros; try subst data.
            destruct x3; simpl.
            elimtype False; eapply NonEmpty_String_wordToNat; eauto.
            computes_to_econstructor.
            apply (@PickComputes _ _ None); intros; try discriminate.
            simpl.
            computes_to_econstructor.
            apply (@PickComputes _ _ (String a x3, x6)); simpl; intuition eauto.
            unfold ValidLabel.
            split.
            eauto.
            simpl; omega.
            eapply (ValidLabel_split_char (String a x3)); simpl; eauto.
            computes_to_econstructor; simpl.
            unfold encode_nat_Spec.
            simpl in H9; rewrite H9, natToWord_wordToNat; eauto.
            computes_to_econstructor; simpl; eauto.
            computes_to_econstructor; simpl; eauto.
          }
          simpl.
          destruct x1; simpl in *; rewrite x_eq, x_eq', H11;
            intuition eauto.
          rewrite !transform_assoc; auto.
          destruct (string_dec x6 ""); injection H5; intros; subst x7;
            reflexivity.
          destruct (string_dec x6 ""); simpl in *; injection H5; intros; subst data.
          unfold ValidDomainName; split; intros.
          rewrite H16 in H9; generalize H9.
          rewrite !length_append; intros.
          generalize w.
          assert (le (String.length label) (wordToNat x0)) by omega.
          intros; etransitivity; eauto.
          eapply WordFacts.wordToNat_lt in w0; simpl in w0; omega.
          rewrite H16 in x3_OK.
          apply (index_correct3 _ (String.length pre)) in x3_OK.
          elimtype False;
            generalize x3_OK; clear.
          { induction pre; simpl.
            - unfold substring; destruct post; simpl; congruence.
            - destruct pre; simpl.
              unfold substring; destruct post; simpl; congruence.
              auto.
          }
          congruence.
          destruct x3; simpl.
          elimtype False; eapply NonEmpty_String_wordToNat; eauto.
          omega.
          eapply ValidDomainName_app'; eauto.
          unfold ValidLabel; split; eauto.
          destruct x3; simpl; try omega.
          elimtype False; eapply NonEmpty_String_wordToNat; eauto.
          eapply WordFacts.wordToNat_lt in w; simpl in w; omega.
          destruct (string_dec x6 ""); simpl in *; injection H5; intros;
            subst xenv'; subst data.
          erewrite peek_correct by eauto.
          destruct (peekD env') eqn: ?; simpl in *; eauto.
          apply add_correct_G.
          eauto.
          destruct (getD x8 p) eqn: Heqo; eauto.
          rewrite get_correct in Heqo by eauto.
          eapply InCacheFixpoint in H4; eauto; intuition.
          destruct (fun H => in_dec H p (getE xenv'' s)).
          apply pointerT_eq_dec .
          rewrite <- get_correct in i by eauto.
          eapply (cache_inv_add_ptr_OK P_OK) in Heqy ; eauto.
          eapply decode_word_add_ptr_OK with (env := env) (env' := env) in H2; eauto.
          eapply decode_string_add_ptr_OK with (env := env) in H3; eauto.
          unfold add_ptr_OK in *; simpl in *.
          congruence.
          eapply addPeek  with (n := 1) in Heqy;
              intuition eauto.
          apply decode_word_peek_distinct in H2.
          simpl in H17; rewrite H17 in H2.
          eapply decode_string_peek_distinct in H3; eauto.
          eapply addPeek with (n := wordToNat x0) in H2;
            intuition eauto.
          rewrite <- H3 in H2.
          erewrite <- peek_correct in H2; eauto.
          eapply (fun H => H14 _ H H2) in n1.
          rewrite !pointerT2Nat_Nat2pointerT in n1; eauto.
          omega.
          rewrite <- H3 in H4.
          erewrite <- peek_correct in H4; eauto.
          apply H16 in H4; intuition.
          apply decode_word_peek_distinct in H2.
          simpl in H4; rewrite H4 in H2.
          eapply decode_string_peek_distinct in H3; eauto.
          eapply addPeekNone with (n := wordToNat x0 * 8) in H2.
          rewrite <- H3 in H2.
          erewrite <- peek_correct in H2; eauto.
          intuition.
          erewrite peek_correct by eauto.
          destruct (peekD env') eqn: ?; simpl in *; eauto.
          apply add_correct_G.
          eauto.
          destruct (getD x8 p) eqn: Heqo; eauto.
          rewrite get_correct in Heqo by eauto.
          eapply InCacheFixpoint in H4; eauto; intuition.
          destruct (fun H => in_dec H p (getE xenv'' s)).
          apply pointerT_eq_dec .
          rewrite <- get_correct in i by eauto.
          eapply (cache_inv_add_ptr_OK P_OK) in Heqy ; eauto.
          eapply decode_word_add_ptr_OK with (env := env) (env' := env) in H2; eauto.
          eapply decode_string_add_ptr_OK with (env := env) in H3; eauto.
          unfold add_ptr_OK in *; simpl in *.
          congruence.
          eapply addPeek  with (n := 1) in Heqy;
              intuition eauto.
          apply decode_word_peek_distinct in H2.
          simpl in H17; rewrite H17 in H2.
          eapply decode_string_peek_distinct in H3; eauto.
          eapply addPeek with (n := wordToNat x0) in H2;
            intuition eauto.
          rewrite <- H3 in H2.
          erewrite <- peek_correct in H2; eauto.
          eapply (fun H => H14 _ H H2) in n2.
          rewrite !pointerT2Nat_Nat2pointerT in n2; eauto.
          omega.
          rewrite <- H3 in H4.
          erewrite <- peek_correct in H4; eauto.
          apply H16 in H4; intuition.
          apply decode_word_peek_distinct in H2.
          simpl in H4; rewrite H4 in H2.
          eapply decode_string_peek_distinct in H3; eauto.
          eapply addPeekNone with (n := wordToNat x0 * 8) in H2.
          rewrite <- H3 in H2.
          erewrite <- peek_correct in H2; eauto.
          intuition.
          apply lt_B_trans; eauto.
          assumption.
          assumption.
    }
    Grab Existential Variables.
    econstructor.
    auto.
    econstructor.
    assumption.
    assumption.
    econstructor.
  Qed.

End DomainName.
