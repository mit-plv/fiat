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
  Definition pointerT := (word 8 * word 8)%type.

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
             (`(ptr1b, env') <- encode_word_Spec (fst position) env;
              `(ptr2b, env') <- encode_word_Spec (snd position) env';
              ret (transform ptr1b ptr2b, env'))
             Else (`(label, domain') <- { labeldomain' |
                                          domain = (fst labeldomain') ++ (snd labeldomain')
                                          /\ ValidLabel (fst labeldomain')
                                          /\ (forall label' post',
                                                 domain = label' ++ post'
                                                 -> ValidLabel label'
                                                 -> String.length label' <= String.length (fst labeldomain'))}%string%nat;
                     `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
                     `(labelb, env') <- encode_string_Spec label env';
                     `(domainb, env') <- encode_DomainName_Spec domain' env';
                     ret (transform (transform lenb labelb) domainb, addE env' (domain, peekE env)))
             Else
             (`(label, domain') <- { labeldomain' |
                                          domain = (fst labeldomain') ++ (snd labeldomain')
                                          /\ ValidLabel (fst labeldomain')
                                          /\ (forall label' post',
                                                 domain = label' ++ post'
                                                 -> ValidLabel label'
                                                 -> String.length label' <= String.length (fst labeldomain'))}%string%nat;
                     `(lenb, env') <- encode_nat_Spec 8 (String.length label) env;
                     `(labelb, env') <- encode_string_Spec label env';
                     `(domainb, env') <- encode_DomainName_Spec domain' env';
                     ret (transform (transform lenb labelb) domainb, addE env' (domain, peekE env))))) domain env.

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
      ValidDomainName (label ++ subdomain)
      -> ValidDomainName subdomain.
  Proof.
    unfold ValidDomainName; intros.
    eapply H0; try eassumption.
    rewrite H1.
    rewrite append_assoc.
    reflexivity.
  Qed.

  Lemma chomp_label_length
    : forall n label subdomain,
      (String.length (label ++ subdomain) <= S n)%nat
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
           If (wlt_dec (natToWord 8 191) labelheader) (* It's a pointer! *)
           Then (`(ps, b2, env') <- Decode_w_Measure_le (decode_word (sz := 8)) (proj1_sig b1) env' decode_word_le;
               match getD cd (labelheader, ps) with
                 | Some EmptyString => None (* bogus *)
                 | Some domain => Some (domain, proj1_sig b2, env')
                 | None => None (* bogus *)
                 end)
           Else (If (wlt_dec labelheader (natToWord 8 64)) Then (* It's a length octet *)
         (match (weq labelheader (wzero 8)) with (* It's the terminal character. *)
              | left _ => Some (EmptyString, proj1_sig b1, env')
              | right n =>
             (`(label, b3, env') <- Decode_w_Measure_lt (decode_string (wordToNat labelheader))
               (proj1_sig b1) env' (decode_string_lt _ (n_eq_0_lt _ n));
              `(domain, b4, e3) <- rec (proj1_sig b3) (lt_B_trans _ _ _) env';
              Some (label ++ domain, b4, addD e3 (label ++ domain, peekD cd))) end)
         Else None))%string b env);
    try exact decode_word_le;
      try exact decode_word_lt.
  Defined.

  Lemma decode_body_monotone
    : forall (x : B)
     (f g : forall y : B, lt_B y x -> CacheDecode -> option (DomainName * B * CacheDecode)),
   (forall (y : B) (p : lt_B y x), f y p = g y p) ->
   (fun cd : CacheDecode =>
    `(labelheader, b1, env') <- Decode_w_Measure_le decode_word x cd decode_word_le;
    If wlt_dec WO~1~0~1~1~1~1~1~1 labelheader
    Then `(ps, b2, env'0) <- Decode_w_Measure_le decode_word (` b1) env' decode_word_le;
         match getD cd (labelheader, ps) with
         | Some ""%string => None
         | Some (String _ _ as domain) => Some (domain, ` b2, env'0)
         | None => None
         end
    Else (If wlt_dec labelheader WO~0~1~0~0~0~0~0~0
          Then match weq labelheader (wzero 8) with
               | in_left => Some (""%string, ` b1, env')
               | right n =>
                   `(label, b3, env'0) <- Decode_w_Measure_lt
                                            (decode_string (wordToNat labelheader)) 
                                            (` b1) env'
                                            (decode_string_lt 
                                               (wordToNat labelheader)
                                               (n_eq_0_lt labelheader n));
                   `(domain, b4, e3) <- f (` b3) (lt_B_trans x b1 b3) env'0;
                   Some
                     ((label ++ domain)%string, b4,
                     addD e3 ((label ++ domain)%string, peekD cd))
               end Else None)) =
   (fun cd : CacheDecode =>
    `(labelheader, b1, env') <- Decode_w_Measure_le decode_word x cd decode_word_le;
    If wlt_dec WO~1~0~1~1~1~1~1~1 labelheader
    Then `(ps, b2, env'0) <- Decode_w_Measure_le decode_word (` b1) env' decode_word_le;
         match getD cd (labelheader, ps) with
         | Some ""%string => None
         | Some (String _ _ as domain) => Some (domain, ` b2, env'0)
         | None => None
         end
    Else (If wlt_dec labelheader WO~0~1~0~0~0~0~0~0
          Then match weq labelheader (wzero 8) with
               | in_left => Some (""%string, ` b1, env')
               | right n =>
                   `(label, b3, env'0) <- Decode_w_Measure_lt
                                            (decode_string (wordToNat labelheader)) 
                                            (` b1) env'
                                            (decode_string_lt 
                                               (wordToNat labelheader)
                                               (n_eq_0_lt labelheader n));
                   `(domain, b4, e3) <- g (` b3) (lt_B_trans x b1 b3) env'0;
                   Some
                     ((label ++ domain)%string, b4,
                     addD e3 ((label ++ domain)%string, peekD cd))
               end Else None)).
  Proof.
    intros; apply functional_extensionality; intros.
    repeat (f_equal; apply functional_extensionality; intros).
    destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x1); simpl.
    repeat (f_equal; apply functional_extensionality; intros).
    destruct (wlt_dec x1 WO~0~1~0~0~0~0~0~0); simpl.
    destruct (weq x1 (wzero 8)).
    reflexivity.
    repeat (f_equal; apply functional_extensionality; intros);
      rewrite H; reflexivity.
    reflexivity.
  Qed.
  
  Lemma encode_body_monotone
    : forall rec rec' : funType [DomainName; CacheEncode] (B * CacheEncode),
   refineFun rec rec' ->
   refineFun (fDom := [DomainName; CacheEncode])
     (fun (domain : DomainName) (env0 : CacheEncode) =>
      If string_dec domain "" Then encode_ascii_Spec terminal_char env0
      Else (Ifopt getE env0 domain as position
            Then b <- {_ : bool | True};
                 If b
                 Then `(ptr1b, env') <- encode_word_Spec (fst position) env0;
                      `(ptr2b, env'0) <- encode_word_Spec (snd position) env';
                      ret (transform ptr1b ptr2b, env'0)
                 Else (`(label, domain') <- {labeldomain' :
                                            string * string |
                                            domain =
                                            (fst labeldomain' ++ snd labeldomain')%string /\
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
                         addE env'1 (domain, peekE env0)))
            Else (`(label, domain') <- {labeldomain' :
                                       string * string |
                                       domain = (fst labeldomain' ++ snd labeldomain')%string /\
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
                    addE env'1 (domain, peekE env0)))))
     (fun (domain : DomainName) (env0 : CacheEncode) =>
      If string_dec domain "" Then encode_ascii_Spec terminal_char env0
      Else (Ifopt getE env0 domain as position
            Then b <- {_ : bool | True};
                 If b
                 Then `(ptr1b, env') <- encode_word_Spec (fst position) env0;
                      `(ptr2b, env'0) <- encode_word_Spec (snd position) env';
                      ret (transform ptr1b ptr2b, env'0)
                 Else (`(label, domain') <- {labeldomain' :
                                            string * string |
                                            domain =
                                            (fst labeldomain' ++ snd labeldomain')%string /\
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
                         addE env'1 (domain, peekE env0)))
            Else (`(label, domain') <- {labeldomain' :
                                       string * string |
                                       domain = (fst labeldomain' ++ snd labeldomain')%string /\
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
                    addE env'1 (domain, peekE env0))))).
  Proof.
    simpl; intros; unfold Bind2.
    apply General.refine_if; intros; rewrite H0; simpl.
    reflexivity.
    apply SetoidMorphisms.refine_If_Opt_Then_Else_Proper.
    * intro; f_equiv; intro.
      apply General.refine_if; intros H5; rewrite H5; simpl;
        unfold Bind2; f_equiv; intro.
      setoid_rewrite H; reflexivity.
    * f_equiv; intro.
      unfold Bind2; f_equiv; intro.
      setoid_rewrite H; reflexivity.
  Qed.

  (* Commenting out until I can patch up proof. *)
  Theorem DomainName_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall (b : nat) cd, P cd -> P (addD cd b)))
          (Get_P_OK
           : cache_inv_Property P
                                (fun P => forall ce l p1 p2,
                                     (@getE _ DomainName _ _ ce l = Some (p1, p2)
                                      -> wlt (natToWord 8 191) p1)))
    :
    encode_decode_correct_f
      cache transformer
      (fun domain => ValidDomainName domain)
      (fun _ _ => True)
      encode_DomainName_Spec decode_DomainName P.
  Proof.
    unfold encode_decode_correct_f; split.
    { intros env xenv xenv' l l' ext Eeq Valid_data
             Ppred_rest Penc.
      unfold decode_DomainName in *; simpl in *.
      unfold encode_DomainName_Spec in Penc.
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
         destruct (proj1 (Ascii_decode_correct P_OK)
                        _ _ _ _ _ ext0 Eeq I I Penc) as [? [? ?] ].
        apply DecodeBindOpt2_inv in H0;
          destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
        eexists; split.
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
      }
      { apply (unroll_LeastFixedPoint (fDom := [DomainName; CacheEncode]) (fCod := (B * CacheEncode))) in Penc; auto using encode_body_monotone.
        { destruct (string_dec l ""); simpl in Penc.
          (* Base case for domain name. *)
          - destruct (proj1 (Ascii_decode_correct P_OK)
                            _ _ _ _ _ ext0 Eeq I I Penc) as [? [? ?] ].
            apply DecodeBindOpt2_inv in H0;
              destruct H0 as [? [? [? [? ?] ] ] ]; injections; subst.
            eexists; split.
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
          - destruct (@getE _ DomainName _ _ env l) as [ [ptr1 ptr2] | ] eqn:GetPtr;
              simpl in Penc; computes_to_inv.
            { (* pointer found *)
              destruct v; simpl in Penc'; unfold Bind2 in Penc'; computes_to_inv.
              - (* Encoder chose to use compression. *)
                destruct v as [b xenv'']; destruct v0 as [b' xenv'''];
                  simpl in *; injections.
                unfold encode_word_Spec in Penc', Penc'';
                  computes_to_inv; subst; simpl in *; injections.
                eexists; split.
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
                  destruct (wlt_dec WO~1~0~1~1~1~1~1~1 ptr1); simpl.
                  * match goal with
                      |- context [Decode_w_Measure_le ?x ?y ?z ?m] =>
                      pose proof (Decode_w_Measure_le_eq x y z m)
                    end.
                    simpl in H0;
                      unfold decode_word at 1 in H0;
                      rewrite <- transformer_dequeue_word_eq_decode_word',
                      transformer_dequeue_encode_word' in H0;
                      simpl in H0;
                      destruct (H0 _ _ _ (eq_refl _)) as [? H'']; clear H0;
                        rewrite H''; clear H''; simpl.
                    eapply get_correct in GetPtr; eauto;
                      unfold DomainName, pointerT in *; rewrite GetPtr.
                    destruct l; try congruence.
                    reflexivity.
                  * apply Get_P_OK in GetPtr; contradiction.
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
              - (* Encoder chose not to compress *)
                destruct Penc' as [l_eq [label1_OK label1_OK'] ].
                destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
                  destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
                    simpl in *; injections.
                destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H I Penc'') as [xenv4 [? xenv_eqv] ].
                pose proof (Valid_data ""%string label1 label2 (eq_refl _) label1_OK).
                simpl; omega.
                destruct (fun H => proj1 (String_decode_correct (P := fun _ => True) (fun _ _ _ => I) (String.length label1)) _ _ _ _ _ (transform b3 ext0) xenv_eqv H I Penc''') as [xenv6 [? xenv6_eqv] ]; eauto.
                eapply IHn in Penc''''.
                destruct Penc'''' as [xenv7 [? ?] ].
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
                  pose proof (Valid_data ""%string label1 label2 (eq_refl _) label1_OK) as w';
                    rewrite H8 in w'.
                  destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x); simpl;
                    try (apply WordFacts.wordToNat_lt in w; simpl in w; omega).
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
                    rewrite H5; simpl; rewrite H2; reflexivity.
                  * destruct n2.
                    rewrite <- natToWord_wordToNat;
                      rewrite <- (natToWord_wordToNat x).
                    apply WordFacts.natToWord_wlt.
                    simpl.
                    apply Nomega.Nlt_in.
                    rewrite Nnat.Nat2N.id; etransitivity; eauto.
                    simpl. unfold BinPos.Pos.to_nat; simpl.
                    omega.
                    apply Nomega.Nlt_in.
                    simpl. unfold BinPos.Pos.to_nat; simpl.
                    omega.
                    simpl; omega.
                + erewrite peek_correct.
                  apply add_correct; eauto.
                  eauto.
                + eauto using ValidDomainName_app.
                + eauto using chomp_label_length.
                + eassumption.
            }
            { (* No pointer available *)
              unfold Bind2 in Penc; computes_to_inv.
              destruct Penc as [l_eq [label1_OK label1_OK'] ].
              destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
                destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
                  simpl in *; injections.
              destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H I Penc') as [xenv4 [? xenv_eqv] ].
              pose proof (Valid_data ""%string label1 label2 (eq_refl _) label1_OK).
              simpl; omega.
              destruct (fun H => proj1 (String_decode_correct (P := fun _ => True) (fun _ _ _ => I) (String.length label1)) _ _ _ _ _ (transform b3 ext0) xenv_eqv H I Penc'') as [xenv6 [? xenv6_eqv] ]; eauto.
              eapply IHn in Penc'''.
              destruct Penc''' as [xenv7 [? ?] ].
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
                pose proof (Valid_data ""%string label1 label2 (eq_refl _) label1_OK) as w';
                  rewrite H8 in w'.
                destruct (wlt_dec WO~1~0~1~1~1~1~1~1 x); simpl;
                  try (apply WordFacts.wordToNat_lt in w; simpl in w; omega).
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
                  rewrite H5; simpl; rewrite H2; reflexivity.
                * destruct n2.
                  rewrite <- natToWord_wordToNat;
                    rewrite <- (natToWord_wordToNat x).
                  apply WordFacts.natToWord_wlt.
                  simpl.
                  apply Nomega.Nlt_in.
                  rewrite Nnat.Nat2N.id; etransitivity; eauto.
                  simpl. unfold BinPos.Pos.to_nat; simpl.
                  omega.
                  apply Nomega.Nlt_in.
                  simpl. unfold BinPos.Pos.to_nat; simpl.
                  omega.
                  simpl; omega.
              + erewrite peek_correct.
                apply add_correct; eauto.
                eauto.
              + eauto using ValidDomainName_app.
              + eauto using chomp_label_length.
              + eassumption.
            }
        }
      }
    }
    unfold decode_DomainName, encode_DomainName_Spec; 
      intros env env' xenv' data bin;
      revert env env' xenv' data.
      eapply (@well_founded_induction _ _ well_founded_lt_b) with
      (a := bin); intros.
      rewrite Coq.Init.Wf.Fix_eq in H2; auto using decode_body_monotone; simpl.

      
      (*{ unfold decode_list_step, encode_list_step_Spec.
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
  Admitted.
End DomainName.
