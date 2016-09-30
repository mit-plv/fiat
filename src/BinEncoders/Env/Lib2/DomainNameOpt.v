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
                                          (domain = (fst labeldomain') ++ String "." (snd labeldomain') \/ labeldomain' = (domain, ""))
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
                                     (domain = (fst labeldomain') ++ String "." (snd labeldomain') \/ labeldomain' = (domain, ""))
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
        eapply (ValidLabel_OK_split label _ (x ++ String "." post)) in H2;
          subst; eauto.
        pose proof (proj2 H1 _ _ H2); repeat split;
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
              Ifopt (index 0 "." label) as _ Then None
              Else (`(domain, b4, e3) <- rec (proj1_sig b3) (lt_B_trans _ _ _) env';
              If (string_dec domain "") Then
                 Some (label, b4, addD e3 (label, peekD cd))
                 Else Some (label ++ (String "." domain), b4,
                            addD e3 (label ++ (String "." domain), peekD cd))
             )) end)
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
                    Ifopt (index 0 "." label) as _ Then None
                    Else (
                   `(domain, b4, e3) <- f (` b3) (lt_B_trans x b1 b3) env'0;
                   If (string_dec domain "") Then
                      Some (label, b4, addD e3 (label, peekD cd))
                   Else Some (label ++ (String "." domain), b4,
                            addD e3 (label ++ (String "." domain), peekD cd)))%string
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
                     Ifopt (index 0 "." label) as _ Then None
                     Else (
                     `(domain, b4, e3) <- g (` b3) (lt_B_trans x b1 b3) env'0;
                       If (string_dec domain "") Then
                          Some (label, b4, addD e3 (label, peekD cd))
                       Else Some (label ++ (String "." domain), b4,
                                  addD e3 (label ++ (String "." domain), peekD cd)))%string
               end Else None)).
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
    Else (Ifopt getE env0 domain as position
          Then b <- {_ : bool | True};
               If b
               Then `(ptr1b, env') <- encode_word_Spec (fst position) env0;
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
                       addE env'1 (domain, peekE env0)))
          Else (`(label, domain') <- {labeldomain' :
                                        string * string |
                                      (domain =
                                           (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                           labeldomain' = (domain, ""%string)) /\
                                     ValidLabel (fst labeldomain') /\
                                     (forall label' post' : string,
                                      domain = (label' ++ post')%string ->
                                      ValidLabel label' ->
                                      (String.length label' <= String.length (fst labeldomain'))%nat)};
                `(lenb, env') <- encode_nat_Spec 8 (String.length label) env0;
                `(labelb, env'0) <- encode_string_Spec label env';
                `(domainb, env'1) <- rec domain' env'0;
                ret
                  (transform (transform lenb labelb) domainb, addE env'1 (domain, peekE env0)))))
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
                       addE env'1 (domain, peekE env0)))
          Else (`(label, domain') <- {labeldomain' :
                                        string * string |
                                      (domain =
                                           (fst labeldomain' ++ String "." (snd labeldomain'))%string \/
                                           labeldomain' = (domain, ""%string)) /\
                                        ValidLabel (fst labeldomain') /\
                                     (forall label' post' : string,
                                      domain = (label' ++ post')%string ->
                                      ValidLabel label' ->
                                      (String.length label' <= String.length (fst labeldomain'))%nat)};
                `(lenb, env') <- encode_nat_Spec 8 (String.length label) env0;
                `(labelb, env'0) <- encode_string_Spec label env';
                `(domainb, env'1) <- rec' domain' env'0;
                ret
                  (transform (transform lenb labelb) domainb, addE env'1 (domain, peekE env0))))).
  Proof.
    simpl; intros; unfold Bind2.
    apply General.refine_if; intros; rewrite H0; simpl.
    reflexivity.
    apply SetoidMorphisms.refine_If_Opt_Then_Else_Proper.
    * intro; f_equiv; intro.
      apply General.refine_if; intros H5; rewrite H5; simpl.
      reflexivity.
      unfold Bind2; f_equiv; eauto.
      intro; setoid_rewrite H; reflexivity.
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

  (* Commenting out until I can patch up proof. *)
  Theorem DomainName_decode_correct
          (P_OK : forall (b : nat) (cd : CacheDecode),
              cache_inv cd
              -> cache_inv (addD cd b))
          (Get_cache_inv_OK
           : cache_inv_Property cache_inv
                                (fun P => forall ce l p1 p2,
                                     (@getE _ DomainName _ _ ce l = Some (p1, p2)
                                      -> wlt (natToWord 8 191) p1)))
    :
    encode_decode_correct_f
      cache transformer
      (fun domain => ValidDomainName domain)
      (fun _ _ => True)
      encode_DomainName_Spec decode_DomainName cache_inv.
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
                  * apply Get_cache_inv_OK in GetPtr; contradiction.
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
                generalize l_eq; intros [l_eq' | l_eq'].
                destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H I Penc'') as [xenv4 [? xenv_eqv] ].
                pose proof ((proj1 Valid_data) ""%string label1 _ l_eq' label1_OK).
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
                  pose proof ((proj1 Valid_data) ""%string label1 _ (eq_refl _) label1_OK) as w';
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
                    omega.
                    apply Nomega.Nlt_in.
                    simpl. unfold BinPos.Pos.to_nat; simpl.
                    omega.
                    simpl; omega.
                + erewrite peek_correct, l_eq'.
                  apply add_correct; eauto.
                  eauto.
                + subst; eauto using ValidDomainName_app.
                + subst; eauto using chomp_label_length.
                + eassumption.
                + injections.
                  destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H I Penc'') as [xenv4 [? xenv_eqv] ].
                  pose proof (proj1 Valid_data ""%string l ""%string (append_EmptyString_r _) label1_OK).
                simpl; omega.
                destruct (fun H => proj1 (String_decode_correct (P := fun _ => True) (fun _ _ _ => I) (String.length l)) _ _ _ _ _ (transform b3 ext0) xenv_eqv H I Penc''') as [xenv6 [? xenv6_eqv] ]; eauto.
                eapply IHn in Penc''''.
                destruct Penc'''' as [xenv7 [? ?] ].
                eexists; split.
                rewrite Init.Wf.Fix_eq; auto using decode_body_monotone; simpl.
                  * match goal with
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
                    try (apply WordFacts.wordToNat_lt in w; simpl in w; omega).
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
                  * erewrite peek_correct.
                    apply add_correct; eauto.
                    eauto.
                  * unfold ValidDomainName; split; intros.
                    destruct pre; simpl in *; try discriminate.
                    destruct label; simpl in *; try discriminate.
                    omega.
                    destruct pre; simpl in *; try discriminate.
                  * simpl; omega.
                  * eassumption.
            }
            { (* No pointer available *)
              unfold Bind2 in Penc; computes_to_inv.
              destruct Penc as [l_eq [label1_OK label1_OK'] ].
              destruct v as [label1 label2]; destruct v0 as [b' xenv'''];
                  destruct v1 as [b'' xenv'''']; destruct v2 as [b3 xenv5];
                    simpl in *; injections.
                generalize l_eq; intros [l_eq' | l_eq'].
                destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H I Penc') as [xenv4 [? xenv_eqv] ].
                pose proof (proj1 Valid_data ""%string label1 _ l_eq' label1_OK).
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
                  pose proof (proj1 Valid_data ""%string label1 _ (eq_refl _) label1_OK) as w';
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
                    omega.
                    apply Nomega.Nlt_in.
                    simpl. unfold BinPos.Pos.to_nat; simpl.
                    omega.
                    simpl; omega.
                + erewrite peek_correct, l_eq'.
                  apply add_correct; eauto.
                  eauto.
                + subst; eauto using ValidDomainName_app.
                + subst; eauto using chomp_label_length.
                + eassumption.
                + injections.
                  destruct (fun H => proj1 (Nat_decode_correct (P := fun _ => True) 8 (fun _ _ _ => I)) _ _ _ _ _ (transform b'' (transform b3 ext0)) Eeq H I Penc') as [xenv4 [? xenv_eqv] ].
                  pose proof (proj1 Valid_data ""%string l ""%string (append_EmptyString_r _) label1_OK).
                simpl; omega.
                destruct (fun H => proj1 (String_decode_correct (P := fun _ => True) (fun _ _ _ => I) (String.length l)) _ _ _ _ _ (transform b3 ext0) xenv_eqv H I Penc'') as [xenv6 [? xenv6_eqv] ]; eauto.
                eapply IHn in Penc'''.
                destruct Penc''' as [xenv7 [? ?] ].
                eexists; split.
                rewrite Init.Wf.Fix_eq; auto using decode_body_monotone; simpl.
                  * match goal with
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
                    try (apply WordFacts.wordToNat_lt in w; simpl in w; omega).
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
                    assert (WO~0~1~0~0~0~0~0~0 < x \/ WO~0~1~0~0~0~0~0~0 = x)
                      by (destruct (weq WO~0~1~0~0~0~0~0~0 x); eauto using le_neq_lt).
                    destruct H0; eauto.
                    generalize (WordFacts.wordToNat_lt H0); simpl; omega.
                    generalize (f_equal (@wordToNat 8) H0); simpl; omega.
                  * erewrite peek_correct.
                    apply add_correct; eauto.
                    eauto.
                  * unfold ValidDomainName; split; intros.
                    destruct pre; simpl in *; try discriminate.
                    destruct label; simpl in *; try discriminate.
                    omega.
                    destruct pre; simpl in *; try discriminate.
                  * simpl; omega.
                  * eassumption.
            }
        }
      }
    }
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
        destruct (getD env' (x0, x3)) eqn:getD_eq ; try discriminate.
        destruct s; try discriminate; injections.
        eapply Decode_w_Measure_le_eq' in H2.
        eapply Decode_w_Measure_le_eq' in H3.
        destruct (proj2 (Word_decode_correct P_OK) _ _ _ _ _ _ H0 H1 H2) as
            [? [b' [xenv [enc_x0 [x_eq [_ xenv_eqv] ] ] ] ] ].
        destruct (proj2 (Word_decode_correct P_OK) _ _ _ _ _ _ xenv_eqv H4 H3) as
            [? [b'' [xenv' [enc_x0' [x_eq' [_ xenv_eqv'] ] ] ] ] ].
        split; eauto; eexists _, _; split; eauto.
        apply (unroll_LeastFixedPoint'
                 (fDom := [DomainName; CacheEncode])
                 (fCod := (B * CacheEncode)%type));
          auto using encode_body_monotone.
        eapply get_correct in getD_eq.
        rewrite getD_eq; simpl.
        computes_to_econstructor.
        apply (@PickComputes _ _ true); eauto.
        simpl; computes_to_econstructor; eauto.
        simpl; computes_to_econstructor; eauto.
        eauto.
        intuition eauto.
        rewrite x_eq' in x_eq.
        simpl in *; rewrite <- transform_assoc; assumption.
        eapply cacheGet_OK; [ | eassumption ].
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
          destruct (proj2 (Word_decode_correct P_OK) _ _ _ _ _ _ H0 H1 H2) as
              [? [b' [xenv [enc_x0 [x_eq [_ xenv_eqv] ] ] ] ] ]; split; eauto.
          eexists _, _; split; eauto.
          apply (unroll_LeastFixedPoint'
                   (fDom := [DomainName; CacheEncode])
                   (fCod := (B * CacheEncode)%type));
            auto using encode_body_monotone.
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
          destruct (proj2 (Word_decode_correct P_OK) _ _ _ _ _ _ H0 H1 H2) as
              [? [b' [xenv [enc_x0 [x_eq [? xenv_eqv] ] ] ] ] ]; eauto.
          destruct (fun H  => proj2 (String_decode_correct
                                       (P := cache_inv)
                                       P_OK (wordToNat x0))
                                    _ _ _ _ _ _ xenv_eqv H H3) as
              [? [b'' [xenv'' [enc_x0' [x_eq' [? xenv_eqv'] ] ] ] ] ]; eauto.
          eapply H in H4; eauto.
          intuition.
          destruct H11 as [bin' [xenv0 [? [? [? ? ] ] ] ] ].
          destruct (string_dec x6 ""); simpl in *;
            injections.
          { injection H5; intros; rewrite H14.
            eapply cacheAdd_OK; eauto.
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
          }
          { injection H5; intros; rewrite H14.
            eapply cacheAdd_OK; eauto.
            split.
            eapply ValidDomainName_app'; eauto.
            unfold ValidLabel; split; eauto.
            destruct x3; simpl; try omega.
            elimtype False; eapply NonEmpty_String_wordToNat; eauto.
            eapply WordFacts.wordToNat_lt in w; simpl in w; omega.
            destruct x3; simpl; omega.
          }
          destruct H11 as [bin' [xenv0 [? [? [? ? ] ] ] ] ].
          eexists _, _; split; eauto.
          apply (unroll_LeastFixedPoint'
                   (fDom := [DomainName; CacheEncode])
                   (fCod := (B * CacheEncode)%type));
            auto using encode_body_monotone.
          destruct (string_dec (x3 ++ x6) ""); simpl.
          destruct x3; simpl in e; try discriminate.
          elimtype False; eapply NonEmpty_String_wordToNat; eauto.
          destruct (string_dec x6 ""); simpl in *;
            injections.
          { injection H5; intros; try subst data.
            destruct (string_dec x3 ""); simpl.
            subst x3; subst x6; simpl in *; congruence.
            destruct (@getE _ DomainName _ _ env x3)
              as [ [ptr1 ptr2] | ] eqn:GetPtr; simpl.
            - computes_to_econstructor.
              apply (@PickComputes _ _ false); eauto.
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
            - simpl; computes_to_econstructor.
              apply (@PickComputes _ _ (x3, x6)); simpl; intuition eauto.
              subst x6; eauto.
              unfold ValidLabel.
              split; eauto.
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
            destruct (@getE _ DomainName _ _ env (String a (x3 ++ String "." x6))%string)
              as [ [ptr1 ptr2] | ] eqn:GetPtr; simpl.
            - computes_to_econstructor.
              apply (@PickComputes _ _ false); eauto.
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
            - simpl; computes_to_econstructor.
              apply (@PickComputes _ _ (String a x3, x6)); simpl; intuition eauto.
              unfold ValidLabel.
              split; eauto.
              simpl; omega.
              eapply (ValidLabel_split_char (String a x3)); simpl; eauto.
              computes_to_econstructor; simpl.
              unfold encode_nat_Spec;
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
            erewrite peek_correct.
            apply add_correct.
            eauto.
            eauto.
            erewrite peek_correct.
            apply add_correct.
            eauto.
            eauto.
            apply lt_B_trans; eauto.
            assumption.
            assumption.
    }
  Qed.

  Print Assumptions DomainName_decode_correct.

End DomainName.
