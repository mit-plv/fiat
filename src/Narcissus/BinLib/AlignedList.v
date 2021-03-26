Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.DomainNameOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BaseFormats.

Require Import
        Bedrock.Word.

Section AlignedList.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Fixpoint align_decode_list {A}
           (A_decode_align : forall n,
               ByteBuffer.t n
               -> CacheDecode
               -> option (A * {n : _ & Vector.t _ n}
                          * CacheDecode))
           (n : nat)
           {sz}
           (v : ByteBuffer.t sz)
           (cd : CacheDecode)
    : option (list A * {n : _ & Vector.t _ n} * CacheDecode) :=
    match n with
    | 0 => Some (@nil _, existT _ _ v, cd)
    | S s' => `(x, b1, e1) <- A_decode_align sz v cd;
                `(xs, b2, e2) <- align_decode_list A_decode_align s' (projT2 b1) e1;
                Some ((x :: xs)%list, b2, e2)
    end.

  Lemma optimize_align_decode_list
        {A}
        (A_decode :
           ByteString
           -> CacheDecode
           -> option (A * ByteString * CacheDecode))
        (A_decode_align : forall n,
            ByteBuffer.t n
            -> CacheDecode
            -> option (A * {n : _ & Vector.t _ n}
                       * CacheDecode))
        (A_decode_OK :
           forall n (v : Vector.t _ n) cd,
             A_decode (build_aligned_ByteString v) cd =
             Ifopt A_decode_align n v cd as a Then
                                              Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                              Else
                                              None)
    : forall (n : nat)
             {sz}
             (v : ByteBuffer.t sz)
             (cd : CacheDecode),
      decode_list A_decode n (build_aligned_ByteString v) cd =
      Ifopt align_decode_list A_decode_align n v cd as a Then
                                                         Some (fst (fst a), build_aligned_ByteString (projT2 (snd (fst a))), snd a)
                                                         Else
                                                         None.
  Proof.
    induction n; simpl; intros; eauto.
    rewrite A_decode_OK.
    rewrite (If_Opt_Then_Else_DecodeBindOpt).
    destruct (A_decode_align sz v cd) as [ [ [? [? ?] ] ?]  | ]; simpl; eauto.
    rewrite IHn.
    rewrite (If_Opt_Then_Else_DecodeBindOpt).
    destruct (align_decode_list A_decode_align n t c)
      as [ [ [? [? ?] ] ?]  | ]; simpl; eauto.
  Qed.

  Fixpoint align_format_list {A}
           (A_format_align :
              A
              ->  CacheFormat
              -> {n : _ & ByteBuffer.t n} * CacheFormat)
           (As : list A)
           (ce : CacheFormat)
    : {n : _ & ByteBuffer.t n} * CacheFormat :=
    match As with
    | nil => (existT _ _ (Vector.nil _), ce)
    | a :: As' =>
      let (b, ce') := A_format_align a ce in
      let (b', ce'') := align_format_list A_format_align As' ce' in
      (existT _ _ (append (projT2 b) (projT2 b')), ce'')
    end.

  Lemma optimize_align_format_list
        {A}
        (A_OK : A -> Prop)
        (format_A : A -> CacheFormat -> Comp (ByteString * CacheFormat))
        (A_format_align :
           A
           ->  CacheFormat
           -> {n : _ & ByteBuffer.t n} * CacheFormat)
        (A_format_OK :
           forall a ce,
             A_OK a
             -> refine (format_A a ce)
                    (ret (let (v', ce') := A_format_align a ce in
                          (build_aligned_ByteString (projT2 v'), ce'))))
    : forall (As : list A)
             (ce : CacheFormat),
      (forall a, In a As -> A_OK a)
      -> refine (format_list format_A As ce)
             (let (v', ce') := (align_format_list A_format_align As ce) in
              ret (build_aligned_ByteString (projT2 v'), ce')).
  Proof.
    induction As; simpl; intros; simpl.
    - simpl.
      repeat f_equiv.
      eapply ByteString_f_equal.
      instantiate (1 := eq_refl _); reflexivity.
      instantiate (1 := eq_refl _); reflexivity.
    - unfold Bind2.
      rewrite A_format_OK; eauto; simplify with monad laws.
      rewrite IHAs.
      destruct (A_format_align a ce); simpl.
      destruct (align_format_list A_format_align As c);
        simplify with monad laws.
      simpl.
      rewrite <- build_aligned_ByteString_append.
      reflexivity.
      intuition.
  Qed.

  Lemma AlignedFormatListThenC {A}
        (A_OK : A -> Prop)
        format_A
        (encode_A : A -> CacheFormat -> {n : nat & t (word 8) n} * CacheFormat)
    : forall (l : list A) ce (c : _ -> Comp _)
             (v' : _ -> {n : nat & t (word 8) n})
             (ce' : _ -> CacheFormat),
      (forall (a : A) (ce : CacheFormat),
          A_OK a ->
          refine (format_A a ce) (ret (let (v', ce') := encode_A a ce in (build_aligned_ByteString (projT2 v'), ce'))))
      -> (forall v ce'',
             format_list format_A l ce ↝ (v, ce'') ->
             refine (c ce'') (ret (build_aligned_ByteString (projT2 (v' ce'')), ce' ce'')))
      -> (forall a : A, In a l -> A_OK a)
      -> refine (((format_list format_A l)
                    ThenC c) ce)
                (ret (let (v, ce'') := align_format_list encode_A l ce in
                      build_aligned_ByteString
                        (Vector.append (projT2 v) (projT2 (v' ce''))),
                      let (v, ce'') := align_format_list encode_A l ce in
                      ce' ce'')).
  Proof.
    intros.
    etransitivity.
    eapply AlignedFormatThenC.
    rewrite (optimize_align_format_list A_OK format_A encode_A); try eassumption.
    match goal with
      |- context [let (v, c) := ?z in ret (@?b v c)] =>
      rewrite (zeta_inside_ret z _)
    end.
    rewrite zeta_to_fst; simpl.
    instantiate (2 := fun ce => fst (_ ce)).
    instantiate (1 := fun ce => snd (_ ce)).
    simpl; reflexivity.
    intros; eapply H0; eauto.
    simpl.
    rewrite !zeta_to_fst; simpl; reflexivity.
  Qed.

  Fixpoint ListAlignedDecodeM {A} {m}
           (A_decode_align : forall {m}, AlignedDecodeM A m)
           (n : nat)
    : AlignedDecodeM (list A) m :=
    match n with
    | 0 => return (@nil A)
    | S s' => a <- A_decode_align;
              l <- ListAlignedDecodeM (@A_decode_align) s';
              return (a :: l)
    end%AlignedDecodeM%list.

  Lemma AlignedDecodeListM {A C : Type}
        (A_decode : DecodeM (A * _) ByteString)
        (A_decode_align : forall {m}, AlignedDecodeM A m)
        (n : nat)
    : forall (t : list A -> DecodeM (C * _) ByteString)
             (t' : list A -> forall {numBytes}, AlignedDecodeM C numBytes),
      (DecodeMEquivAlignedDecodeM A_decode (@A_decode_align))
      -> (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(l, bs, cd') <- decode_list A_decode n v cd;
                          t l bs cd')
           (fun numBytes => l <- ListAlignedDecodeM (@A_decode_align) n;
                            t' l)%AlignedDecodeM%list.
  Proof.
    induction n; simpl; intros; eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply ReturnAlignedDecodeM_LeftUnit;
                                                      reflexivity | reflexivity ].
    eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: set_evars; erewrite !DecodeBindOpt2_assoc; subst_evars; higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply BindAlignedDecodeM_assoc;
                                                      reflexivity | higher_order_reflexivity ].
    simpl.
    eapply Bind_DecodeMEquivAlignedDecodeM; intros.
    eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: set_evars; erewrite !DecodeBindOpt2_assoc; subst_evars; higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [apply BindAlignedDecodeM_assoc;
                                                      reflexivity | higher_order_reflexivity ].
    simpl.
    eapply IHn; eauto.
    intros.
    eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
    2: higher_order_reflexivity.
    2: apply AlignedDecodeMEquiv_sym; etransitivity; [eapply ReturnAlignedDecodeM_LeftUnit | higher_order_reflexivity].
    eapply H0.
  Qed.

  Lemma AlignedFormatListDoneC {A}
        (A_OK : A -> Prop)
        format_A
        (encode_An : A -> CacheFormat -> nat)
        (encode_A1 : forall a ce,  t (word 8) (encode_An a ce))
        (encode_A2 : A -> CacheFormat -> CacheFormat)
    : forall (l : list A) ce,
      (forall (a : A) (ce : CacheFormat),
          A_OK a
          -> refine (format_A a ce) (ret (build_aligned_ByteString (encode_A1 a ce), encode_A2 a ce)))
      -> (forall a : A, In a l -> A_OK a)
      -> refine (((format_list format_A l) DoneC) ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_list (fun a ce => (existT _ _ (encode_A1 a ce), encode_A2 a ce)) l ce))),
                      let (v, ce'') := align_format_list (fun a ce => (existT _ _ (encode_A1 a ce), encode_A2 a ce)) l ce in
                      ce'')).
  Proof.
    intros.
    etransitivity.
    eapply AlignedFormatDoneC.
    rewrite (optimize_align_format_list A_OK format_A (fun a ce => (existT _ _ (encode_A1 a ce), encode_A2 a ce))); try eassumption.
    match goal with
      |- context [let (v, c) := ?z in ret (@?b v c)] =>
      rewrite (zeta_inside_ret z _)
    end.
    rewrite zeta_to_fst; simpl.
    instantiate (2 := fun ce => fst (_ ce)).
    instantiate (1 := fun ce => snd (_ ce)).
    simpl; reflexivity.
    intros; rewrite zeta_to_fst; simpl; reflexivity.
  Qed.

  Fixpoint AlignedEncodeList' {A}
           (A_format_align : forall sz, AlignedEncodeM (S := A) sz)
           (sz : nat)
           v
           idx
           As
           env :=
      match As with
      | nil => if Coq.Init.Nat.ltb idx (S sz) then @ReturnAlignedEncodeM _ (list A) _ v idx nil env else None
      | a :: As' => Ifopt (A_format_align sz v idx a env) as a' Then
                                                                AlignedEncodeList' A_format_align sz (fst (fst a'))
                                                              (snd (fst a'))
                                                              As' (snd a')
                                                              Else None
    end.

  Definition AlignedEncodeList {A}
             (A_format_align : forall sz, AlignedEncodeM (S := A) sz)
    : forall sz, AlignedEncodeM (S := list A) sz :=
    AlignedEncodeList' A_format_align.

  Lemma CorrectAlignedEncoderForFormatList {A}
        format_A
        encode_A
        (encode_A_OK : CorrectAlignedEncoder format_A encode_A)
        (encode_A_OK' :
           forall (a : A) l (env : CacheFormat) (tenv' tenv'' : ByteString * CacheFormat),
            format_A a env ∋ tenv' ->
            format_list format_A l (snd tenv') ∋ tenv'' ->
            exists tenv3 tenv4 : _ * CacheFormat,
              projT1 encode_A_OK a env = Some tenv3
              /\ format_list format_A l (snd tenv3) ∋ tenv4)
    : CorrectAlignedEncoder (format_list format_A)
                               (@AlignedEncodeList A encode_A).
  Proof.
    unfold CorrectAlignedEncoder; intros.
    rename encode_A_OK into X.
    eexists ((fix AlignedEncodeList (As : list A) env :=
               match As with
               | nil => Some (mempty, env)
               | a :: As' => `(t1, env') <- projT1 X a env;
                             `(t2, env'') <- AlignedEncodeList As' env';
                             Some (mappend t1 t2, env'')
               end)); split; [ split | split ].
    - revert env; induction s; intros; simpl; eauto.
      + injections; reflexivity.
      + destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
        destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        unfold Bind2.
        rewrite (proj1 (a0 _ _)), refineEquiv_bind_unit; eauto.
        destruct ((fix AlignedEncodeList (As : list A) (env : CacheFormat) {struct As} :
                          option (ByteString * CacheFormat) :=
                          match As with
                          | [] => Some (ByteString_id, env)
                          | a :: As' =>
                              `(t1, env') <- encode_A' a env;
                              `(t2, env'') <- AlignedEncodeList As' env';
                              Some (ByteString_enqueue_ByteString t1 t2, env'')
                          end)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        rewrite IHs, refineEquiv_bind_unit; simpl; eauto.
        injections; reflexivity.
    - revert env; induction s; intros; simpl; eauto; try discriminate.
      destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
      destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate;
        unfold Bind2; intros ?; computes_to_inv.
      + destruct (encode_A_OK' _ _ _ _ _ H0 H0') as [ [? ?] [ [? ?] [? ?] ] ].
        rewrite H1 in Heqo; injections.
        destruct ((fix AlignedEncodeList (As : list A) (env : CacheFormat) {struct As} :
                     option (ByteString * CacheFormat) :=
                     match As with
                     | [] => Some (ByteString_id, env)
                     | a :: As' =>
                       `(t1, env') <- encode_A' a env;
                       `(t2, env'') <- AlignedEncodeList As' env';
                       Some (ByteString_enqueue_ByteString t1 t2, env'')
                     end) s c) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        eapply IHs; eauto.
      + eapply a0; eauto.
    - induction s; intros; simpl; eauto.
      + injections; reflexivity.
      + destruct X as [encode_A' [? [? ?] ] ]; simpl in *.
        destruct (encode_A' a env) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        destruct ((fix AlignedEncodeList (As : list A) (env : CacheFormat) {struct As} :
                          option (ByteString * CacheFormat) :=
                          match As with
                          | [] => Some (ByteString_id, env)
                          | a :: As' =>
                              `(t1, env') <- encode_A' a env;
                              `(t2, env'') <- AlignedEncodeList As' env';
                              Some (ByteString_enqueue_ByteString t1 t2, env'')
                          end)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
        injections.
        erewrite padding_ByteString_enqueue_ByteString, e, IHs; eauto.
    - unfold EncodeMEquivAlignedEncodeM; intros.
      generalize (le_refl (length s)); remember (length s) eqn: s_eq; rewrite s_eq at 1; clear s_eq.
      revert s env idx. induction n; intros ? ? ? le_s.
      + destruct s; simpl in le_s; try solve [inversion le_s].
        repeat apply conj; intros.
        * injections; simpl in v; pattern v; apply case0; simpl.
          setoid_rewrite (proj2 (PeanoNat.Nat.ltb_lt idx (S idx + m))); try Omega.omega.
          eexists _; split.
          revert v1; rewrite <- (plus_n_O idx); intro; reflexivity.
          pose proof mempty_left as H'; simpl in H'; rewrite H', build_aligned_ByteString_append;
            reflexivity.
        * injections; rewrite length_ByteString_ByteString_id in H0.
          unfold AlignedEncodeList; simpl.
          destruct (NPeano.Nat.ltb idx (S numBytes')) eqn: ?; eauto.
          apply PeanoNat.Nat.ltb_lt in Heqb; Omega.omega.
        * injections; simpl in H0; congruence.
        * discriminate.
      + destruct s; simpl in le_s; try solve [inversion le_s].
        * repeat apply conj; intros.
          -- injections; simpl in v; pattern v; apply case0; simpl.
             setoid_rewrite (proj2 (PeanoNat.Nat.ltb_lt idx (S idx + m))); try Omega.omega.
             eexists _; split.
             revert v1; rewrite <- (plus_n_O idx); intro; reflexivity.
             pose proof mempty_left as H'; simpl in H'; rewrite H', build_aligned_ByteString_append;
               reflexivity.
          -- injections; rewrite length_ByteString_ByteString_id in H0.
             unfold AlignedEncodeList; simpl.
             destruct (NPeano.Nat.ltb idx (S numBytes')) eqn: ?; eauto.
             apply PeanoNat.Nat.ltb_lt in Heqb; Omega.omega.
          -- injections; simpl in H0; congruence.
          -- discriminate.
        * assert ((forall (s : A * {As : list A & le (length As) n} ) (env : CacheFormat) (t : ByteString) (env' : CacheFormat),
                      (projT1 X ∘ fst) s env = Some (t, env') -> padding t = 0)) as H'.
          { destruct X; clear IHn; simpl in *; intuition eauto. }
          assert (EncodeMEquivAlignedEncodeM (projT1 X ∘ fst)
                                             (fun (sz : nat) (t : ByteBuffer.t sz) (idx : nat)
                                                  (s : A * {As : list A & le (length As) n})
                                                  (env : CacheFormat) => encode_A sz t idx (fst s) env)) as H''.
          { destruct X; clear IHn; simpl in *; intuition eauto.
            unfold EncodeMEquivAlignedEncodeM; intros ? [? ?] ?; unfold Basics.compose; simpl.
            apply H2; eauto. }
          assert (EncodeMEquivAlignedEncodeM (S := A * {As : list A & le (length As) n})
                    ((fix AlignedEncodeList (As : list A)
                          (env : CacheFormat) {struct As} : option (ByteString * CacheFormat) :=
                        match As with
                        | [] => Some (mempty, env)
                        | a :: As' => `(t1, env') <- projT1 X a env;
                                      `(t2, env'') <- AlignedEncodeList As' env';
                                      Some (mappend t1 t2, env'')
                        end) ∘ (@projT1 _ _) ∘ snd )
                    (fun (sz : nat) (t : ByteBuffer.t sz) (idx : nat)
                         (s : A * {As : list A & le (length As) n}) (env : CacheFormat) =>
                       AlignedEncodeList encode_A sz t idx (projT1 (snd s)) env)) as H'''.
          { unfold EncodeMEquivAlignedEncodeM; intros ? [? [? ?] ] ?; simpl; eauto. }
          apply le_S_n in le_s.
        pose proof (Append_EncodeMEquivAlignedEncodeM _
                                                      _
                                                      _
                                                      _
                                                      H' H'' H''' env (a, existT _ s le_s) idx); clear H' H'' H'''.
        intuition.
  Qed.
End AlignedList.
