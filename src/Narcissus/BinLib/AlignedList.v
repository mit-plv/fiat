Require Import
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.DecideableEnsembles
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
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedMonads
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant.

Require Import
        Bedrock.Word.

Section AlignedList.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Fixpoint align_decode_list {A}
           (A_decode_align : forall n,
               Vector.t (word 8) n
               -> CacheDecode
               -> option (A * {n : _ & Vector.t _ n}
                          * CacheDecode))
           (n : nat)
           {sz}
           (v : Vector.t (word 8) sz)
           (cd : CacheDecode)
    : option (list A *  {n : _ & Vector.t _ n} * CacheDecode) :=
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
            Vector.t (word 8) n
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
             (v : Vector.t (word 8) sz)
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
              -> {n : _ & Vector.t (word 8) n} * CacheFormat)
           (As : list A)
           (ce : CacheFormat)
    : {n : _ & Vector.t (word 8) n} * CacheFormat :=
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
           -> {n : _ & Vector.t (word 8) n} * CacheFormat)
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

  Lemma AlignedDecodeListM {A C : Set}
        (A_decode : DecodeM A ByteString)
        (A_decode_align : forall {m}, AlignedDecodeM A m)
        (n : nat)
    : forall (t : list A -> DecodeM C ByteString)
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

End AlignedList.
