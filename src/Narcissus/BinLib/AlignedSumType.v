Require Import
        Coq.Strings.String
        Coq.Arith.Mult
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.i2list
        Fiat.Common.DecideableEnsembles
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad.

Require Import
        Bedrock.Word.

Section AlignedSumType.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Definition align_format_sumtype
             {m : nat}
             {types : t Type m}
             (align_encoders_n :
                ilist2.ilist2 (B := fun T : Type => T -> CacheFormat -> nat) types)
             (align_encoders_v :
                i2list (B := fun T : Type => T -> CacheFormat -> nat)
                       (fun (T : Type) (n : _) => forall t ce, Vector.t (word 8) (n t ce)) align_encoders_n)
             (align_encoders_ce :
                ilist (B := (fun T : Type => T -> CacheFormat -> CacheFormat)) types)
             (st : SumType types)
             (ce : CacheFormat)
    := (existT _ _ (i2th align_encoders_v (SumType_index types st) (SumType_proj types st) ce),
        ith align_encoders_ce (SumType_index types st) (SumType_proj types st) ce).

  Lemma align_format_sumtype_OK'
        {m : nat}
        {types : t Type m}
        (align_encoders_n :
           ilist2.ilist2 (B := fun T : Type => T -> CacheFormat -> nat) types)
        (align_encoders_v :
           i2list (B := fun T : Type => T -> CacheFormat -> nat)
                  (fun (T : Type) (n : _) => forall t ce, Vector.t (word 8) (n t ce)) align_encoders_n)
        (align_encoders_ce :
           ilist (B := (fun T : Type => T -> CacheFormat -> CacheFormat)) types)
        (formatrs :
           ilist (B := (fun T : Type => T -> @CacheFormat cache -> Comp (ByteString * (CacheFormat)))) types)
        (formatrs_OK : forall idx t (ce : CacheFormat),
            refine (ith formatrs idx t ce)
                   (ret (build_aligned_ByteString (i2th align_encoders_v idx t ce),
                         ith align_encoders_ce idx t ce)))
    : forall (st : SumType types)
             (ce : CacheFormat),
      refine (format_SumType types formatrs st ce)
             (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype
                                                            align_encoders_n
                                                            align_encoders_v
                                                            align_encoders_ce st ce))),
                   (snd (align_format_sumtype align_encoders_n
                                                            align_encoders_v
                                                            align_encoders_ce st ce)))).
  Proof.
    intros; unfold format_SumType, align_format_sumtype.
    rewrite formatrs_OK; reflexivity.
  Qed.

  Corollary align_format_sumtype_OK
            {m : nat}
            {types : t Type m}
            (align_encoders_n :
               ilist2.ilist2 (B := fun T : Type => T -> CacheFormat -> nat) types)
            (align_encoders_v :
               i2list (B := fun T : Type => T -> CacheFormat -> nat)
                      (fun (T : Type) (n : _) => forall t ce, Vector.t (word 8) (n t ce)) align_encoders_n)
            (align_encoders_ce :
               ilist (B := (fun T : Type => T -> CacheFormat -> CacheFormat)) types)
            (formatrs :
               ilist (B := (fun T : Type => T -> @CacheFormat cache -> Comp (ByteString * (CacheFormat)))) types)
            (formatrs_OK : Iterate_Ensemble_BoundedIndex (fun idx => forall t (ce : CacheFormat),
                                                              refine (ith formatrs idx t ce)
                                                                         (ret (build_aligned_ByteString (i2th align_encoders_v idx t ce),
                                                                               ith align_encoders_ce idx t ce))))
    : forall (st : SumType types)
             (ce : CacheFormat),
      refine (format_SumType types formatrs st ce)
             (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype align_encoders_n
                                                                               align_encoders_v
                                                                               align_encoders_ce st ce))),
                   (snd (align_format_sumtype align_encoders_n
                                              align_encoders_v
                                              align_encoders_ce st ce)))).
  Proof.
    intros; eapply align_format_sumtype_OK'; intros.
    eapply Iterate_Ensemble_BoundedIndex_equiv in formatrs_OK.
    apply formatrs_OK.
  Qed.

  Lemma align_format_sumtype_OK_inv'
        {m : nat}
        {types : t Type m}
        (A_OKs : SumType types -> Prop)
        (align_encoders_n :
               ilist2.ilist2 (B := fun T : Type => T -> CacheFormat -> nat) types)
            (align_encoders_v :
               i2list (B := fun T : Type => T -> CacheFormat -> nat)
                      (fun (T : Type) (n : _) => forall t ce, Vector.t (word 8) (n t ce)) align_encoders_n)
            (align_encoders_ce :
               ilist (B := (fun T : Type => T -> CacheFormat -> CacheFormat)) types)
        (encoders :
           ilist (B := (fun T : Type => T -> CacheFormat -> Comp (ByteString * (CacheFormat)))) types)
        (encoders_OK : forall idx t (ce : CacheFormat),
            A_OKs (inj_SumType _ idx t)
            -> refine (ith encoders idx t ce)
                      (ret (build_aligned_ByteString (i2th align_encoders_v idx t ce),
                            ith align_encoders_ce idx t ce)))
    : forall (st : SumType types)
             (ce : CacheFormat),
      A_OKs st
      -> refine (format_SumType types encoders st ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype align_encoders_n
                                                                               align_encoders_v
                                                                               align_encoders_ce st ce))),
                      (snd (align_format_sumtype align_encoders_n
                                                 align_encoders_v
                                                 align_encoders_ce st ce)))).
  Proof.
    intros; unfold format_SumType, align_format_sumtype.
    rewrite encoders_OK; eauto.
    reflexivity.
    rewrite inj_SumType_proj_inverse; eauto.
  Qed.

  Corollary align_format_sumtype_OK_inv
            {m : nat}
            {types : t Type m}
            (A_OKs : SumType types -> Prop)
            (align_encoders_n :
               ilist2.ilist2 (B := fun T : Type => T -> CacheFormat -> nat) types)
            (align_encoders_v :
               i2list (B := fun T : Type => T -> CacheFormat -> nat)
                      (fun (T : Type) (n : _) => forall t ce, Vector.t (word 8) (n t ce)) align_encoders_n)
            (align_encoders_ce :
               ilist (B := (fun T : Type => T -> CacheFormat -> CacheFormat)) types)
            (encoders :
               ilist (B := (fun T : Type => T -> CacheFormat -> Comp (ByteString * (CacheFormat)))) types)
            (encoders_OK : Iterate_Ensemble_BoundedIndex
                             (fun idx => forall t (ce : CacheFormat),
                                  A_OKs (inj_SumType _ idx t)
                                  -> refine (ith encoders idx t ce)
                                            (ret (build_aligned_ByteString (i2th align_encoders_v idx t ce),
                                                  ith align_encoders_ce idx t ce))))
    : forall (st : SumType types)
             (ce : CacheFormat),
      A_OKs st
      -> refine (format_SumType types encoders st ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype align_encoders_n
                                                                               align_encoders_v
                                                                               align_encoders_ce st ce))),
                      (snd (align_format_sumtype align_encoders_n
                                                 align_encoders_v
                                                 align_encoders_ce st ce)))).
  Proof.
    intros; eapply align_format_sumtype_OK_inv'; intros.
    eapply Iterate_Ensemble_BoundedIndex_equiv in encoders_OK.
    apply encoders_OK; eauto.
    eauto.
  Qed.

  Lemma AlignedFormatSumTypeDoneC
            {m : nat}
            {types : t Type m}
            (A_OKs_l : ilist (B := fun T : Type => T -> Prop) types)
            (A_OKs : SumType types -> Prop := fun st => ith A_OKs_l (SumType_index _ st) (SumType_proj _ st))
            (align_encoders_n :
               ilist2.ilist2 (B := fun T : Type => T -> CacheFormat -> nat) types)
            (align_encoders_v :
               i2list (B := fun T : Type => T -> CacheFormat -> nat)
                      (fun (T : Type) (n : _) => forall t ce, Vector.t (word 8) (n t ce)) align_encoders_n)
            (align_encoders_ce :
               ilist (B := (fun T : Type => T -> CacheFormat -> CacheFormat)) types)
            (encoders :
               ilist (B := (fun T : Type => T -> CacheFormat -> Comp (ByteString * (CacheFormat)))) types)
            (encoders_OK : Iterate_Ensemble_BoundedIndex
                             (fun idx => forall t (ce : CacheFormat),
                                  A_OKs (inj_SumType _ idx t)
                                  -> refine (ith encoders idx t ce)
                                            (ret (build_aligned_ByteString (i2th align_encoders_v idx t ce),
                                                  ith align_encoders_ce idx t ce))))
    : forall (st : SumType types)
             (ce : CacheFormat),
      A_OKs st
      -> refine (((format_SumType types encoders st) DoneC) ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype align_encoders_n
                                                                                  align_encoders_v
                                                                                  align_encoders_ce st ce))),
                      (snd (align_format_sumtype align_encoders_n
                                                 align_encoders_v
                                                 align_encoders_ce st ce)))).
  Proof.
    intros.
    etransitivity.
    eapply AlignedFormatDoneC.
    rewrite (align_format_sumtype_OK_inv A_OKs); try eassumption.
    instantiate (2 := fun ce => fst (align_format_sumtype align_encoders_n align_encoders_v align_encoders_ce st ce)).
    instantiate (1 := fun ce => snd (align_format_sumtype align_encoders_n align_encoders_v align_encoders_ce st ce)).
    simpl; reflexivity.
    simpl; reflexivity.
  Qed.

  Definition AlignedEncodeSumType
             {m : nat}
             {types : t Type m}
             (aligned_encoders :
                  ilist (B := fun T : Type => forall sz, AlignedEncodeM (S := T) sz) types)
    : forall sz, AlignedEncodeM (S := SumType types) sz :=
    fun sz v idx st env => ith aligned_encoders (SumType_index types st) sz v idx (SumType_proj types st) env.

  Lemma CorrectAlignedEncoderForFormatSumType'
            {m : nat}
            {types : t Type m}
            (formats : ilist types)
            (aligned_encoders :
                  ilist (B := fun T : Type => forall sz, AlignedEncodeM (S := T) sz) types)
            (encoders_OK :
               forall idx,
                 CorrectAlignedEncoder (ith formats idx) (ith aligned_encoders idx))
    : CorrectAlignedEncoder (format_SumType types formats)
                            (AlignedEncodeSumType aligned_encoders).
  Proof.
    unfold CorrectAlignedEncoder; intros.
    eexists (fun st => projT1 (encoders_OK (SumType_index types st)) (SumType_proj types st)).
    split; [ | split]; intros.
    - pose proof (projT2 (encoders_OK (SumType_index types s))); simpl in *; destruct H.
      specialize (H (SumType_proj types s) env); intuition.
    - pose proof (projT2 (encoders_OK (SumType_index types s))); simpl in *; destruct H0.
      specialize (H0 (SumType_proj types s) env); intuition.
      specialize (H0 (SumType_proj types s) env); intuition eauto.
    - unfold EncodeMEquivAlignedEncodeM; intros.
      pose proof (projT2 (encoders_OK (SumType_index types s))); simpl in *; destruct H.
      unfold EncodeMEquivAlignedEncodeM in H0; intuition eauto;
        specialize (H2 env (SumType_proj types s) idx); intuition eauto.
      + eapply H2; eauto.
      + eapply H5; eauto.
  Qed.

  Lemma CorrectAlignedEncoderForFormatSumType
            {m : nat}
            {types : t Type m}
            (formats : ilist types)
            (aligned_encoders :
                  ilist (B := fun T : Type => forall sz, AlignedEncodeM (S := T) sz) types)
            (encoders_OK :
               Iterate_Dep_Type_BoundedIndex
                 (fun idx =>
                 CorrectAlignedEncoder (ith formats idx) (ith aligned_encoders idx)))
    : CorrectAlignedEncoder (format_SumType types formats)
                            (AlignedEncodeSumType aligned_encoders).
  Proof.
    intros; eapply CorrectAlignedEncoderForFormatSumType'.
    eapply Lookup_Iterate_Dep_Type; eauto.
  Qed.

End AlignedSumType.

Arguments align_format_sumtype : simpl never.
Arguments SumType_proj : simpl never.
Arguments SumType_index : simpl never.
