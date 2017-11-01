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
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedDecoders.

Require Import
        Bedrock.Word.

Section AlignedSumType.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Lemma align_format_sumtype_OK_inv'
        {m : nat}
        {types : t Type m}
        (A_OKs : SumType types -> Prop)
        (align_encoders :
           ilist (B := (fun T : Type => T -> CacheFormat -> ({n : _ & Vector.t (word 8) n} * (CacheFormat)))) types)
        (encoders :
           ilist (B := (fun T : Type => T -> CacheFormat -> Comp (ByteString * (CacheFormat)))) types)
        (encoders_OK : forall idx t (ce : CacheFormat),
            A_OKs (inj_SumType _ idx t)
            -> refine (ith encoders idx t ce)
                      (ret (build_aligned_ByteString (projT2 (fst (ith align_encoders idx t ce))),
                            snd (ith align_encoders idx t ce))))
    : forall (st : SumType types)
             (ce : CacheFormat),
      A_OKs st
      -> refine (format_SumType types encoders st ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype align_encoders st ce))),
                      (snd (align_format_sumtype align_encoders st ce)))).
  Proof.
    intros; unfold format_SumType, align_format_sumtype.
    rewrite encoders_OK; eauto.
    reflexivity.
    rewrite inj_SumType_proj_inverse; eauto.
  Qed.

  Corollary align_format_sumtype_OK
            {m : nat}
            {types : t Type m}
            (A_OKs : SumType types -> Prop)
            (align_encoders :
               ilist (B := (fun T : Type => T -> CacheFormat -> ({n : _ & Vector.t (word 8) n} * (CacheFormat)))) types)
            (encoders :
               ilist (B := (fun T : Type => T -> CacheFormat -> Comp (ByteString * (CacheFormat)))) types)
            (encoders_OK : Iterate_Ensemble_BoundedIndex
                             (fun idx => forall t (ce : CacheFormat),
                                  A_OKs (inj_SumType _ idx t)
                                  -> refine (ith encoders idx t ce)
                                            (ret (build_aligned_ByteString (projT2 (fst (ith align_encoders idx t ce))),
                                                  snd (ith align_encoders idx t ce)))))
    : forall (st : SumType types)
             (ce : CacheFormat),
      A_OKs st
      -> refine (format_SumType types encoders st ce)
                (ret (build_aligned_ByteString (projT2 (fst (align_format_sumtype align_encoders st ce))),
                      (snd (align_format_sumtype align_encoders st ce)))).
  Proof.
    intros; eapply align_format_sumtype_OK_inv'; intros.
    eapply Iterate_Ensemble_BoundedIndex_equiv in encoders_OK.
    apply encoders_OK; eauto.
    eauto.
  Qed.

End AlignedSumType.
