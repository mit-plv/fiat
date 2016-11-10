Require Import
        Fiat.Common.ilist
        Fiat.Common.SumType
        Fiat.Common.IterateBoundedIndex
        Fiat.Examples.DnsServer.Packet
        Fiat.BinEncoders.Env.Common.Specs.

Require Import
        Coq.Sets.Ensembles
        Bedrock.Word.

Section SumType.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Definition encode_SumType_Spec {m}
             (types : Vector.t Type m)
             (encoders : ilist (B := fun T => T -> CacheEncode -> Comp (B * CacheEncode)) types)
             (st : SumType types)
    : CacheEncode -> Comp (B * CacheEncode) :=
    ith encoders (SumType_index types st) (SumType_proj types st).

  Definition encode_SumType_Impl {m}
             (types : Vector.t Type m)
             (encoders : ilist (B := fun T => T -> CacheEncode -> (B * CacheEncode)) types)
             (st : SumType types)
    : CacheEncode -> (B * CacheEncode) :=
    ith encoders (SumType_index types st) (SumType_proj types st).

  Lemma refine_encode_SumType {m}
        (types : Vector.t Type m)
        (encoder_Specs : ilist (B := fun T => T -> CacheEncode -> Comp (B * CacheEncode)) types)
        (encoder_Impls : ilist (B := fun T => T -> CacheEncode -> (B * CacheEncode)) types)
        (st : SumType types)
        (ce : CacheEncode)
    :
      Iterate_Ensemble_BoundedIndex'
        (fun idx => forall a ce,
             refine (ith encoder_Specs idx a ce)
                    (ret (ith encoder_Impls idx a ce)))
      -> refine (encode_SumType_Spec types encoder_Specs st ce) (ret (encode_SumType_Impl types encoder_Impls st ce)).
  Proof.
    intros.
    unfold encode_SumType_Impl, encode_SumType_Spec; simpl.
    remember (SumType_proj types st); clear Heqn.
    revert n ce; pattern (SumType_index types st).
    eapply Iterate_Ensemble_equiv'.
    apply H.
  Qed.

  Definition decode_SumType {m}
             (types : Vector.t Type m)
             (decoders : ilist (B := fun T => B -> CacheDecode -> option (T * B * CacheDecode)) types)
             (idx : Fin.t m)
             (b : B)
             (cd : CacheDecode)
    : option (SumType types * B * CacheDecode) :=
    `(a, b', cd') <- ith decoders idx b cd;
      Some (inj_SumType types idx a, b', cd').

  Lemma tri_proj_eq {A C D} : forall a c d (acd : A * C * D),
      a = fst (fst acd)
      -> c = snd (fst acd)
      -> d = snd acd
      -> acd = ((a, c), d).
  Proof.
    intros; subst; intuition.
  Qed.

  Theorem SumType_decode_correct' {m}
          {P}
          (types : Vector.t Type m)
          (encoders : ilist (B := fun T => T -> CacheEncode ->
                                           Comp (B * CacheEncode)) types)
          (decoders : ilist (B := fun T => B -> CacheDecode -> option (T * B * CacheDecode)) types)
          (invariants : forall idx, Vector.nth types idx -> Prop)
          (invariants_rest : forall idx, Vector.nth types idx -> B -> Prop)
          (cache_invariants : forall idx, (CacheDecode -> Prop) -> Prop)
          (encoders_decoders_correct : forall idx,
              cache_inv_Property P (cache_invariants idx)
              -> encode_decode_correct_f
                cache transformer
                (fun st => invariants idx st)
                (invariants_rest idx)
                (ith encoders idx)
                (ith decoders idx)
                P)
          idx
    :
      cache_inv_Property P (fun P => forall idx, cache_invariants idx P)
      -> encode_decode_correct_f cache transformer (fun st => SumType_index types st = idx /\ invariants _ (SumType_proj types st))
                                 (fun st b => invariants_rest _ (SumType_proj _ st) b)
                          (encode_SumType_Spec types encoders)
                          (decode_SumType types decoders idx)
                          P.
  Proof.
    split;
      revert types encoders decoders invariants invariants_rest encoders_decoders_correct;
      unfold encode_decode_correct_f, encode_SumType_Spec, decode_SumType.
    { intros; intuition.
      eapply (proj1 (encoders_decoders_correct _ (H _))) in H2; eauto;
        destruct_ex; intuition.
      subst; setoid_rewrite H2; simpl.
      eexists; intuition eauto.
      repeat f_equal.
      rewrite inj_SumType_proj_inverse; reflexivity.
    }
    { intros.
      destruct (ith decoders idx bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
        simpl in *; try discriminate; injections.
      eapply (proj2 (encoders_decoders_correct idx (H _))) in Heqo;
        eauto; destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst.
      exists x; exists x0; intuition;
        try rewrite index_SumType_inj_inverse; eauto.
      - pattern (SumType_index types (inj_SumType types idx n)),
        (SumType_proj types (inj_SumType types idx n)).
        eapply SumType_proj_inj; eauto.
      - pattern (SumType_index types (inj_SumType types idx n)),
        (SumType_proj types (inj_SumType types idx n)).
        eapply SumType_proj_inj; eauto.
    }
  Qed.

  Theorem SumType_decode_correct {m}
          {P}
          (types : Vector.t Type m)
          (encoders : ilist (B := fun T => T -> CacheEncode ->
                                           Comp (B * CacheEncode)) types)
          (decoders : ilist (B := fun T => B -> CacheDecode -> option (T * B * CacheDecode)) types)
          (invariants : ilist (B := fun T => Ensemble T) types)
          (invariants_rest : ilist (B := fun T => T -> B -> Prop) types)
          (cache_invariants : Vector.t (Ensemble (CacheDecode -> Prop)) m)
          (encoders_decoders_correct :
             Iterate_Ensemble_BoundedIndex (fun idx =>
              cache_inv_Property P (Vector.nth cache_invariants idx)
              -> encode_decode_correct_f
                cache transformer
                (ith invariants idx)
                (ith invariants_rest idx)
                (ith encoders idx)
                (ith decoders idx)
                P))
          idx
    :
      cache_inv_Property P (fun P => Iterate_Ensemble_BoundedIndex (fun idx => Vector.nth cache_invariants idx P))
      -> encode_decode_correct_f cache transformer (fun st => SumType_index types st = idx /\ (ith invariants) _ (SumType_proj types st))
                                 (fun st b => (ith invariants_rest) _ (SumType_proj _ st) b)
                          (encode_SumType_Spec types encoders)
                          (decode_SumType types decoders idx)
                          P.
  Proof.
    intros; eapply SumType_decode_correct'; eauto.
    intros.
    eapply Iterate_Ensemble_BoundedIndex_equiv in encoders_decoders_correct; eauto.
    unfold cache_inv_Property in *; intros;
      eapply Iterate_Ensemble_BoundedIndex_equiv in H; eauto.
  Qed.

End SumType.

Arguments SumType : simpl never.
