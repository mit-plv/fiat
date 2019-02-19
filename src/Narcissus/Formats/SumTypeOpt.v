Require Import
        Fiat.Common.ilist
        Fiat.Common.SumType
        Fiat.Common.IterateBoundedIndex
        Fiat.Narcissus.Common.Specs.

Require Import
        Coq.Sets.Ensembles
        Bedrock.Word.

Section SumType.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : MonoidUnitOpt monoid bool}.

  Definition format_SumType {m}
             (types : Vector.t Type m)
             (formatrs : ilist (B := fun T => T -> CacheFormat -> Comp (B * CacheFormat)) types)
             (st : SumType types)
    : CacheFormat -> Comp (B * CacheFormat) :=
    ith formatrs (SumType_index types st) (SumType_proj types st).

  Definition encode_SumType {m}
             (types : Vector.t Type m)
             (formatrs : ilist (B := fun T => T -> CacheFormat -> (B * CacheFormat)) types)
             (st : SumType types)
    : CacheFormat -> (B * CacheFormat) :=
    ith formatrs (SumType_index types st) (SumType_proj types st).

  Lemma refine_format_SumType {m}
        (types : Vector.t Type m)
        (formats : ilist (B := fun T => T -> CacheFormat -> Comp (B * CacheFormat)) types)
        (encoders : ilist (B := fun T => T -> CacheFormat -> (B * CacheFormat)) types)
        (st : SumType types)
        (ce : CacheFormat)
    :
      Iterate_Ensemble_BoundedIndex'
        (fun idx => forall a ce,
             refine (ith formats idx a ce)
                    (ret (ith encoders idx a ce)))
      -> refine (format_SumType types formats st ce) (ret (encode_SumType types encoders st ce)).
  Proof.
    intros.
    unfold format_SumType, encode_SumType; simpl.
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
          (formatrs : ilist (B := fun T => T -> CacheFormat ->
                                           Comp (B * CacheFormat)) types)
          (decoders : ilist (B := fun T => B -> CacheDecode -> option (T * B * CacheDecode)) types)
          (invariants : forall idx, Vector.nth types idx -> Prop)
          (cache_invariants : forall idx, (CacheDecode -> Prop) -> Prop)
          (formatrs_decoders_correct : forall idx,
              cache_inv_Property P (cache_invariants idx)
              -> CorrectDecoder
                monoid
                (fun st => invariants idx st)
                (fun st => invariants idx st)
                eq
                (ith formatrs idx)
                (ith decoders idx)
                P (ith formatrs idx))
          idx
    :
      cache_inv_Property P (fun P => forall idx, cache_invariants idx P)
      -> CorrectDecoder monoid (fun st => SumType_index types st = idx /\ invariants _ (SumType_proj types st))
                        (fun st => SumType_index types st = idx /\ invariants _ (SumType_proj types st))
                        eq
                        (format_SumType types formatrs)
                        (decode_SumType types decoders idx)
                        P
                        (format_SumType types formatrs).
  Proof.
    split;
      revert types formatrs decoders invariants formatrs_decoders_correct;
      unfold CorrectDecoder, format_SumType, decode_SumType.
    { intros; intuition.
      unfold id in *;
      eapply (proj1 (formatrs_decoders_correct _ (H _))) in H2; eauto;
        destruct_ex; intuition.
      subst; setoid_rewrite H2; simpl.
      eexists _, _; intuition eauto.
      repeat f_equal.
      unfold id; rewrite inj_SumType_proj_inverse; reflexivity.
    }
    { intros.
      destruct (ith decoders idx t env') as [ [ [? ?] ? ] | ] eqn : ? ;
        simpl in *; try discriminate; injections.
      eapply (proj2 (formatrs_decoders_correct idx (H _))) in Heqo;
        eauto; destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst.
      eexists _, _; intuition eauto; unfold id in *; eauto;
        try rewrite index_SumType_inj_inverse; eauto.
      - unfold id; pattern (SumType_index types (inj_SumType types idx n)),
        (SumType_proj types (inj_SumType types idx n)).
        eapply SumType_proj_inj; eauto.
      - unfold id;
          pattern (SumType_index types (inj_SumType types idx n)),
          (SumType_proj types (inj_SumType types idx n)).
        eapply SumType_proj_inj; eauto.
    }
  Qed.

  Theorem SumType_decode_correct {m}
          {P}
          (types : Vector.t Type m)
          (formatrs : ilist (B := fun T => T -> CacheFormat ->
                                           Comp (B * CacheFormat)) types)
          (decoders : ilist (B := fun T => B -> CacheDecode -> option (T * B * CacheDecode)) types)
          (invariants : ilist (B := fun T => Ensemble T) types)
          (cache_invariants : Vector.t (Ensemble (CacheDecode -> Prop)) m)
          (formatrs_decoders_correct :
             Iterate_Ensemble_BoundedIndex (fun idx =>
              cache_inv_Property P (Vector.nth cache_invariants idx)
              -> CorrectDecoder
                monoid
                (ith invariants idx)
                (ith invariants idx)
                eq
                (ith formatrs idx)
                (ith decoders idx)
                P
                (ith formatrs idx)))
          idx
    :
      cache_inv_Property P (fun P => Iterate_Ensemble_BoundedIndex (fun idx => Vector.nth cache_invariants idx P))
      -> CorrectDecoder monoid
                        (fun st => SumType_index types st = idx /\ (ith invariants) _ (SumType_proj types st))
                        (fun st => SumType_index types st = idx /\ (ith invariants) _ (SumType_proj types st))
                        eq
                          (format_SumType types formatrs)
                          (decode_SumType types decoders idx)
                          P
                          (format_SumType types formatrs).
  Proof.
    intros; eapply SumType_decode_correct'; eauto.
    intros.
    eapply Iterate_Ensemble_BoundedIndex_equiv in formatrs_decoders_correct; eauto.
    unfold cache_inv_Property in *; intros;
      eapply Iterate_Ensemble_BoundedIndex_equiv in H; eauto.
  Qed.

End SumType.

Arguments SumType : simpl never.
