Require Import
        Fiat.Common.ilist
        Fiat.Common.SumType
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

  Theorem SumType_decode_correct {m}
          (types : Vector.t Type m)
          (encoders : ilist (B := fun T => T -> CacheEncode ->
                                           Comp (B * CacheEncode)) types)
          (decoders : ilist (B := fun T => B -> CacheDecode -> option (T * B * CacheDecode)) types)
          (invariants : forall idx, Vector.nth types idx -> Prop)
          (encoders_decoders_correct : forall idx,
              encode_decode_correct_f
                cache transformer
                (fun st => invariants idx st)
                (ith encoders idx)
                (ith decoders idx))
          idx
    :
    encode_decode_correct_f cache transformer (fun st => SumType_index types st = idx /\ invariants _ (SumType_proj types st))
                          (encode_SumType_Spec types encoders)
                          (decode_SumType types decoders idx).
  Proof.
    split;
      revert types encoders decoders invariants encoders_decoders_correct;
      unfold encode_decode_correct_f, encode_SumType_Spec, decode_SumType.
    { intros; intuition.
      eapply (proj1 (encoders_decoders_correct _)) in H1; eauto;
        destruct_ex; intuition.
      subst; rewrite H1; simpl.
      eexists; intuition eauto.
      repeat f_equal.
      rewrite inj_SumType_proj_inverse; reflexivity.
    }
    { intros.
      destruct (ith decoders idx bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
        simpl in *; try discriminate; injections.
      eapply (proj2 (encoders_decoders_correct idx)) in Heqo;
        eauto; destruct_ex; intuition; subst.
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
End SumType.

Arguments SumType : simpl never.
