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

  Definition encode_SumType {m}
             (types : Vector.t Type m)
             (encoders : ilist (B := fun T => T -> CacheEncode -> B * CacheEncode) types)
             (st : SumType types)
    : CacheEncode -> B * CacheEncode :=
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
          (encoders : ilist (B := fun T => T -> CacheEncode -> B * CacheEncode) types)
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
                          (encode_SumType types encoders)
                          (decode_SumType types decoders idx).
  Proof.
    revert types encoders decoders invariants encoders_decoders_correct.
    unfold encode_decode_correct_f, encode_SumType, decode_SumType.
    induction types.
    - inversion idx.
    - revert types IHtypes h; pattern n, idx; apply Fin.caseS;
        clear n idx; intros; destruct H0.
      + (* First element *)
        destruct types.
        * unfold SumType in data; simpl in *.
          destruct (encoders_decoders_correct Fin.F1 _ _ _ _ _ ext H H2 H1) as [? [? ?] ]; simpl in *.
          rewrite H3; simpl; eexists; eauto.
        * destruct data; try discriminate; simpl in *.
          destruct (encoders_decoders_correct Fin.F1 _ _ _ _ _ ext H H2 H1) as [? [? ?] ]; simpl in *.
          match goal with
            |- context [@prim_fst ?A ?B ?a ?z ?k] =>
            replace (@prim_fst A B a z k) with (Some (h1, ext, x))
              by (rewrite <- H3; reflexivity)
          end.
          simpl; eauto.
      + (* Second element *)
        destruct types; try discriminate.
        destruct data; try discriminate.
        assert (p = SumType_index (Vector.cons Type h0 n types) s) by
            (apply Fin.FS_inj in H0;
             rewrite <- H0; reflexivity).
        assert (invariants
                  (Fin.FS (SumType_index (Vector.cons Type h0 n types) s))
                  (SumType_proj (Vector.cons Type h0 n types) s)) as H3' by
            eapply H2.
        assert (ith encoders
                    (Fin.FS (SumType_index (Vector.cons Type h0 n types) s))
                    (SumType_proj (Vector.cons Type h0 n types) s) env =
                (bin, xenv)) as H1' by apply H1; clear H1.
        assert (exists xenv' : CacheDecode,
     (`(a, b', cd') <- ith (ilist_tl decoders) p (transform bin ext) env';
      Some
        (inj_SumType (Vector.cons Type h0 n types) p a, b',
        cd')) = Some (s, ext, xenv') /\ Equiv xenv xenv').
        { eapply (IHtypes p (ilist_tl encoders) (ilist_tl decoders)
                 (fun idx => invariants (Fin.FS idx))); eauto.
          intros.
          destruct (encoders_decoders_correct (Fin.FS _) _ _ _ _ _ ext0 H1 H4 H5) as [? [? ?] ]; simpl in *.
          eexists; intuition eauto.
        }
        destruct_ex; intuition.
        eexists; split; eauto.
        match goal with
            |- context [ith ?d ?idx ?tb ?env'] =>
            destruct (ith d idx tb env') eqn: ?
          end.
        simpl in Heqo.
        unfold ilist_tl in H4.
        match type of H4 with
          context [@ith ?A ?B ?m ?As ?il ?n ?il' ?M] =>
          assert (@ith A B m As il n il' M = Some p0) as Heqo'
              by (simpl; apply Heqo);
            rewrite Heqo' in H4
        end.
        destruct p0 as [ [? ?] ?]; simpl in *.
        injection H4; intros.
        repeat f_equal; eauto.
        match type of H4 with
          context [@ith ?A ?B ?m ?As ?il ?n ?il' ?M] =>
          assert (@ith A B m As il n il' M = None) as Heqo'
              by (simpl; apply Heqo);
            rewrite Heqo' in H4; discriminate
        end.
  Qed.
End SumType.

Arguments SumType : simpl never.
