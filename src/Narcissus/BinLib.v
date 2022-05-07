Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Fiat.Narcissus.Common.Monoid.

Require Import Bedrock.Word.

Require Export
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedByteBuffer
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedString
        Fiat.Narcissus.BinLib.AlignedDelimiter
        Fiat.Narcissus.BinLib.AlignedLexeme
        Fiat.Narcissus.BinLib.AlignedSumType
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedIPChecksum.

Global Instance ByteStringQueueMonoid : Monoid ByteString := ByteStringQueueMonoid.

(*Lemma CorrectAlignedDecoder2CorrectDecoder
      {A} {cache : Cache.Cache}
      Invariant
      (FormatSpec : Specs.FormatM A _)
      (decoder : CorrectAlignedDecoderFor Invariant FormatSpec)
  : Specs.CorrectDecoderFor Invariant FormatSpec.
Proof.
  eexists (projT1 (projT2 decoder)).
  abstract (destruct decoder as [aligned_decoder [ [decoder Inv] ? ] ]; simpl in *;
            intuition eauto).
Defined. *)

Lemma CorrectAlignedEncoder2CorrectEncoder
      {A} {cache : Cache.Cache}
      (FormatSpec : Specs.FormatM A _)
      (encoder : CorrectAlignedEncoderFor FormatSpec)
  : Specs.CorrectEncoderFor FormatSpec.
Proof.
  eexists (projT1 (projT2 encoder)); split; intros;
    destruct encoder as [aligned_encoder [encoder [encoder_OK [padding_OK encoder_equiv] ] ] ].
  - destruct benv'.
    eapply encoder_OK; eauto.
  - simpl in *.
    eapply encoder_OK; eauto.
Defined.

(* Here are the expected correctness lemmas for synthesized functions. *)
Lemma CorrectDecodeEncode'
      {S T} {cache : Cache.Cache}
      {monoid : Monoid T}
  : forall Invariant
           (FormatSpec : Specs.FormatM S T)
           (encoder : Specs.CorrectEncoderFor FormatSpec)
           (decoder : Specs.CorrectDecoderFor Invariant FormatSpec),
    forall a envE envD b envE',
      Cache.Equiv envE envD
      -> Invariant a
      -> snd (fst (proj1_sig decoder)) envD
      -> projT1 encoder a envE = Some (b, envE')
      -> forall ext, exists envD',
          fst (fst (proj1_sig decoder)) (mappend b ext) envD = Some (a, ext, envD').
Proof.
  intros.
  destruct encoder as [encoder encoder_OK].
  destruct decoder as [ [ [decoder Inv] P_env] [decoder_OK Inv_cd] ]; simpl in *.
  specialize (proj1 (encoder_OK a envE) _ H2); intro.
  specialize (decoder_OK Inv_cd).
  destruct decoder_OK as [decoder_OK _].
  unfold Specs.cache_inv_Property in Inv_cd.
  eapply decoder_OK  with (ext := ext) in H3; eauto.
  destruct H3 as [? [? ?] ]; intuition.
  subst; eauto.
Qed.

(* Here are the expected correctness lemmas for optimized versions of the synthesized functions. *)
Lemma CorrectDecodeEncode
      {A} {cache : Cache.Cache}
      {sz}
  : forall Invariant
           (FormatSpec : Specs.FormatM A _)
           (encoder : CorrectAlignedEncoderFor FormatSpec)
           (decoder : CorrectAlignedDecoderFor Invariant FormatSpec),
    forall a ce cd v,
      Cache.Equiv ce cd
      -> Invariant a
      -> snd (projT1 (projT2 decoder)) cd
      -> forall idx ce' v',
          projT1 encoder sz v 0 a ce = Some (v', idx, ce')
          -> exists cd' idx',
            (projT1 decoder sz) v' 0 cd = Some (a, idx', cd').
Proof.
  intros.
  destruct (projT1 (projT2 encoder) a ce) as [ [? ?] | ] eqn: ?.
  - generalize Heqo; intro.
    (*eapply (@CorrectDecodeEncode' _ _ _ _ _ _
                                  (CorrectAlignedEncoder2CorrectEncoder _ encoder)
                                  (CorrectAlignedDecoder2CorrectDecoder _ _ decoder))
      in Heqo; eauto.
    destruct Heqo.
    simpl in H3.
    pose proof (projT2 (projT2 encoder)); simpl in *.
    destruct H4.
    pose proof (proj1 H5 _ _ _ _ Heqo0).
    assert (numBytes b <= sz)%nat.
    { destruct (Compare_dec.le_gt_dec (8 + 8 * sz) (length_ByteString b + 8 * 0)); eauto.
      apply @proj2 in H5.
      eapply proj2 in H5.
      eapply proj1 in H5.
      specialize (H5 _ _ _ v Heqo0 l).
      congruence.
      unfold length_ByteString in g.
      rewrite H6 in g.
      unfold gt in g.
      Lia.lia.
    }
    apply @proj2 in H5.
    eapply proj1 in H5.
    generalize H7; intros H7'.
    assert (numBytes b + (sz - numBytes b) = sz) as sz_eq by Lia.lia.
    eapply (build_aligned_ByteString_eq_split _ _ v) in H7.
    instantiate (1 := sz_eq) in H7.
    eapply (build_aligned_ByteString_eq_split _ _ v') in H7'.
    instantiate (1 := sz_eq) in H7'.
    specialize (H5 _ _ Heqo0 H6 (Vector.nil _) (fst (Vector_split _ _ (Guarded_Vector_split (numBytes b) sz v))) _
                   (snd (Vector_split _ _ (Guarded_Vector_split (numBytes b) sz v)))).
    destruct H5 as [? [? ?] ].
    simpl in *.
    rewrite <- Vector_split_append in H5.
    pose proof mempty_left; simpl in H9.
    rewrite build_aligned_ByteString_nil, H9 in H8.
    symmetry in H8.
    destruct (build_aligned_ByteString_split _ _ _ H8).
    symmetry in H8.
    rewrite H10 in H8 at 1.
    rewrite <- build_aligned_ByteString_append in H8.
    subst.
    assert (numBytes b + (sz - numBytes b) - (sz - numBytes b) = numBytes b) by Lia.lia.
    revert x1 H8 H10.
    rewrite H11; intros.
    assert (Some ((Guarded_Vector_split (numBytes b) sz v'), idx, ce') = Some
                                                                           (Vector.append x1
                                                                                          (snd (Vector_split (numBytes b) (sz - numBytes b) (Guarded_Vector_split (numBytes b) sz v))),
                                                                            numBytes b, c)).
    apply build_aligned_ByteString_inj in H8; subst.
    apply build_aligned_ByteString_inj in H7; subst.
    apply build_aligned_ByteString_inj in H7'; subst.
    revert H2.
    rewrite H7 at 1.
    rewrite H7' at 1.
    simpl.
    simpl in *; unfold ByteBuffer.t in H5.
    rewrite <- H5.
    rewrite <- sz_eq.
    simpl; unfold ByteBuffer.t, Core.char; intros.
    rewrite <- H2.
    reflexivity.
    injection H12; intros; subst; clear H12.
    instantiate (1 := build_aligned_ByteString (snd (Vector_split (numBytes b) (sz - numBytes b) (Guarded_Vector_split (numBytes b) sz v)))) in H3.
    apply build_aligned_ByteString_inj in H7'; subst.
    rewrite H10 in H3 at 1.
    rewrite <- build_aligned_ByteString_append in H3.
    rewrite <- H15 in H3.
    pose proof (proj2 (projT2 (projT2 decoder))).
    eapply H12 in H3.
    simpl in H3; destruct H3.
    eexists _, _.
    rewrite <- H3.
    rewrite H7' at 1.
    generalize sz_eq v'; clear; intros.
    rewrite <- sz_eq; simpl; reflexivity.
  - pose proof (projT2 (projT2 encoder)); simpl in *.
    destruct H3 as [? [? ?] ].
    specialize (H5 ce a 0); intuition.
    eapply H9 in Heqo.
    rewrite Heqo in H2; discriminate. *)
Admitted.

Lemma CorrectEncodeDecode
      {S}
      {cache : Cache.Cache}
  : forall Invariant
           (FormatSpec : Specs.FormatM S ByteString)
           (decoder : CorrectAlignedDecoderFor Invariant FormatSpec),
    forall sz v' ce cd cd' s idx',
      Cache.Equiv ce cd
      -> snd (projT1 (projT2 decoder)) cd
      -> (projT1 decoder sz) v' 0 cd = Some (s, idx', cd')
      -> Invariant s /\
         exists ce' (v1 : Vector.t (word 8) idx') (v2 : Vector.t (word 8) (sz - idx')) H,
           Guarded_Vector_split idx' sz v' = eq_rect _ _ (Vector.append v1 v2) _ H
           /\ Cache.Equiv ce' cd' /\ FormatSpec s ce (build_aligned_ByteString v1, ce').
Proof.
  intros.
  (*pose proof (Specs.CorrectEncodeDecode _ _ (CorrectAlignedDecoder2CorrectDecoder _ _ decoder)).
  simpl in *.
  destruct (fst (projT1 (projT2 decoder)) (build_aligned_ByteString v') cd)
    as [ [ [? ?] ?] | ] eqn: ?.
  - specialize (H2 _ _ _ _ _ _ H H0 Heqo);
      destruct H2 as [? [? [? [? [? ?] ] ] ] ].
    pose proof (proj2 (projT2 (projT2 decoder))).
    destruct H6 as [_ [? [? ?] ] ].
    specialize (H8 _ _ _ Heqo).
    specialize (H6 _ _ _ _ _ Heqo).
    destruct H8 as [? [? ?] ].
    rewrite H8 in H1; injection H1; intros; subst.
    intuition.
    assert (sz >= numBytes b)%nat.
    { revert H6; unfold length_ByteString; simpl.
      generalize (paddingOK b); clear; intros; Lia.lia. }
    assert (sz - numBytes b + (sz - (sz - numBytes b)) = sz - numBytes b + (sz - (sz - numBytes b))).
    Lia.lia.
    assert ((sz - (sz - numBytes b)) = numBytes b) by Lia.lia.
    eexists _, (fst (Vector_split _ _ (Guarded_Vector_split (sz - numBytes b) sz v'))),
    (snd (Vector_split _ _ (Guarded_Vector_split (sz - numBytes b) sz v'))), H12;
      intuition eauto.
    rewrite <- Vector_split_append.
    revert H12.
    destruct H13; intros.
    clear.
    intros; rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto.
    decide equality.
    destruct (build_aligned_ByteString_split' _ _ _ H9).
    rewrite H14 in H3.
    destruct (build_aligned_ByteString_split _ _ _ H3).
    subst.
    rewrite <- build_aligned_ByteString_append in H3.
    rewrite build_aligned_ByteString_eq_split' with (n := sz - numBytes b) in H3; eauto.
    replace (build_aligned_ByteString
       (fst
          (Vector_split (sz - numBytes b) (sz - (sz - numBytes b)) (Guarded_Vector_split (sz - numBytes b) sz v'))))
               with (build_aligned_ByteString x3); eauto.
    revert x2 x3 H3 H5 H14.
    generalize (Guarded_Vector_split (sz - numBytes b) sz v').
    rewrite H13.
    intros.
    apply build_aligned_ByteString_inj in H3; subst.
    rewrite <- Vector_append_split_fst; eauto.
    clear; Lia.lia.
  - pose proof (proj2 (projT2 (projT2 decoder))).
    destruct H3 as [_ [? [? ?] ] ].
    apply H4 in Heqo.
    congruence. *)
Admitted.

(* Various Constants that clients should never simplify. *)
Global Arguments split1 : simpl never.
Global Arguments split2 : simpl never.
Global Arguments weq : simpl never.
Global Arguments natToWord : simpl never.
Global Arguments Guarded_Vector_split : simpl never.
Global Arguments Core.append_word : simpl never.
Global Arguments split1' : simpl never.
Global Arguments split2' : simpl never.
Global Arguments natToWord : simpl never.
Global Arguments combine : simpl never.
Global Arguments Vector.nth : simpl never.
Global Arguments SetCurrentBytes : simpl never.
Global Arguments wordToNat : simpl never.
Global Arguments plus : simpl never.
