Require Import Fiat.Narcissus.Common.Monoid.

Require Import Bedrock.Word.

Require Export
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedIPChecksum.

Global Instance ByteStringQueueMonoid : Monoid ByteString := ByteStringQueueMonoid.

(* Here are the expected correctness lemmas for optimized versions of the synthesized functions. *)
Lemma CorrectDecodeEncode
      {A} {cache : Cache.Cache}
      {sz}
  : forall Invariant
           (FormatSpec : Specs.FormatM A _)
           (encoder : CorrectAlignedEncoderFor FormatSpec Invariant)
           (decoder : CorrectAlignedDecoderFor Invariant FormatSpec),
    forall a ce cd v,
      Cache.Equiv ce cd
      -> Invariant a
      -> snd (projT1 (projT2 decoder)) cd
      -> forall cd' idx ce' v',
          projT1 encoder a sz v 0 ce = Some (v', idx, ce')
          -> (projT1 decoder sz) v' 0 cd = Some (a, idx, cd').
Proof.
  intros.
  destruct encoder as [aligned_encoder aligned_encoder_OK].
  simpl in *; specialize (aligned_encoder_OK _ H0).
  destruct aligned_encoder_OK as [encoder [encoder_OK [padding_OK encoder_equiv] ] ].
  destruct decoder as [aligned_decoder [ [decoder Inv] [ [Inv' [decoder_OK Inv_cd] ] decoder_equiv ] ] ]; simpl in *.
  specialize (decoder_OK Inv_cd).
Abort.
(* specialize (encoder_OK ce _ (Core.ReturnComputes _)) .
  destruct (encoder_equiv ce 0) as [? [? ?] ].
  specialize (H3 (padding_OK _)).

  destruct decoder_equiv.

  specialize (encoder_OK a ce _ (ReturnComputes _)) .
  destruct decoder_OK as [decoder_OK _].
  destruct (encoder a ce) as [bin ce'].
  unfold cache_inv_Property in Inv_cd.
  eapply decoder_OK  with (ext := mempty) in encoder_OK; eauto.
  destruct_ex; intuition.
  rewrite mempty_right in H3; eauto.
Qed. *)

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
