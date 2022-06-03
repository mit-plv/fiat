(* Projections of CorrectAligned*For proofs to CorrectAligned* and CorrectDecoder *)
Require Import
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs.

Definition CorrectAlignedDecoderFor_to_Decoder
           {V} {inv : V -> Prop} {f}
           (X : CorrectAlignedDecoderFor inv f)
  : ByteString -> CacheDecode -> option (V * ByteString * CacheDecode)
  := fst (projT1 (projT2 X)).

Definition CorrectAlignedDecoderFor_to_CacheInv
           {V} {inv : V -> Prop} {f}
           (X : CorrectAlignedDecoderFor inv f)
  : CacheDecode -> Prop
  := snd (projT1 (projT2 X)).

(* Required to prevent coq to create trouble unfolding these terms *)
Arguments CorrectAlignedDecoderFor_to_Decoder _ _ _ _ / .
Arguments CorrectAlignedDecoderFor_to_CacheInv _ _ _ _ / .

Lemma Project_CorrectAlignedDecoder :
  forall {V} {inv : V -> Prop} {f}
         (X : CorrectAlignedDecoderFor inv f),
    CorrectAlignedDecoder inv f (projT1 X).
Proof.
  destruct X; auto.
Defined.

Lemma Project_CorrectDecoder :
  forall {V} {inv : V -> Prop} {f}
         (X : CorrectAlignedDecoderFor inv f),
    CorrectDecoder ByteStringQueueMonoid inv inv
                   eq f
                   (CorrectAlignedDecoderFor_to_Decoder X)
                   (CorrectAlignedDecoderFor_to_CacheInv X) f.
Proof.
  intros V inv f X.
  unfold CorrectAlignedDecoderFor_to_CacheInv.
  unfold CorrectAlignedDecoderFor_to_Decoder.
  destruct X as [AD H].
  simpl in *.
  destruct H as [x0 H].
  simpl in *.
  do 3 destruct H.
  auto.
Defined.

Definition Project_CorrectAlignedEncoder {A} {f : FormatM A ByteString}
           (enc : CorrectAlignedEncoderFor f)
  : CorrectAlignedEncoder f (projT1 enc) :=
  Eval simpl in projT2 enc.

