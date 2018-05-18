Require Import Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Automation.Solver.

Ltac start_synthesizing_encoder :=
  lazymatch goal with
  | |- CorrectAlignedEncoderFor ?Invariant ?Spec =>
    try unfold Spec; try unfold Invariant
  end;
  (* Memoize any string constants *)
  (*pose_string_hyps; *)
  eexists; simpl; intros.

Ltac align_encoder_step :=
  first [
      apply @CorrectAlignedEncoderForThenC
    | apply @CorrectAlignedEncoderForDoneC
    | apply CorrectAlignedEncoderForFormatList
    | apply CorrectAlignedEncoderForFormatChar; eauto
    | apply CorrectAlignedEncoderForFormat2Char; eauto
    | apply CorrectAlignedEncoderForFormatNat].

Ltac align_encoder :=
  repeat align_encoder_step.

Ltac start_synthesizing_decoder :=
  match goal with
  | |- CorrectAlignedDecoderFor ?Invariant ?Spec =>
    try unfold Spec; try unfold Invariant
  end;

  (* Memoize any string constants *)
  (* pose_string_hyps; *)
  eapply Start_CorrectAlignedDecoderFor; simpl; intros.

Ltac align_decoders_step :=
  first [
      eapply @AlignedDecodeNatM; intros
    | eapply @AlignedDecodeBind2CharM; intros; eauto
    | eapply @AlignedDecodeListM; intros; eauto
    | eapply @AlignedDecodeCharM; intros; eauto
    | eapply @Return_DecodeMEquivAlignedDecodeM].

Ltac align_decoders := repeat align_decoders_step.
Locate Ltac normalize_compose .
Ltac synthesize_aligned_decoder :=
  start_synthesizing_decoder;
  [ match goal with
      |- CorrectDecoder ?monoid _ _ _ _ _ => normalize_compose monoid
    end;
    repeat decode_step idtac
  | cbv beta; synthesize_cache_invariant
  | cbv beta; optimize_decoder_impl
  | ];
  cbv beta; align_decoders.

Ltac synthesize_aligned_encoder :=
  start_synthesizing_encoder;
  align_encoder.
