

Ltac start_synthesizing_encoder :=
  lazymatch goal with
  | |- CorrectAlignedEncoderFor ?Invariant ?Spec =>
    try unfold Spec; try unfold Invariant
  end;
  (* Memoize any string constants *)
  (*pose_string_hyps; *)
  eexists; simpl; intros.

Ltac align_encoder :=
    repeat first [
           apply @CorrectAlignedEncoderForThenC
         | apply @CorrectAlignedEncoderForDoneC
         | apply CorrectAlignedEncoderForFormatList
         | apply CorrectAlignedEncoderForFormatChar; eauto
         | apply CorrectAlignedEncoderForFormat2Char; eauto
         | apply CorrectAlignedEncoderForFormatNat].
