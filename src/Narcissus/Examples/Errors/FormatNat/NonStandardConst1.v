From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : bool }.
Definition format := format_nat 7 ◦ const 0 ++ format_bool ◦ data.
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
