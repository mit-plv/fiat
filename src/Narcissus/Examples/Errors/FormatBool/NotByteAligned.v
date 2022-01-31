From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : bool }.
Definition format := format_bool ◦ data.
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
