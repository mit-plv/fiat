From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : bool }.
Definition format := (fun _ => format_nat 7 0) ++ format_bool ◦ data.
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
