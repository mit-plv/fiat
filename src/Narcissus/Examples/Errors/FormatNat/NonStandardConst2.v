From Fiat.Narcissus Require Import Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Automation.Error.

Record msg := { data : bool }.
Definition format := (fun _ => format_nat 7 0) ++ format_bool ◦ data.
Definition invariant (_ : msg) := True.

Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
Defined.

Let dec' := Eval simpl in extractDecoder dec.
Print dec'.
Print Assumptions dec'.
