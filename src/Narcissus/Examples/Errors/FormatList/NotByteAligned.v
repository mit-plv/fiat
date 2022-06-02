From Fiat.Narcissus Require Import Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Automation.Error.

Record msg := { data : list bool }.
Definition format :=
  format_nat 8 ◦ length ◦ data ++
  format_list format_bool ◦ data.
Definition invariant (m : msg) := length (m.(data)) < pow2 8.

Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
Defined.

Let dec' := Eval simpl in extractDecoder dec.
Print dec'.
Print Assumptions dec'.
