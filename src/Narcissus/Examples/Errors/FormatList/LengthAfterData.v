From Fiat.Narcissus Require Import Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Automation.Error.

Record msg := { data : list (word 8) }.
Definition format :=
  format_list format_word ◦ data ++
  format_nat 8 ◦ length ◦ data.
Definition invariant (m : msg) := length (m.(data)) < pow2 8.

Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
  Show Proof.
Defined.
