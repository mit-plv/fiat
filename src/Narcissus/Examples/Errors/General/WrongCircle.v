From Fiat.Narcissus Require Import Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Automation.Error.

Record msg := { data : word 8 }.
Definition format := format_word ∘ data.
Definition invariant (_ : msg) := True.

Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
  Show Proof.
Defined.
