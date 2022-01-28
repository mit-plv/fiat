From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : word 8 }.
Definition format (m : msg) := format_word m.(data).
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
