From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : list (word 8) }.
Definition format := format_list format_word ◦ data.
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
