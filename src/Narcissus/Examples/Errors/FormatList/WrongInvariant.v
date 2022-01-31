From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : list (word 8) }.
Definition format :=
  format_nat 8 ◦ length ◦ data ++
  format_list format_word ◦ data.
Definition invariant (m : msg) := length (m.(data)) < pow2 9.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
