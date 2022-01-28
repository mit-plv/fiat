From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : list (word 8) }.
Definition format :=
  format_list format_word ◦ data ++
  format_nat 8 ◦ length ◦ data.
Definition invariant (m : msg) := length (m.(data)) < pow2 8.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
