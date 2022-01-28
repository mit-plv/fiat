From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : list bool }.
Definition format :=
  format_nat 8 ◦ length ◦ data ++
  format_list format_bool ◦ data.
Definition invariant (m : msg) := length (m.(data)) < pow2 8.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
