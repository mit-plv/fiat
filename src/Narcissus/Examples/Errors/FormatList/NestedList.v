From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : list (list (word 8)) }.
Definition format :=
  format_nat 8 ◦ length ◦ data ++
  format_list (format_nat 8 ◦ length ++ format_list format_word) ◦ data.
Definition invariant (m : msg) :=
  length (m.(data)) < pow2 8 /\ forall l, In l m.(data) -> length l < pow2 8.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
