From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : list nat }.
Definition format :=
  format_nat 8 ◦ length ◦ data ++
  format_list (format_nat 8) ◦ data.
(* Only swap the two clauses. *)
Definition invariant (m : msg) :=
  forall n, In n m.(data) -> n < pow2 8 /\ length (m.(data)) < pow2 8.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
