From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : word 16 }.
(* How to achieve this? *)
Definition format :=
  format_word ◦ (split1 8 8 ∘ data) ++
  format_word ◦ (split2 8 8 ∘ data).
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
Defined.
