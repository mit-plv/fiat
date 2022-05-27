From Fiat.Narcissus Require Import Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Automation.Error.

Record person := { age : word 8; salary : word 8 }.
Record msg := { data : word 8; who : person }.
(* Note that sometimes we have a dedicated format for the nested record. *)
Definition format :=
  format_word ◦ data ++
  format_word ◦ age ◦ who ++
  format_word ◦ salary ◦ who.
Definition invariant (_ : msg) := True.

Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
Defined.
