From Fiat.Narcissus Require Import Examples.TutorialPrelude.
Require Import Fiat.Narcissus.Automation.Error.

Record msg := { data : word 8 }.
Definition format :=
  format_string ◦ const "<data>" ++
  format_word ◦ data ++
  format_string ◦ const "</data>".
Definition invariant (_ : msg) := True.

Definition dec : Maybe (CorrectAlignedDecoderFor invariant format).
Proof.
  maybe_synthesize_aligned_decoder.
  Show Proof.
  (* More of a limitation than error: need to fix [solve_side_condition], add
  a decides instance, disallow simplifying the decoder function, and add a
  [DecodeMEquivAlignedDecodeM] instance. *)
Defined.
