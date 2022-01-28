From Fiat.Narcissus Require Import Examples.TutorialPrelude.

Record msg := { data : word 8 }.
Definition format :=
  format_string ◦ const "<data>" ++
  format_word ◦ data ++
  format_string ◦ const "</data>".
Definition invariant (_ : msg) := True.

Definition dec : CorrectAlignedDecoderFor invariant format.
Proof.
  synthesize_aligned_decoder.
  (* More of a limitation than error: need to fix [solve_side_condition], add
  a decides instance, disallow simplifying the decoder function, and add a
  [DecodeMEquivAlignedDecodeM] instance. *)
Defined.
