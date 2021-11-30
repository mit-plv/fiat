From Fiat.Narcissus Require Import Examples.TutorialPrelude.

(** General errors *)
Module wrong_circle.
  Record msg := { data : word 8 }.
  Definition format := format_word ∘ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End wrong_circle.

Module pointed_composition.
  Record msg := { data : word 8 }.
  Definition format (m : msg) := format_word m.(data).
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End pointed_composition.

(* TODO *)
(* CorrectDecoder instances not found. *)
(* Unable to discharge invariant. *)
(* Equivalent but non-standard format, e.g., not using point-free style. *)
(* Errors in synthesizing cache invariants? *)
(* Can we resume the synthesis? *)


(** format_word *)
Module format_word_correct.
  Record msg := { data : word 16 }.
  Definition format := format_word ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  Definition decode := simplify (decoder_impl' dec).
End format_word_correct.

Module big_word_hang.
  Record msg := { data : word 128 }.
  Definition format := format_word ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    (* [synthesize_aligned_decoder] not terminating. More of a bug than an
    error. *)
  Abort.

End big_word_hang.

Module not_byte_aligned.
  Record msg := { data : word 1 }.
  Definition format := format_word ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    (* [synthesize_aligned_decoder] hangs. *)
  Abort.

End not_byte_aligned.

Module endian.
  Record msg := { data : word 16 }.
  (* How to achieve this? *)
  Definition format :=
    format_word ◦ (split1 8 8 ∘ data) ++
    format_word ◦ (split2 8 8 ∘ data).
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.

End endian.

(** format_bool *)
Module format_bool_correct.
  Record msg := { b1 : bool; b2 : bool; b3 : bool; b4 : bool; b5 : bool; b6 : bool; b7 : bool; b8 : bool }.
  Definition format :=
    format_bool ◦ b1 ++
    format_bool ◦ b2 ++
    format_bool ◦ b3 ++
    format_bool ◦ b4 ++
    format_bool ◦ b5 ++
    format_bool ◦ b6 ++
    format_bool ◦ b7 ++
    format_bool ◦ b8.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  Definition decode := simplify (decoder_impl' dec).
End format_bool_correct.

Module format_bool_correct'.
  Record msg := { data : bool }.
  Definition format := format_const WO~0~0~0~0~0~0~0 ++ format_bool ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  Definition decode := simplify (decoder_impl' dec).
End format_bool_correct'.

Module bool_not_byte_aligned.
  Record msg := { data : bool }.
  Definition format := format_bool ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    (* [synthesize_aligned_decoder] hangs. The same reason as non-byte-aligned
    word. *)
  Abort.
End bool_not_byte_aligned.

(** format_nat *)
Module non_standard_const1.
  Record msg := { data : bool }.
  Definition format := format_nat 7 ◦ const 0 ++ format_bool ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End non_standard_const1.

Module non_standard_const2.
  Record msg := { data : bool }.
  Definition format := (fun _ => format_nat 7 0) ++ format_bool ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End non_standard_const2.

(* TODO *)

(** format_list *)
Module format_list_correct.
  Record msg := { data : list (word 8) }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list format_word ◦ data.
  Definition invariant (m : msg) := length (m.(data)) < pow2 8.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  Definition decode := simplify (decoder_impl' dec).
End format_list_correct.

Module list_missing_length.
  Record msg := { data : list (word 8) }.
  Definition format := format_list format_word ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_missing_length.

Module list_missing_invariant.
  Record msg := { data : list (word 8) }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list format_word ◦ data.
  Definition invariant (_ : msg) := True.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_missing_invariant.

Module list_wrong_invariant.
  Record msg := { data : list (word 8) }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list format_word ◦ data.
  Definition invariant (m : msg) := length (m.(data)) < pow2 9.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_wrong_invariant.

Module list_length_after_data.
  Record msg := { data : list (word 8) }.
  Definition format :=
    format_list format_word ◦ data ++
    format_nat 8 ◦ length ◦ data.
  Definition invariant (m : msg) := length (m.(data)) < pow2 8.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_length_after_data.

Module list_not_byte_aligned.
  Record msg := { data : list bool }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list format_bool ◦ data.
  Definition invariant (m : msg) := length (m.(data)) < pow2 8.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_not_byte_aligned.

Module list_actually_byte_aligned.
  Record msg := { data : list bool }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list format_bool ◦ data.
  Definition invariant (m : msg) :=
    length (m.(data)) < pow2 8 /\ length (m.(data)) mod 8 = 0.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_actually_byte_aligned.

Module format_list_nat_correct.
  Record msg := { data : list nat }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list (format_nat 8) ◦ data.
  Definition invariant (m : msg) :=
    length (m.(data)) < pow2 8 /\ forall n, In n m.(data) -> n < pow2 8.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  Definition decode := simplify (decoder_impl' dec).
End format_list_nat_correct.

Module list_nat_wrong_invariant.
  Record msg := { data : list nat }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list (format_nat 8) ◦ data.
  Definition invariant (m : msg) :=
    length (m.(data)) < pow2 8 /\ forall n, In n m.(data) -> n < pow2 9.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_nat_wrong_invariant.

Module list_nat_non_standard_invariant.
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
  Abort.
End list_nat_non_standard_invariant.

Module list_nested_list.
  Record msg := { data : list (list (word 8)) }.
  Definition format :=
    format_nat 8 ◦ length ◦ data ++
    format_list (format_nat 8 ◦ length ++ format_list format_word) ◦ data.
  Definition invariant (m : msg) :=
    length (m.(data)) < pow2 8 /\ forall l, In l m.(data) -> length l < pow2 8.

  Definition dec : CorrectAlignedDecoderFor invariant format.
  Proof.
    synthesize_aligned_decoder.
  Abort.
End list_nested_list.

(** Record *)
(* TODO *)
(* field missing *)
(* nested record *)
(* invariant unsat *)
(* list of records *)
