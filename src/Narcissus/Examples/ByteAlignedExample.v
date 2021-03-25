Require Import
        Coq.ZArith.ZArith
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore.

Open Scope nat_scope.
Open Scope type_scope.

(* Our source data is a record with two fields. *)
Record simple_record :=
  { id : word 16;
    payload : list (word 8) }.

Definition simple_format
           (p : simple_record) :=
        format_nat 8 (|p.(payload)|)        (* Format the length of the payload as an 8-bit word. *)
  ThenC format_word p.(id)                  (* Format the id of the record. *)
  ThenC format_list format_word p.(payload) (* Format the actual payload. *)
  DoneC.

(* A record needs to have fewer than 2^8 characters in its payload for
   the format to be invertible. *)
Definition simple_record_OK (p : simple_record) := (| p.(payload)| ) < pow2 8.

(* Step One: Synthesize an encoder and a proof that it is correct. *)
Definition simple_encoder :
  CorrectAlignedEncoderFor simple_format (fun _ => True).
Proof.
  synthesize_aligned_encoder.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition simple_encoder_impl r {sz} v :=
  Eval simpl in (projT1 simple_encoder r sz v 0 tt).

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition simple_decoder
  : CorrectAlignedDecoderFor simple_record_OK simple_format.
Proof.
  synthesize_aligned_decoder.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Definition simple_decoder_impl {sz} v :=
  Eval simpl in (projT1 simple_decoder sz v 0 tt).

(* We can now run these functions. As expected, the decoder successfully
   recovers the encoded packet.*)
Eval compute in
    Ifopt (simple_encoder_impl
             {| id := natToWord _ 10;
                payload := [wzero 8; wzero 8; wzero 8] |}
             (initialize_Aligned_ByteString 15))
  as bs Then simple_decoder_impl (fst (fst bs))
        Else None.

(* We can also examine the synthesized functions*)
Print simple_decoder_impl.
Print simple_encoder_impl.
