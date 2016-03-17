Require Import Fiat.BinEncoders.NoEnv.Specs
               Fiat.BinEncoders.NoEnv.Libraries.Helpers
               Fiat.BinEncoders.NoEnv.Libraries.Sig
               Fiat.BinEncoders.NoEnv.Libraries.BinCore
               Fiat.BinEncoders.NoEnv.Libraries.FixInt
               Fiat.BinEncoders.NoEnv.Libraries.FixList2
               Fiat.BinEncoders.NoEnv.Libraries.Bool.

Set Implicit Arguments.

Record packet_t :=
  { sourceport  : { n : N | (n < exp2 16)%N };
    destport    : { n : N | (n < exp2 16)%N };
    sequence    : { n : N | (n < exp2 32)%N };
    acknowledge : { n : N | (n < exp2 32)%N };
    offset      : { n : N | (n < exp2 4)%N };
    reserved    : { s : list bool | length s = 6 };
    controls    : { s : list bool | length s = 4 };
    window      : { n : N | (n < exp2 16)%N };
    urgentptr   : { n : N | (n < exp2 16)%N }(*; no options for now
    options     : option_t*) }.

Definition encode_packet (bundle : packet_t * bin_t) :=
  FixInt_encode (sourceport (fst bundle),
  FixInt_encode (destport (fst bundle),
  FixInt_encode (sequence (fst bundle),
  FixInt_encode (acknowledge (fst bundle),
  FixInt_encode (offset (fst bundle),
  FixList2_encode Bool_encode (reserved (fst bundle),
  FixList2_encode Bool_encode (controls (fst bundle),
  FixInt_encode (window (fst bundle),
  FixInt_encode (urgentptr (fst bundle), snd bundle))))))))).

Require Import Fiat.BinEncoders.NoEnv.Automation.Solver.

Global Instance packet_decoder
  : Decoder of encode_packet.
Proof.
  decoder_from_encoder.
Defined.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "(*)"  [ "(,)" ].

(* Extraction "extracted-tcp.ml" encode_packet packet_decoder. *)