Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Our source data type for IP packets. *)
Record IPv4_Packet :=
  { TotalLength : word 16;
     ID : word 16;
     DF : bool; (* Don't fragment flag *)
     MF : bool; (*  Multiple fragments flag *)
     FragmentOffset : word 13;
     TTL : word 8;
     Protocol : EnumType ["ICMP"; "TCP"; "UDP"];
     SourceAddress : word 32;
     DestAddress : word 32;
     Options : list (word 32) }.
(*@Tuple <"TotalLength" :: word 16,
  "ID" :: word 16,
  "DF" :: bool, (* Don't fragment flag *)
  "MF" :: bool, (*  Multiple fragments flag *)
  "FragmentOffset" :: word 13,
  "TTL" :: word 8,
  "Protocol" :: EnumType ["ICMP"; "TCP"; "UDP"],
  "SourceAddress" :: word 32,
  "DestAddress" :: word 32,
  "Options" :: list (word 32)>.*)

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
     WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
     WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Header_Len (ip4 : IPv4_Packet) := 5 + |ip4.(Options)|.

Definition IPv4_Packet_Format (ip4 : IPv4_Packet)  :=
  (format_word (natToWord 4 4)
               ThenC format_nat 4 (IPv4_Packet_Header_Len ip4)
               ThenC format_unused_word 8 (* TOS Field! *)
               ThenC format_word ip4.(TotalLength)
               ThenC format_word ip4.(ID)
               ThenC format_unused_word 1 (* Unused flag! *)
               ThenC format_bool ip4.(DF)
               ThenC format_bool ip4.(MF)
               ThenC format_word ip4.(FragmentOffset)
               ThenC format_word ip4.(TTL)
               ThenC format_enum ProtocolTypeCodes ip4.(Protocol)
               DoneC)
    ThenChecksum IPChecksum_Valid' OfSize 16
    ThenCarryOn (format_word ip4.(SourceAddress)
                             ThenC format_word ip4.(DestAddress)
                             ThenC format_list format_word ip4.(Options)
                             DoneC)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4.(Options)|) 11 /\
  lt (20 + 4 * |ipv4.(Options)|) (wordToNat ipv4.(TotalLength)).

(* Step One: Synthesize an encoder and a proof that it is correct. *)

Definition IPv4_encoder :
  CorrectAlignedEncoderFor IPv4_Packet_Format IPv4_Packet_OK.
Proof.
  synthesize_aligned_encoder.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition IPv4_encoder_impl r {sz} v :=
  Eval simpl in (projT1 IPv4_encoder r sz v 0 tt).

(* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)
Lemma IPv4_Packet_Header_Len_eq
  : forall packet len,
    IPv4_Packet_Header_Len packet = len
    -> ((|packet.(Options) |) = len - 5).
Proof.
  unfold IPv4_Packet_Header_Len; intros.
  apply Minus.plus_minus.
  rewrite H; reflexivity.
Qed.

Lemma IPv4_Packet_Header_Len_bound
  : forall packet,
    IPv4_Packet_OK packet ->
    lt (IPv4_Packet_Header_Len packet) (pow2 4)%nat.
Proof.
  intros; replace (pow2 4) with 16 by reflexivity.
  unfold IPv4_Packet_OK in H; unfold IPv4_Packet_Header_Len.
  omega.
Qed.

Hint Resolve IPv4_Packet_Header_Len_eq : data_inv_hints.
Hint Resolve IPv4_Packet_Header_Len_bound : data_inv_hints.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition IPv4_Packet_Header_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.
  (* We have to use an extra lemma at the start, because of the 'exotic'
     IP Checksum. *)
  eapply CorrectAlignedDecoderForIPChecksumThenC.
  repeat calculate_length_ByteString.
  (* Once that's done, the normal automation works just fine :) *)
  synthesize_aligned_decoder.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Arguments GetCurrentBytes : simpl never.
Definition IPv4_decoder_impl {sz} v :=
  Eval simpl in (projT1 IPv4_Packet_Header_decoder sz v 0 ()).


(* Some example uses of the encoder and decoder functions. *)
(* A binary version of a packet, sourced directly from the web. *)
Definition bin_pkt : Vector.t (word 8) _ :=
  Eval compute in Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0].

(* An source version of a packet. *)
Definition pkt :=
  {| TotalLength := WO~0~1~1~1~0~1~0~0~0~0~0~0~0~0~0~0;
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Definition bad_pkt :=
  {| TotalLength := wzero _; (* length is too short *)
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Eval vm_compute in (IPv4_decoder_impl bin_pkt).

(* This should succeed, *)
Eval compute in
    Ifopt (IPv4_encoder_impl pkt (initialize_Aligned_ByteString 100))
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* This should fail because the total length field is too short, *)
Eval compute in
    Ifopt (IPv4_encoder_impl bad_pkt (initialize_Aligned_ByteString 100))
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)
