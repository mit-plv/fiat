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
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
Open Scope string_scope.

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

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
     WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
     WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Format : FormatM IPv4_Packet ByteString :=
  (format_nat 4 ◦ (constant 4)
               ++ format_nat 4 ◦ (plus 5) ◦ @length _ ◦ Options
               ++ format_unused_word 8 (* TOS Field! *)
               ++ format_word ◦ TotalLength
               ++ format_word ◦ ID
               ++ format_unused_word 1 (* Unused flag! *)
               ++ format_bool ◦ DF
               ++ format_bool ◦ MF
               ++ format_word ◦ FragmentOffset
               ++ format_word ◦ TTL
               ++ format_enum ProtocolTypeCodes ◦ Protocol)%format
ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn (format_word ◦ SourceAddress
               ++ format_word ◦ DestAddress
               ++ format_list format_word ◦ Options)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4.(Options)|) 11 /\
  lt (20 + 4 * |ipv4.(Options)|) (wordToNat ipv4.(TotalLength)).

(* Step One: Synthesize an encoder and a proof that it is correct. *)

Ltac new_encoder_rules ::=
  match goal with
    |- CorrectAlignedEncoder (_ ThenChecksum _ OfSize _ ThenCarryOn _) _ =>
    eapply @CorrectAlignedEncoderForIPChecksumThenC
  end.

Definition IPv4_encoder :
  CorrectAlignedEncoderFor IPv4_Packet_Format.
Proof.
  synthesize_aligned_encoder.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition IPv4_encoder_impl {sz} v r :=
  Eval simpl in (projT1 IPv4_encoder sz v 0 r tt).
Print IPv4_encoder_impl.

Ltac apply_new_combinator_rule ::=
  match goal with
  | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ _ =>
    eapply compose_IPChecksum_format_correct' with (format1 := fmt1);
    [ exact H
    | repeat calculate_length_ByteString
    | repeat calculate_length_ByteString
    | solve_mod_8
    | solve_mod_8
    | intros; normalize_format; apply_rules
    | normalize_format; apply_rules
    | solve_Prefix_Format
    ]
  end.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition IPv4_Packet_Header_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.
  synthesize_aligned_decoder.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Arguments GetCurrentBytes : simpl never.
Definition IPv4_decoder_impl {sz} v :=
  Eval simpl in (projT1 IPv4_Packet_Header_decoder sz v 0 ()).

Section BP.
  Local Opaque ByteBuffer.of_vector.
  Local Transparent weqb.
  Local Transparent natToWord.
  (* Some example uses of the encoder and decoder functions. *)
  (* A binary version of a packet, sourced directly from the web. *)
  Definition bin_pkt : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0]).

  Definition bin_pkt' : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;0;0;192;168;222;10;192;168;222;1;0;0;0;0]).
End BP.

(* An source version of a packet, different from binary packet above. *)
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

Local Transparent natToWord.
Local Transparent weqb.
(* This should succeed, *)
Eval compute in
    Ifopt (IPv4_encoder_impl (initialize_Aligned_ByteString 100) pkt)
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* This should fail because the total length field is too short, *)
Eval compute in
    Ifopt (IPv4_encoder_impl (initialize_Aligned_ByteString 100) bad_pkt)
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* Some addition checksum sanity checks. *)
Compute
  match IPv4_decoder_impl bin_pkt with
  | Some (p, _, _) => Some ((wordToN p.(SourceAddress)), wordToN p.(DestAddress))
  | None => None
  end.

Goal match AlignedIPChecksum.calculate_IPChecksum bin_pkt' 0 ()()  with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  reflexivity.
Qed.

Definition pkt' := {|
                    TotalLength := WO~0~1~1~0~0~1~0~0~0~0~0~0~0~0~0~0;
                    ID := WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    DF := false;
                    MF := false;
                    FragmentOffset := WO~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    TTL := WO~0~0~1~0~0~1~1~0;
                    Protocol := Fin.F1;
                    SourceAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~1~0~1~0;
                    DestAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~0~0~0~1;
                    Options := [] |}.

Goal match IPv4_encoder_impl (initialize_Aligned_ByteString 24) pkt'  with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  compute.
  reflexivity.
Qed.
