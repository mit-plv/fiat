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
        Fiat.Narcissus.BaseFormats
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

Definition IPv4_Packet_Format : FormatM IPv4_Packet ByteString :=
  (format_word ◦ (fun _ => natToWord 4 4)
++ (format_nat 4) ◦ IPv4_Packet_Header_Len
++ format_unused_word 8 (* TOS Field! *)
++ format_word ◦ TotalLength
++ format_word ◦ ID
++ format_unused_word 1 (* Unused flag! *)
++ format_bool ◦ DF
++ format_bool ◦ MF
++ format_word ◦ FragmentOffset
++ format_word ◦ TTL
++ format_enum ProtocolTypeCodes ◦ Protocol)%format
 ThenChecksum IPChecksum_Valid OfSize 16
    ThenCarryOn (format_word ◦ SourceAddress
                 ++ format_word ◦ DestAddress
                 ++ format_list format_word ◦ Options)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4.(Options)|) 11 /\
  lt (20 + 4 * |ipv4.(Options)|) (wordToNat ipv4.(TotalLength)).

(* Step One: Synthesize an encoder and a proof that it is correct. *)

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

Arguments andb : simpl never.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition IPv4_Packet_Header_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.
  (* We have to use an extra lemma at the start, because of the 'exotic'
     IP Checksum. *)
  start_synthesizing_decoder.
  Opaque CorrectDecoder.
  match goal with
    | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ =>
      eapply compose_IPChecksum_format_correct with (format1 := fmt1)
  end.
  apply H.
  intros.
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  solve_mod_8.
  solve_mod_8.
  eapply Nat.mod_divides;
  try omega.
  eexists (4 * (| Options a |)).
  omega.
  simpl; intros.
  instantiate (1 := fun _ => 0); simpl. admit.
  intros.
  NormalizeFormats.normalize_format.
  unfold format_unused_word.
  repeat apply_rules.
  eapply format_sequence_correct.
  cbv beta; synthesize_cache_invariant.
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  cbv beta; align_decoders.
  Grab Existential Variables.
  shelve.
  synthesize_cache_invariant.
  synthesize_cache_invariant.
  synthesize_cache_invariant.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Arguments GetCurrentBytes : simpl never.
Definition IPv4_decoder_impl {sz} v :=
  Eval simpl in (projT1 IPv4_Packet_Header_decoder sz v 0 ()).

Section BP.
  Local Opaque ByteBuffer.of_vector.

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
