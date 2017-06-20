Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeCheckSum
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.SolverOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.IPChecksum.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Definition InjectEnum {n A}
           (gallina_constructors: VectorDef.t A n)
           (enum_member: Fin.t n) : A :=
  VectorDef.nth gallina_constructors enum_member.
  Require Import IPv4Header.

Definition MakeDecoder {A}
           (impl: ByteString -> unit -> option (A * ByteString * unit))
           (bs: ByteString) : option (A * ByteString) :=
  (* let bs := {| padding := 0; front := WO; paddingOK := zero_lt_eight; byteString := buffer |} in *)
  match impl bs () with
  | Some (pkt, bs, _) => Some (pkt, bs)
  | None => None
  end.

Section EncodeWord.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  (* Extracting words as Int64 prevents us from recursing on them directly *)

  Fixpoint encode_word'_recurse_on_size (sz : nat) (w : word sz) (b' : B) {struct sz} : B.
  Proof.
    destruct sz.
    - apply b'.
    - apply (enqueue_opt (whd w) (encode_word'_recurse_on_size sz (wtl w) b')).
  Defined.

  Lemma encode'_on_size_correct :
    forall sz w b', encode_word' sz w b' = encode_word'_recurse_on_size sz w b'.
  Proof.
    induction sz; dependent destruction w; intros; simpl.
    - reflexivity.
    - rewrite IHsz; reflexivity.
  Qed.
End EncodeWord.

Section Ethernet.
  Require Import EthernetHeader.

  Inductive fiat_ethernet_type := ARP | IP | RARP.

  Definition fiat_ethernet_decode packet_length := MakeDecoder (fst (frame_decoder packet_length)).

  Definition List_of_vector {A n} (v: Vector.t A n) : list A :=
    Vector.fold_right List.cons v nil.

  Definition fiat_ethernet_destruct_packet {A}
             (f: forall (Destination : list char)
                   (Source : list char)
                   (type : fiat_ethernet_type),
                 A)
             (packet: EthernetHeader) :=
    f  (List_of_vector packet!"Destination")
       (List_of_vector packet!"Source")
       (InjectEnum [ARP; IP; RARP] packet!"Type").
End Ethernet.

Section ARPv4.
  Require Import ARPPacket.

  Inductive fiat_arpv4_hardtype := Ethernet | IEEE802 | Chaos.
  Inductive fiat_arpv4_prottype := IPv4 | IPv6.
  Inductive fiat_arpv4_operation := Request | Reply | RARPRequest | RARPReply.

  Definition fiat_arpv4_decode := MakeDecoder (fst ARP_Packet_decoder).

  Definition fiat_arpv4_destruct_packet {A}
             (f: forall (HardType : fiat_arpv4_hardtype)
                   (ProtType : fiat_arpv4_prottype)
                   (Operation : fiat_arpv4_operation)
                   (SenderHardAddress : list char)
                   (SenderProtAddress : list char)
                   (TargetHardAddress : list char)
                   (TargetProtAddress : list char),
                 A)
             (packet: ARPPacket) : A :=
    f (InjectEnum [Ethernet; IEEE802; Chaos] packet!"HardType")
      (InjectEnum [IPv4; IPv6] packet!"ProtType")
      (InjectEnum [Request; Reply; RARPRequest; RARPReply] packet!"Operation")
      packet!"SenderHardAddress"
      packet!"SenderProtAddress"
      packet!"TargetHardAddress"
      packet!"TargetProtAddress".
End ARPv4.

Section IPv4.
  Require Import IPv4Header.

  Definition fiat_ipv4_decode := MakeDecoder IPv4_decoder_impl.

  Inductive fiat_ipv4_protocol :=
  | ICMP | TCP | UDP.

  Definition fiat_ipv4_protocol_to_enum (proto: fiat_ipv4_protocol) : EnumType ["ICMP"; "TCP"; "UDP"] :=
    match proto with
    | ICMP => ```"ICMP"
    | TCP => ```"TCP"
    | UDP => ```"UDP"
    end.

  Definition fiat_ipv4_construct_packet
             (TotalLength : (word 16))
             (ID : (word 16))
             (DF : bool)
             (MF : bool)
             (FragmentOffset : word 13)
             (TTL : char)
             (Protocol : fiat_ipv4_protocol)
             (SourceAddress : word 32)
             (DestAddress : word 32)
             (Options : list (word 32)) : IPv4_Packet :=
    <"TotalLength" :: TotalLength,
     "ID" :: ID,
     "DF" :: DF,
     "MF" :: MF,
     "FragmentOffset" :: FragmentOffset,
     "TTL" :: TTL,
     "Protocol" :: fiat_ipv4_protocol_to_enum Protocol,
     "SourceAddress" :: SourceAddress,
     "DestAddress" :: DestAddress,
     "Options" :: Options>.

  Definition fiat_ipv4_destruct_packet {A}
             (f: forall (TotalLength : (word 16))
                   (ID : (word 16))
                   (DF : bool)
                   (MF : bool)
                   (FragmentOffset : word 13)
                   (TTL : char)
                   (Protocol : fiat_ipv4_protocol)
                   (SourceAddress : word 32)
                   (DestAddress : word 32)
                   (Options : list (word 32)),
                 A)
              (packet : IPv4_Packet) : A :=
    f packet!"TotalLength"
      packet!"ID"
      packet!"DF"
      packet!"MF"
      packet!"FragmentOffset"
      packet!"TTL"
      (InjectEnum [ICMP; TCP; UDP] packet!"Protocol")
      packet!"SourceAddress"
      packet!"DestAddress"
      packet!"Options".
End IPv4.

Section TCP.
  Require Import TCP_Packet.

  Definition fiat_tcp_decode srcAddress dstAddress tcpLength :=
    MakeDecoder (TCP_Packet_decoder_impl srcAddress dstAddress tcpLength).

  Definition fiat_tcp_destruct_packet {A}
             (f: forall (SourcePort : word 16)
                   (DestPort : word 16)
                   (SeqNumber : word 32)
                   (AckNumber : word 32)
                   (NS : bool) (* ECN-nonce concealment protection flag *)
                   (CWR : bool) (* Congestion Window Reduced (CWR) flag *)
                   (ECE : bool) (* ECN-Echo flag *)
                   (ACK : bool) (* Acknowledgment field is significant flag *)
                   (PSH : bool) (* Push function flag *)
                   (RST : bool) (* Reset the connection flag *)
                   (SYN : bool) (* Synchronize sequence numbers flag *)
                   (FIN : bool) (* N srcAddress dstAddress udpLength o more data from sender flag*)
                   (WindowSize : word 16)
                   (UrgentPointer : option (word 16))
                   (Options : list (word 32))
                   (Payload : list char),
                 A)
             (packet: TCP_Packet) : A :=
    f packet!"SourcePort"
      packet!"DestPort"
      packet!"SeqNumber"
      packet!"AckNumber"
      packet!"NS"
      packet!"CWR"
      packet!"ECE"
      packet!"ACK"
      packet!"PSH"
      packet!"RST"
      packet!"SYN"
      packet!"FIN"
      packet!"WindowSize"
      packet!"UrgentPointer"
      packet!"Options"
      packet!"Payload".
End TCP.

Section UDP.
  Require Import UDP_Packet.

  Definition fiat_udp_decode srcAddress dstAddress udpLength :=
    MakeDecoder (UDP_Packet_decoder_impl srcAddress dstAddress udpLength).

  Definition fiat_udp_destruct_packet {A}
             (f: forall (SourcePort : word 16)
                   (DestPort : word 16)
                   (Payload : list char),
                 A)
             (packet: UDP_Packet) : A :=
    f packet!"SourcePort"
      packet!"DestPort"
      packet!"Payload".
End UDP.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

Extract Inductive prod => "(*)"  [ "(,)" ].

(** * Inline a few functions *)
Extraction Inline DecodeBindOpt2.
Extraction Inline If_Opt_Then_Else.
Extraction Inline decode_nat decode_word decode_word'.

(** * Extract words as int64
      (Only works for word length < 64) *)
Extract Constant whd => "(fun _ w -> ((Int64.logand Int64.one w) = Int64.one))".
Extract Constant wtl => "(fun _ w -> (Int64.shift_right_logical w 1))".
Extract Constant wplus => "(fun _ w w' -> Int64.add w w')".
Extract Constant wmult => "(fun _ w w' -> Int64.mul w w')".
Extract Constant wminus => "(fun _ w w' -> Int64.max (Int64.zero) (Int64.sub w w'))".
Extract Constant weq => "(fun _ w w' -> w = w')".
Extract Constant weqb => "(fun _ w w' -> w = w')".
Extract Constant wlt => "(fun _ w w' -> w < w')".
Extract Constant wlt_dec => "(fun _ w w' -> w < w')".
Extract Constant wand => "(fun _ w w' -> Int64.logand w w')".
Extract Constant wor => "(fun _ w w' -> Int64.logor w w')".
Extract Constant wnot => "(fun _ w -> Int64.lognot w)".
Extract Constant wneg => "(fun _ w w' -> failwith ""Called Wneg"")".
Extract Constant combine => "(fun _ w w' -> failwith ""Using combine"")".
Extract Constant wordToNat => "(fun _ w -> Int64.to_int w)". (* Not ideal *)
Extract Constant natToWord => "(fun _ w -> Int64.of_int w)".
Extract Constant wzero => "(fun _ -> Int64.zero)".
Extract Constant wzero' => "(fun _ -> Int64.zero)".
Extract Constant wones => "(fun n -> Int64.sub (Int64.shift_left Int64.one n) Int64.one)".

Extract Constant SW_word => "(fun sz b n -> Int64.add (if b then Int64.shift_left Int64.one sz else Int64.zero) n)".

Extract Inductive Word.word =>
int64 ["Int64.zero" "(fun (b, _, w') -> Int64.add (if b then Int64.one else Int64.zero) (Int64.shift_left w' 1))"]
      "failwith ""Destructing an int64""".

(** * Don't recurse on int64 *)
Extract Constant encode_word' => "encode_word'_recurse_on_size".

(** * Special case of internet checksum *)
Extract Constant InternetChecksum.add_bytes_into_checksum =>
"(fun b_hi b_lo checksum ->
    let oneC_plus w w' =
      let sum = Int64.add w w' in
      let mask = Int64.of_int 65535 in
      (Int64.add (Int64.logand sum mask)
                 (Int64.shift_right_logical sum 16))
    in oneC_plus (Int64.logor (Int64.shift_left b_hi 8) b_lo) checksum)".

Extract Constant InternetChecksum.OneC_plus => "failwith ""Calling OneC_plus""".

(** Efficient bit strings *)

Extract Inductive ByteString =>
  "BitString.t"
    ["(fun _ -> failwith ""Constructing a ByteString"")"]
    "(fun _ _ -> failwith ""Destructing a ByteString"")".

Extract Constant ByteString_id => "(BitString.create ())".
Extract Constant ByteString_enqueue => "BitString.enqueue".
Extract Constant ByteString_dequeue => "BitString.dequeue".
Extract Constant length_ByteString => "BitString.bitlength".
Extract Constant ByteString_enqueue_ByteString => "BitString.append".

Extraction "Fiat4Mirage"
           fiat_ethernet_decode
           fiat_ethernet_destruct_packet
           fiat_arpv4_decode
           fiat_arpv4_destruct_packet
           fiat_ipv4_decode
           fiat_ipv4_destruct_packet
           fiat_tcp_decode
           fiat_tcp_destruct_packet
           fiat_udp_decode
           fiat_udp_destruct_packet
           encode_word'_recurse_on_size.