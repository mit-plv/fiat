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
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.SolverOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.IPChecksum.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Require Import
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad.

Open Scope string_scope.
Open Scope Tuple_scope.

Definition InjectEnum {n A}
           (gallina_constructors: VectorDef.t A n)
           (enum_member: Fin.t n) : A :=
  VectorDef.nth gallina_constructors enum_member.

Definition MakeDecoder {A B} sz
           (impl: forall {sz}, Vector.t char sz -> option (A * nat * B))
           (bs: Vector.t char sz) : option A :=
  match impl bs with
  | Some (pkt, _, _) => Some (pkt)
  | None => None
  end.

Definition MakeEncoder {A B} sz
           (impl: A -> forall {sz}, Vector.t char sz -> option (Vector.t char sz * nat * B))
           (pkt: A) (out: Vector.t char sz) : option (Vector.t char sz) :=
  match impl pkt out with
  | Some (out, _, _) => Some out
  | None => None
  end.

(* Section FormatWord. *)
(*   Context {B : Type}. *)
(*   Context {cache : Cache}. *)
(*   Context {cacheAddNat : CacheAdd cache nat}. *)
(*   Context {monoid : Monoid B}. *)
(*   Context {monoidUnit : QueueMonoidOpt monoid bool}. *)

(*   (* Extracting words as Int64 prevents us from recursing on them directly *) *)

(*   Fixpoint encode_word'_recurse_on_size (sz : nat) (w : word sz) (b' : B) {struct sz} : B. *)
(*   Proof. *)
(*     destruct sz. *)
(*     - apply b'. *)
(*     - apply (enqueue_opt (whd w) (encode_word'_recurse_on_size sz (wtl w) b')). *)
(*   Defined. *)

(*   Lemma format'_on_size_correct : *)
(*     forall sz w b', encode_word' sz w b' = encode_word'_recurse_on_size sz w b'. *)
(*   Proof. *)
(*     induction sz; dependent destruction w; intros; simpl. *)
(*     - reflexivity. *)
(*     - rewrite IHsz; reflexivity. *)
(*   Qed. *)
(* End FormatWord. *)

(* Section Ethernet. *)
(*   Require Import EthernetHeader. *)

(*   Inductive fiat_ethernet_type := ARP | IP | RARP. *)

(*   Definition fiat_ethernet_decode packet_length := MakeDecoder (fst (frame_decoder packet_length)). *)

(*   Definition List_of_vector {A n} (v: Vector.t A n) : list A := *)
(*     Vector.fold_right List.cons v nil. *)

(*   Definition fiat_ethernet_destruct_packet {A} *)
(*              (f: forall (Destination : list char) *)
(*                    (Source : list char) *)
(*                    (type : fiat_ethernet_type), *)
(*                  A) *)
(*              (packet: EthernetHeader) := *)
(*     f  (List_of_vector packet!"Destination") *)
(*        (List_of_vector packet!"Source") *)
(*        (InjectEnum [ARP; IP; RARP] packet!"Type"). *)
(* End Ethernet. *)

(* Section ARPv4. *)
(*   Require Import ARPPacket. *)

(*   Inductive fiat_arpv4_hardtype := Ethernet | IEEE802 | Chaos. *)
(*   Inductive fiat_arpv4_prottype := IPv4 | IPv6. *)
(*   Inductive fiat_arpv4_operation := Request | Reply | RARPRequest | RARPReply. *)

(*   Definition fiat_arpv4_decode := MakeDecoder (fst ARP_Packet_decoder). *)

(*   Definition fiat_arpv4_destruct_packet {A} *)
(*              (f: forall (HardType : fiat_arpv4_hardtype) *)
(*                    (ProtType : fiat_arpv4_prottype) *)
(*                    (Operation : fiat_arpv4_operation) *)
(*                    (SenderHardAddress : list char) *)
(*                    (SenderProtAddress : list char) *)
(*                    (TargetHardAddress : list char) *)
(*                    (TargetProtAddress : list char), *)
(*                  A) *)
(*              (packet: ARPPacket) : A := *)
(*     f (InjectEnum [Ethernet; IEEE802; Chaos] packet!"HardType") *)
(*       (InjectEnum [IPv4; IPv6] packet!"ProtType") *)
(*       (InjectEnum [Request; Reply; RARPRequest; RARPReply] packet!"Operation") *)
(*       packet!"SenderHardAddress" *)
(*       packet!"SenderProtAddress" *)
(*       packet!"TargetHardAddress" *)
(*       packet!"TargetProtAddress". *)
(* End ARPv4. *)

Section IPv4.
  Require Import Fiat.Narcissus.Examples.NetworkStack.IPv4Header.

  Definition fiat_ipv4_decode {sz} := MakeDecoder sz (@IPv4_decoder_impl).

  Inductive fiat_ipv4_protocol :=
  | ICMP | TCP | UDP.

  Definition fiat_ipv4_protocol_to_enum (proto: fiat_ipv4_protocol) : EnumType ["ICMP"; "TCP"; "UDP"] :=
    match proto with
    | ICMP => ```"ICMP"
    | TCP => ```"TCP"
    | UDP => ```"UDP"
    end.

  Definition fiat_ipv4_enum_to_protocol (proto: EnumType ["ICMP"; "TCP"; "UDP"]) : fiat_ipv4_protocol :=
    InjectEnum [ICMP; TCP; UDP] proto.

  Definition fiat_ipv4_encode {sz} := MakeEncoder sz (@IPv4_encoder_impl).
End IPv4.

(* Section TCP. *)
(*   Require Import TCP_Packet. *)

(*   Definition fiat_tcp_decode srcAddress dstAddress tcpLength := *)
(*     MakeDecoder (TCP_Packet_decoder_impl srcAddress dstAddress tcpLength). *)

(*   Definition fiat_tcp_destruct_packet {A} *)
(*              (f: forall (SourcePort : word 16) *)
(*                    (DestPort : word 16) *)
(*                    (SeqNumber : word 32) *)
(*                    (AckNumber : word 32) *)
(*                    (NS : bool) (* ECN-nonce concealment protection flag *) *)
(*                    (CWR : bool) (* Congestion Window Reduced (CWR) flag *) *)
(*                    (ECE : bool) (* ECN-Echo flag *) *)
(*                    (ACK : bool) (* Acknowledgment field is significant flag *) *)
(*                    (PSH : bool) (* Push function flag *) *)
(*                    (RST : bool) (* Reset the connection flag *) *)
(*                    (SYN : bool) (* Synchronize sequence numbers flag *) *)
(*                    (FIN : bool) (* N srcAddress dstAddress udpLength o more data from sender flag*) *)
(*                    (WindowSize : word 16) *)
(*                    (UrgentPointer : option (word 16)) *)
(*                    (Options : list (word 32)) *)
(*                    (Payload : list char), *)
(*                  A) *)
(*              (packet: TCP_Packet) : A := *)
(*     f packet!"SourcePort" *)
(*       packet!"DestPort" *)
(*       packet!"SeqNumber" *)
(*       packet!"AckNumber" *)
(*       packet!"NS" *)
(*       packet!"CWR" *)
(*       packet!"ECE" *)
(*       packet!"ACK" *)
(*       packet!"PSH" *)
(*       packet!"RST" *)
(*       packet!"SYN" *)
(*       packet!"FIN" *)
(*       packet!"WindowSize" *)
(*       packet!"UrgentPointer" *)
(*       packet!"Options" *)
(*       packet!"Payload". *)
(* End TCP. *)

(* Section UDP. *)
(*   Require Import UDP_Packet. *)

(*   Definition fiat_udp_decode srcAddress dstAddress udpLength := *)
(*     MakeDecoder (UDP_Packet_decoder_impl srcAddress dstAddress udpLength). *)

(*   Definition fiat_udp_destruct_packet {A} *)
(*              (f: forall (SourcePort : word 16) *)
(*                    (DestPort : word 16) *)
(*                    (Payload : list char), *)
(*                  A) *)
(*              (packet: UDP_Packet) : A := *)
(*     f packet!"SourcePort" *)
(*       packet!"DestPort" *)
(*       packet!"Payload". *)
(* End UDP. *)

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inlined Constant NPeano.ltb => "(<)".
Extract Inlined Constant NPeano.leb => "(<=)".

(** * Inline a few functions *)
Extraction Inline fst snd.
Extraction Inline If_Opt_Then_Else.
Extraction Inline BindAlignedDecodeM ReturnAlignedDecodeM ThrowAlignedDecodeM.
Extraction Inline AppendAlignedEncodeM ReturnAlignedEncodeM ThrowAlignedEncodeM.
(* Extraction Inline decode_nat decode_word decode_word'. *)

(** * Extract words as int64
      (Only works for words with length < 64) *)

Extract Inductive Word.word =>
"Int64Word.t"
  ["(Int64Word.w0)" "Int64Word.ws"]
  "Int64Word.destruct".

Extract Inlined Constant whd => "Int64Word.whd".
Extract Inlined Constant wtl => "Int64Word.wtl".
Extract Inlined Constant wplus => "Int64Word.wplus".
Extract Inlined Constant wmult => "Int64Word.wmult".
Extract Inlined Constant wminus => "Int64Word.wminus".
Extract Inlined Constant weq => "Int64Word.weq".
Extract Inlined Constant weqb => "Int64Word.weqb".
Extract Inlined Constant wlt => "Int64Word.wlt".
Extract Inlined Constant wlt_dec => "Int64Word.wlt_dec".
Extract Inlined Constant wand => "Int64Word.wand".
Extract Inlined Constant wor => "Int64Word.wor".
Extract Inlined Constant wnot => "Int64Word.wnot".
Extract Inlined Constant wneg => "Int64Word.wneg".
Extract Inlined Constant wordToNat => "Int64Word.wordToNat".
Extract Inlined Constant natToWord => "Int64Word.natToWord".
Extract Inlined Constant wzero => "Int64Word.wzero".
Extract Inlined Constant wzero' => "Int64Word.wzero'".
Extract Inlined Constant wones => "Int64Word.wones".

Extract Inlined Constant word_split_hd => "Int64Word.word_split_hd".
Extract Inlined Constant word_split_tl => "Int64Word.word_split_tl".
Extract Inlined Constant AlignWord.split1' => "Int64Word.split1'".
Extract Inlined Constant AlignWord.split2' => "Int64Word.split2'".
Extract Inlined Constant split1 => "Int64Word.split1".
Extract Inlined Constant split2 => "Int64Word.split2".
Extract Inlined Constant SW_word => "Int64Word.SW_word".
Extract Inlined Constant combine => "Int64Word.combine".
Extract Inlined Constant append_word => "Int64Word.append".

Definition word_split_hd_test := word_split_hd (natToWord 5 30).
Definition word_split_tl_test := wordToNat (word_split_tl (natToWord 5 30)).
Definition alignword_split1'_test := wordToNat (AlignWord.split1' 2 3 (natToWord 5 30)).
Definition alignword_split2'_test := wordToNat (AlignWord.split2' 2 3 (natToWord 5 30)).
Definition split1_test := wordToNat (split1 3 2 (natToWord 5 30)).
Definition split2_test := wordToNat (split2 3 2 (natToWord 5 30)).
Definition combine_test := wordToNat (combine (natToWord 5 30) (natToWord 7 14)).
Definition append_word_test := wordToNat (append_word (@natToWord 8 5) (@natToWord 12 126)).

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

(** Efficient bytestrings *)

Extract Inductive Fin.t =>
"ArrayVector.idx_t"
  ["ArrayVector.zero" "ArrayVector.succ"]
  "ArrayVector.destruct".

Extract Inductive Vector.t =>
"ArrayVector.storage_t"
  ["ArrayVector.empty ()" "ArrayVector.cons"]
  "ArrayVector.destruct_idx".
Extract Inductive VectorDef.t =>
"ArrayVector.storage_t"
  ["ArrayVector.empty ()" "ArrayVector.cons"]
  "ArrayVector.destruct_storage".

Extract Inlined Constant Vector.nth => "ArrayVector.nth".
Extract Inlined Constant VectorDef.nth => "ArrayVector.nth".
Extract Inlined Constant nth_opt => "ArrayVector.nth_opt".
Extract Inlined Constant set_nth' => "ArrayVector.set_nth".
Extract Inlined Constant word_indexed => "ArrayVector.index".
Extract Inlined Constant InternetChecksum.Vector_fold_left_pair => "ArrayVector.fold_left_pair".

Print InternetChecksum.Vector_checksum.

Extraction IPv4_encoder_impl.

Definition fiat_ipv4_decode_bench (_: unit) :=
  fiat_ipv4_decode bin_pkt.
Definition fiat_ipv4_decode_test := fiat_ipv4_decode_bench ().
Definition fiat_ipv4_decode_reference := Eval compute in fiat_ipv4_decode_test.

Definition fiat_ipv4_encode_bench (_: unit) :=
  fiat_ipv4_encode pkt (AlignedByteString.initialize_Aligned_ByteString 20).
Definition fiat_ipv4_encode_test := fiat_ipv4_encode_bench ().
Definition fiat_ipv4_encode_reference := Eval compute in fiat_ipv4_encode_test.

(* Definition should_fail := *)
(*   let bs := (AlignedByteString.initialize_Aligned_ByteString 20) in *)
(*   let bs' := set_nth' bs 10 (wone _) in *)
(*   let bs'' := set_nth' bs 10 (wone _) in *)
(*   (bs', bs''). *)

Extraction "Fiat4Mirage"
           (* fiat_ethernet_decode *)
           (* fiat_ethernet_destruct_packet *)
           (* fiat_arpv4_decode *)
           (* fiat_arpv4_destruct_packet *)

           word_split_hd_test
           word_split_tl_test
           split1_test
           split2_test
           alignword_split1'_test
           alignword_split2'_test
           combine_test
           append_word_test

           fiat_ipv4_decode
           fiat_ipv4_decode_bench
           fiat_ipv4_decode_test
           fiat_ipv4_decode_reference
           fiat_ipv4_encode
           fiat_ipv4_decode_bench
           fiat_ipv4_encode_test
           fiat_ipv4_encode_reference

           (* fiat_ipv4_destruct_packet *)
           (* fiat_tcp_decode *)
           (* fiat_tcp_destruct_packet *)
           (* fiat_udp_decode *)
           (* fiat_udp_destruct_packet *)
           (* encode_word'_recurse_on_size *)
.
