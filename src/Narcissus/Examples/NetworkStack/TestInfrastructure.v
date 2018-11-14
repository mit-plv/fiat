Require Export Bedrock.Word.

Require Import
        Fiat.Narcissus.Examples.NetworkStack.EthernetHeader
        Fiat.Narcissus.Examples.NetworkStack.ARPPacket
        Fiat.Narcissus.Examples.NetworkStack.IPv4Header
        Fiat.Narcissus.Examples.NetworkStack.TCP_Packet
        Fiat.Narcissus.Examples.NetworkStack.UDP_Packet.

Require Coq.Vectors.VectorDef.
Export Coq.Vectors.VectorDef.VectorNotations.

(* Require Export *)
(*         Fiat.Common.SumType *)
(*         Fiat.Common.EnumType *)
(*         Fiat.Common.BoundedLookup *)
(*         Fiat.Common.ilist *)
(*         Fiat.Computation *)
(*         Fiat.QueryStructure.Specification.Representation.Notations *)
(*         Fiat.QueryStructure.Specification.Representation.Heading *)
(*         Fiat.QueryStructure.Specification.Representation.Tuple *)
(*         Fiat.Narcissus.BinLib.Core *)
(*         Fiat.Narcissus.BinLib.AlignedByteString *)
(*         Fiat.Narcissus.Common.Specs *)
(*         Fiat.Narcissus.Common.WordFacts *)
(*         Fiat.Narcissus.Common.ComposeCheckSum *)
(*         Fiat.Narcissus.Common.ComposeIf *)
(*         Fiat.Narcissus.Common.ComposeOpt *)
(*         Fiat.Narcissus.Automation.SolverOpt *)
(*         Fiat.Narcissus.Formats.FixListOpt *)
(*         Fiat.Narcissus.Stores.EmptyStore *)
(*         Fiat.Narcissus.Formats.WordOpt *)
(*         Fiat.Narcissus.Formats.Bool *)
(*         Fiat.Narcissus.Formats.NatOpt *)
(*         Fiat.Narcissus.Formats.Vector *)
(*         Fiat.Narcissus.Formats.EnumOpt *)
(*         Fiat.Narcissus.Formats.SumTypeOpt *)
(*         Fiat.Narcissus.Formats.IPChecksum. *)

Definition InjectEnum {n A}
           (gallina_constructors: VectorDef.t A n)
           (enum_member: Fin.t n) : A :=
  VectorDef.nth gallina_constructors enum_member.

Require Import AlignedByteString.

Definition WrapDecoder {A B} sz
           (impl: forall {sz}, ByteBuffer.t sz -> option (A * nat * B))
           (bs: ByteBuffer.t sz) : option A :=
  match impl bs with
  | Some (pkt, _, _) => Some pkt
  | None => None
  end.

Definition WrapEncoder {A B} sz
           (impl: forall {sz}, ByteBuffer.t sz -> A -> option (ByteBuffer.t sz * nat * B))
           (pkt: A) (out: ByteBuffer.t sz) : option (ByteBuffer.t sz) :=
  match impl out pkt with
  | Some (out, _, _) => Some out
  | None => None
  end.

Definition IsSome {A} (x: option A) :=
  match x with Some _ => True | None => False end.

Definition must {A} (x: option A) (pr: IsSome x) : A :=
  match x as xx return (IsSome xx -> A) with
  | Some a => fun _ => a
  | None => fun pr => False_rect _ pr
  end pr.

Definition MakeBuffer sz := AlignedByteString.initialize_Aligned_ByteString sz.
Definition FreshBuffer {sz} (len: nat) (v: ByteBuffer.t sz) := AlignedByteString.initialize_Aligned_ByteString len.

Definition fiat_ethernet_encode {sz} :=
  WrapEncoder sz (fun sz v pkt => @EthernetHeader_encoder_impl pkt sz v).
Definition fiat_ethernet_decode {sz} v packet_length :=
  WrapDecoder sz (@Ethernet_decoder_impl packet_length) v.

Definition fiat_arp_decode {sz} :=
  WrapDecoder sz (@ARP_decoder_impl).
Definition fiat_arp_encode {sz} :=
  WrapEncoder sz (@ARP_encoder_impl).

Definition fiat_ipv4_decode {sz} :=
  WrapDecoder sz (@IPv4_decoder_impl).
Definition fiat_ipv4_encode {sz} :=
  WrapEncoder sz (@IPv4_encoder_impl).

Definition fiat_tcp_encode {sz} v srcAddress dstAddress tcpLength :=
  WrapEncoder sz (fun sz v pkt => @TCP_encoder_impl srcAddress dstAddress tcpLength pkt sz v) v.
Definition fiat_tcp_decode {sz} v (srcAddress dstAddress: Vector.t (word 8) 4) tcpLength :=
  WrapDecoder sz (@TCP_decoder_impl srcAddress dstAddress tcpLength) v.

Definition fiat_udp_encode {sz} v srcAddress dstAddress udpLength :=
  WrapEncoder sz (fun sz v pkt => @UDP_encoder_impl srcAddress dstAddress udpLength pkt sz v) v.
Definition fiat_udp_decode {sz} v (srcAddress dstAddress: Vector.t (word 8) 4) (udpLength: word 16) :=
  WrapDecoder sz (@UDP_decoder_impl srcAddress dstAddress udpLength) v.
