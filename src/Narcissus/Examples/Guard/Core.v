Require Export BinNat.
Require Export Coq.Lists.List.
Export ListNotations.

Require Export Bedrock.Word.
Require Export Fiat.Common.EnumType.
Require Export Fiat.Narcissus.Formats.ByteBuffer.
Require Export Fiat.Narcissus.Examples.NetworkStack.IPv4Header.
Require Export Fiat.Narcissus.Examples.NetworkStack.UDP_Packet.
Require Export Fiat.Narcissus.Examples.NetworkStack.TCP_Packet.

Definition bytes := { n: nat & ByteBuffer.t n }.

Definition bytes_of_ByteBuffer {n} (bb: ByteBuffer.t n) : bytes :=
  existT _ n bb.

(* Results describe what the guard may do after processing a rule. *)
Inductive result := ACCEPT | DROP.

Definition ipv4Split {A} (k: forall (w1 w2 w3 w4: word 8), A) (addr: word 32) : A :=
  let w1 := split2 24 8 addr in
  let w2 := split1 8 8 (split2 16 16 addr) in
  let w3 := split1 8 16 (split2 8 24 addr) in
  let w4 := split1 8 24 addr in
  k w1 w2 w3 w4.

Definition ipv4ToList :=
  ipv4Split (fun w1 w2 w3 w4 => [w1; w2; w3; w4]).

Definition ipv4ToByteBuffer :=
  ipv4Split (fun w1 w2 w3 w4 => ByteBuffer.of_list [w1; w2; w3; w4]: ByteBuffer.t 4).

Definition WrapDecoder {A B C} (f: forall n, ByteBuffer.t n -> option (A * B * C)) :=
  fun (bs: bytes) =>
    match f _ (projT2 bs) with
    | Some pkt => Some (fst (fst pkt))
    | None => None
    end.

Definition ipv4_decode (bs: bytes) :=
  WrapDecoder (@IPv4_decoder_impl) bs.

Definition tcp_decode (hdr: IPv4_Packet) :=
  let src := ipv4ToByteBuffer hdr.(SourceAddress) in
  let dst := ipv4ToByteBuffer hdr.(DestAddress) in
  let offset := 20 + 4 * List.length hdr.(IPv4Header.Options) in
  let tcpLen := wordToNat hdr.(TotalLength) - offset in
  fun (bs: bytes) =>
    let bs' := AlignedByteBuffer.bytebuffer_of_bytebuffer_range offset tcpLen (projT2 bs) in
    WrapDecoder (@TCP_decoder_impl src dst (natToWord 16 tcpLen)) bs'.

Definition udp_decode (hdr: IPv4_Packet) :=
  let src := ipv4ToByteBuffer hdr.(SourceAddress) in
  let dst := ipv4ToByteBuffer hdr.(DestAddress) in
  let offset := 20 + 4 * List.length hdr.(IPv4Header.Options) in
  let tcpLen := wordToNat hdr.(TotalLength) - offset in
  fun (bs: bytes) =>
    let bs' := AlignedByteBuffer.bytebuffer_of_bytebuffer_range offset tcpLen (projT2 bs) in
    WrapDecoder (@UDP_decoder_impl src dst (natToWord 16 tcpLen)) bs'.
