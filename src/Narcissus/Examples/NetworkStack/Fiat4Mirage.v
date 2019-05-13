Require Import Fiat.Narcissus.Examples.NetworkStack.TestInfrastructure.

Require Import
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignedEncodeMonad.

Open Scope string_scope.

Require Import Fiat.Common.EnumType.

Section Ethernet.
  Inductive fiat_ethernet_type := ARP | IP | IPV6 | RARP.

  Definition fiat_ethernet_type_of_enum (enum: EnumType ["ARP"; "IP"; "IPV6"; "RARP"]) : fiat_ethernet_type :=
    InjectEnum [ARP; IP; IPV6; RARP] enum.

  Definition fiat_ethernet_type_to_enum (type: fiat_ethernet_type) : EnumType ["ARP"; "IP"; "IPV6"; "RARP"] :=
    match type with
    | ARP => ```"ARP"
    | IP => ```"IP"
    | IPV6 => ```"IPV6"
    | RARP => ```"RARP"
    end.
End Ethernet.

Section ARP.
  Inductive fiat_arp_hardtype := Ethernet | IEEE802 | Chaos.
  Definition fiat_arp_hardtype_of_enum (enum: EnumType ["Ethernet"; "IEEE802"; "Chaos"]) :=
    InjectEnum [Ethernet; IEEE802; Chaos] enum.
  Definition fiat_arp_hardtype_to_enum (hardtype: fiat_arp_hardtype)
    : EnumType ["Ethernet"; "IEEE802"; "Chaos"] :=
    match hardtype with
    | Ethernet => ```"Ethernet"
    | IEEE802 => ```"IEEE802"
    | Chaos => ```"Chaos"
    end.

  Inductive fiat_arp_prottype := IPv4 | IPv6.
  Definition fiat_arp_prottype_of_enum (enum: EnumType ["IPv4"; "IPv6"]) :=
    InjectEnum [IPv4; IPv6] enum.
  Definition fiat_arp_prottype_to_enum (prottype: fiat_arp_prottype)
    : EnumType ["IPv4"; "IPv6"] :=
    match prottype with
    | IPv4 => ```"IPv4"
    | IPv6 => ```"IPv6"
    end.

  Inductive fiat_arp_operation := Request | Reply | RARPRequest | RARPReply.
  Definition fiat_arp_operation_of_enum (enum: EnumType ["Request"; "Reply"; "RARPRequest"; "RARPReply"]) :=
    InjectEnum [Request; Reply; RARPRequest; RARPReply] enum.
  Definition fiat_arp_operation_to_enum (operation: fiat_arp_operation)
    : EnumType ["Request"; "Reply"; "RARPRequest"; "RARPReply"] :=
    match operation with
    | Request => ```"Request"
    | Reply => ```"Reply"
    | RARPRequest => ```"RARPRequest"
    | RARPReply => ```"RARPReply"
    end.
End ARP.

Section IPv4.
  Inductive fiat_ipv4_protocol :=
  | ICMP | TCP | UDP.
  Definition fiat_ipv4_protocol_of_enum (proto: EnumType ["ICMP"; "TCP"; "UDP"]) : fiat_ipv4_protocol :=
    InjectEnum [ICMP; TCP; UDP] proto.
  Definition fiat_ipv4_protocol_to_enum (proto: fiat_ipv4_protocol)
    : EnumType ["ICMP"; "TCP"; "UDP"] :=
    match proto with
    | ICMP => ```"ICMP"
    | TCP => ```"TCP"
    | UDP => ```"UDP"
    end.
End IPv4.

Require Import Narcissus.OCamlExtraction.Extraction.

Extract Inductive Vector.t =>
"StackVector.t"
  ["StackVector.empty ()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inductive VectorDef.t =>
"StackVector.t"
  ["StackVector.empty ()" "StackVector.cons"]
  "StackVector.destruct".

Extract Inlined Constant Vector.nth => "StackVector.nth".
Extract Inlined Constant VectorDef.nth => "StackVector.nth".
Extract Inlined Constant Vector_nth_opt => "StackVector.nth_opt".
Extract Inlined Constant EnumOpt.word_indexed => "StackVector.index".

(*
Extract Inductive Vector.t =>
"ArrayVector.storage_t"
  ["ArrayVector.empty ()" "ArrayVector.cons"]
  "ArrayVector.destruct_storage".
Extract Inductive VectorDef.t =>
"ArrayVector.storage_t"
  ["ArrayVector.empty ()" "ArrayVector.cons"]
  "ArrayVector.destruct_storage".

Extract Inlined Constant Vector.hd => "ArrayVector.hd".
Extract Inlined Constant VectorDef.hd => "ArrayVector.hd".
Extract Inlined Constant Vector.tl => "ArrayVector.tl".
Extract Inlined Constant VectorDef.tl => "ArrayVector.tl".
Extract Inlined Constant Vector.to_list => "ArrayVector.to_list".
Extract Inlined Constant VectorDef.to_list => "ArrayVector.to_list".
Extract Inlined Constant Vector.append => "ArrayVector.append".
Extract Inlined Constant VectorDef.append => "ArrayVector.append".
Extract Inlined Constant Vector.nth => "ArrayVector.nth".
Extract Inlined Constant VectorDef.nth => "ArrayVector.nth".
Extract Inlined Constant Vector.replace => "ArrayVector.set_nth".
Extract Inlined Constant VectorDef.replace => "ArrayVector.set_nth".
Extract Inlined Constant Vector_nth_opt => "ArrayVector.nth_opt".
Extract Inlined Constant EnumOpt.word_indexed => "ArrayVector.index".

Extract Inlined Constant nth_opt => "ArrayVector.nth_opt".
Extract Inlined Constant set_nth' => "ArrayVector.set_nth".
Extract Inlined Constant InternetChecksum.ByteBuffer_fold_left_pair => "ArrayVector.fold_left_pair".
Extract Inlined Constant AlignedList.buffer_blit_buffer => "ArrayVector.blit_array".
Extract Inlined Constant AlignedList.bytebuffer_of_bytebuffer_range =>
  "(fun sz from len v ->
    let b = ArrayVector.array_of_range sz from len v in
    ExistT (ArrayVector.length b, b))".
*)

Extraction "Fiat4Mirage"

           fiat_ethernet_type_of_enum
           fiat_ethernet_type_to_enum
           fiat_ethernet_encode
           fiat_ethernet_decode
           fiat_arp_hardtype_of_enum
           fiat_arp_hardtype_to_enum
           fiat_arp_prottype_of_enum
           fiat_arp_prottype_to_enum
           fiat_arp_operation_of_enum
           fiat_arp_operation_to_enum
           fiat_arp_decode
           fiat_arp_encode
           fiat_ipv4_protocol_of_enum
           fiat_ipv4_protocol_to_enum
           fiat_ipv4_decode
           fiat_ipv4_encode
           fiat_tcp_encode
           fiat_tcp_decode
           fiat_udp_encode
           fiat_udp_decode

           projT2
           existT.

