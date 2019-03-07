Require Import Fiat.Narcissus.Examples.NetworkStack.TestInfrastructure.

(* Require Import *)
(*         Fiat.Narcissus.BinLib.AlignedDecodeMonad *)
(*         Fiat.Narcissus.BinLib.AlignedEncodeMonad. *)

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

