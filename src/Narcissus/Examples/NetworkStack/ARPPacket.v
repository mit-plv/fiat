Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

Definition monoid : Monoid ByteString := ByteStringQueueMonoid.

(* Start Example Derivation. *)

Definition ARPPacket :=
  @Tuple <"HardType" :: EnumType ["Ethernet"; "802"; "Chaos"],
          "ProtType" :: EnumType ["IPv4"; "IPv6"], (* Overlaps with etherType. *)
          "Operation" :: EnumType ["Request";
                                   "Reply";
                                   "RARP Request";
                                   "RARP Reply"],
          "SenderHardAddress" :: list char,
          "SenderProtAddress" :: list char,
          "TargetHardAddress" :: list char,
          "TargetProtAddress" :: list char >.

Definition HardTypeCodes : Vector.t (word 16) 3 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1
  ].

Definition EtherTypeCodes : Vector.t (word 16) 2 :=
  [WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0;
   WO~1~0~0~0~0~1~1~0~1~1~0~1~1~1~0~1
  ].

Definition HardSizeCodes : Vector.t char 3 :=
  [WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~1~0
  ].

Definition ProtSizeCodes : Vector.t char 2 :=
  [WO~0~0~0~0~0~1~0~0;
   WO~0~0~0~1~0~0~0~0 ].

Definition OperationCodes : Vector.t (word 16) 4 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
  ].

Definition format_ARPPacket_Spec (arp : ARPPacket) :=
          format_enum HardTypeCodes arp!"HardType"
    ThenC format_enum EtherTypeCodes arp!"ProtType"
    ThenC format_word HardSizeCodes[@arp!"HardType"]
    ThenC format_word ProtSizeCodes[@arp!"ProtType"]
    ThenC format_enum OperationCodes arp!"Operation"
    ThenC format_list format_word arp!"SenderHardAddress"
    ThenC format_list format_word arp!"SenderProtAddress"
    ThenC format_list format_word arp!"TargetHardAddress"
    ThenC format_list format_word arp!"TargetProtAddress"
    DoneC.

Definition ARP_Packet_OK (arp : ARPPacket) :=
  (|arp!"SenderHardAddress"|) = wordToNat HardSizeCodes[@arp!"HardType"]
  /\ (|arp!"SenderProtAddress"|) = wordToNat ProtSizeCodes[@arp!"ProtType"]
  /\ (|arp!"TargetHardAddress"|) = wordToNat HardSizeCodes[@arp!"HardType"]
  /\ (|arp!"TargetProtAddress"|) = wordToNat ProtSizeCodes[@arp!"ProtType"].

Arguments Vector.nth : simpl never.

Definition ARPPacket_decoder
  : CorrectDecoderFor ARP_Packet_OK format_ARPPacket_Spec.
Proof.
  synthesize_decoder.
Defined.

Definition ARP_Packet_decoder :=
  Eval simpl in proj1_sig ARPPacket_decoder.
Print ARP_Packet_decoder.
