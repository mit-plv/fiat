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
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.NoCache
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

Definition transformer : Transformer ByteString := ByteStringQueueTransformer.

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

Definition encode_ARPPacket_Spec (arp : ARPPacket) :=
          encode_enum_Spec HardTypeCodes arp!"HardType"
    ThenC encode_enum_Spec EtherTypeCodes arp!"ProtType"
    ThenC encode_word_Spec HardSizeCodes[@arp!"HardType"]
    ThenC encode_word_Spec ProtSizeCodes[@arp!"ProtType"]
    ThenC encode_enum_Spec OperationCodes arp!"Operation"
    ThenC encode_list_Spec encode_word_Spec arp!"SenderHardAddress"
    ThenC encode_list_Spec encode_word_Spec arp!"SenderProtAddress"
    ThenC encode_list_Spec encode_word_Spec arp!"TargetHardAddress"
    ThenC encode_list_Spec encode_word_Spec arp!"TargetProtAddress"
    DoneC.

Definition ARP_Packet_OK (arp : ARPPacket) :=
  (|arp!"SenderHardAddress"|) = wordToNat HardSizeCodes[@arp!"HardType"]
  /\ (|arp!"SenderProtAddress"|) = wordToNat ProtSizeCodes[@arp!"ProtType"]
  /\ (|arp!"TargetHardAddress"|) = wordToNat HardSizeCodes[@arp!"HardType"]
  /\ (|arp!"TargetProtAddress"|) = wordToNat ProtSizeCodes[@arp!"ProtType"].

Arguments Vector.nth : simpl never.

Definition ARPPacket_decoder
  : CorrectDecoderFor ARP_Packet_OK encode_ARPPacket_Spec.
Proof.
  synthesize_decoder.
Defined.

Definition ARP_Packet_decoder :=
  Eval simpl in proj1_sig ARPPacket_decoder.
Print ARP_Packet_decoder.
