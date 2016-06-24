Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
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
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.Vector
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Start Example Derivation. *)

Definition IPv4_Packet :=
  @Tuple <"ID" :: word 16,
          "DF" :: bool, (* Don't fragment flag *)
          "MF" :: bool, (*  Multiple fragments flag *)
          "FragmentOffset" :: word 13,
          "TTL" :: char,
          "Protocol" :: BoundedString ["ICMP"; "TCP"; "UDP"],
          (* So many to choose from: http://www.iana.org/assignments/protocol-numbers/protocol-numbers.xhtml*)
          "SourceAddress" :: word 32,
          "DestAddress" :: word 32,
          "Options" :: list (word 32)>.

Definition ProtocolTypeCodes : Vector.t (word 16) 3 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~1~0~0~0~1
  ].

Variable IPChecksum : ByteString -> ByteString.

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition encode_IPv4_Packet_Spec (ip4 : IPv4_Packet) (payload_len : nat) :=
          encode_word_Spec (natToWord 4 4)
    ThenC encode_nat_Spec 4 (5 + |ip4!"Options"|)
    ThenC encode_nat_Spec 4 (5 + |ip4!"Options"| + payload_len) (* payload length is an argument *)
    ThenC encode_word_Spec ip4!"ID"
    ThenC (Either encode_word_Spec WO~1 Or encode_word_Spec WO~0) (* Unused flag! *)
    ThenC encode_word_Spec (WS ip4!"DF" WO)
    ThenC encode_word_Spec (WS ip4!"MF" WO)
    ThenC encode_word_Spec ip4!"FragmentOffset"
    ThenC encode_word_Spec ip4!"TTL"
    ThenChecksum IPChecksum
    ThenCarryOn encode_word_Spec ip4!"SourceAddress"
    ThenC encode_word_Spec ip4!"DestAddress"
    ThenC encode_list_Spec encode_word_Spec ip4!"Options".
