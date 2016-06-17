Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Examples.DnsServer.Packet
        Fiat.Common.SumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.DomainNameOpt.

Require Import
        Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.

Definition EthernetFrame :=
  @Tuple <"Destination" :: Vector.t char 6,
          "Source" :: Vector.t char 6,
          "Type" :: BoundedString ["ARP"; "IP"; "RARP"],
          "Data" :: list char>.

  Definition EthernetFrame_Spec (p : EthernetFrame) :=
       encode_word_Spec p!"id"
  Then encode_word_Spec (WS p!"QR" WO)
  Then encode_enum_Spec Opcode_Ws p!"Opcode"
  Then encode_word_Spec (WS p!"AA" WO)
  Then encode_word_Spec (WS p!"TC" WO)
  Then encode_word_Spec (WS p!"RD" WO)
  Then encode_word_Spec (WS p!"RA" WO)
  Then encode_word_Spec (WS false (WS false (WS false WO))) (* 3 bits reserved for future use *)
  Then encode_enum_Spec RCODE_Ws p!"RCODE"
  Then encode_nat_Spec 16 1 (* length of question field *)
  Then encode_nat_Spec 16 (|p!"answers"|)
  Then encode_nat_Spec 16 (|p!"authority"|)
  Then encode_nat_Spec 16 (|p!"additional"|)
  Then encode_question_Spec p!"question"
  Then (encode_list_Spec encode_resource_Spec (p!"answers" ++ p!"additional" ++ p!"authority"))
  Done.
