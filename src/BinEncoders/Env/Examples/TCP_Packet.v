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
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.Option
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

Definition TCP_Packet :=
  @Tuple <"SourcePort" :: word 16,
          "DestPort" :: word 16,
          "SeqNumber" :: word 32,
          "AckNumber" :: word 32,
          "NS" :: bool, (* ECN-nonce concealment protection flag *)
          "CWR" :: bool, (* Congestion Window Reduced (CWR) flag *)
          "ECE" :: bool, (* ECN-Echo flag *)
          (* We can infer the URG flag from the Urgent Pointer field *)
          "ACK" :: bool, (* Acknowledgment field is significant flag *)
          "PSH" :: bool, (* Push function flag *)
          "RST" :: bool, (* Reset the connection flag *)
          "SYN" :: bool, (* Synchronize sequence numbers flag *)
          "FIN" :: bool, (* No more data from sender flag*)
          "WindowSize" :: word 16,
          "UrgentPointer" :: option (word 16),
          "Options" :: list (word 32),
          "Payload" :: list char >.

Variable IPChecksum : ByteString -> ByteString.

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition TCP_Checksum (* Dummy Checksum for now*)
           (srcAddr : word 32)
           (destAddr : word 32)
           (tcpLength : nat)
           (b : ByteString)
  := ByteString_id.

Definition encode_TCP_Packet_Spec
           (srcAddr : word 32)
           (destAddr : word 32)
           (tcpLength : nat)
           (* These values are provided by the IP header for checksum calculation.*)
           (tcp : TCP_Packet) :=
          encode_word_Spec (tcp!"SourcePort")
    ThenC encode_word_Spec (tcp!"DestPort")
    ThenC encode_word_Spec (tcp!"SeqNumber")
    ThenC encode_word_Spec (tcp!"AckNumber")
    ThenC encode_nat_Spec 4 (5 + |tcp!"Options"|)
    ThenC encode_unused_word_Spec 3 (* These bits are reserved for future use. *)
    ThenC encode_bool_Spec tcp!"NS"
    ThenC encode_bool_Spec tcp!"CWR"
    ThenC encode_bool_Spec tcp!"ECE"
    ThenC encode_option_Spec (fun _ => encode_bool_Spec true) (encode_bool_Spec false) tcp!"UrgentPointer"
    ThenC encode_bool_Spec tcp!"ACK"
    ThenC encode_bool_Spec tcp!"PSH"
    ThenC encode_bool_Spec tcp!"RST"
    ThenC encode_bool_Spec tcp!"SYN"
    ThenC encode_bool_Spec tcp!"FIN"
    ThenC encode_word_Spec tcp!"WindowSize"
    ThenChecksum (TCP_Checksum srcAddr destAddr tcpLength)
    ThenCarryOn encode_option_Spec encode_word_Spec (encode_unused_word_Spec 16) tcp!"UrgentPointer"
    ThenC encode_list_Spec encode_word_Spec tcp!"Options"
    ThenC encode_list_Spec encode_word_Spec tcp!"Payload".
