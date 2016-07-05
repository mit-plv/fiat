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
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt
        Fiat.BinEncoders.Env.Lib2.IPChecksum.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Start Example Derivation. *)

Definition ICMP_Unreachable :=
  @Tuple <"Payload" :: list char >. (* IP Header + first 64 bits of original datagram. *)

Definition ICMP_TimeExceeded :=
  @Tuple <"Payload" :: list char >. (* IP Header + first 64 bits of original datagram. *)

Definition ICMP_ParameterProblem :=
  @Tuple <"Pointer" :: char,
          "Payload" :: list char >. (* IP Header + first 64 bits of original datagram. *)

Definition ICMP_SourceQuench :=
  @Tuple <"Payload" :: list char >. (* IP Header + first 64 bits of original datagram. *)

Definition ICMP_Redirect :=
  @Tuple <"RouterIP" :: word 32, (* IP Address of the router to use *)
          "Payload" :: list char >. (* IP Header + first 64 bits of original datagram. *)

Definition ICMP_Echo :=
  @Tuple <"ID" :: word 16, (* Identifier for sender *)
          "SeqNum" :: word 16, (* Identifier for request *)
          "Payload" :: list char>. (* Optional data to be echoed. *)

Definition ICMP_Timestamp :=
  @Tuple <"ID" :: word 16, (* Identifier for sender *)
          "SeqNum" :: word 16, (* Identifier for request *)
          "Originate" :: word 32, (* Time request sent *)
          "Received" :: word 32, (*  Time request received *)
          "Transmit" :: word 32>. (*  Time reply sent *)

Definition ICMP_AddressMask :=
  @Tuple <"ID" :: word 16, (* Identifier for sender *)
          "SeqNum" :: word 16, (* Identifier for request *)
          "SubnetMask" :: word 32>. (* The subnet mask of interest. *)

Definition ICMP_RouterAdvertisement :=
  @Tuple <"TTL" :: word 16, (* Time to Live for the provided router information. *)
          "RoutersPlusPreferences" :: list (word 32 * word 32)>. (* Pairs of a router's IP address *)
                                                                 (* and its preference level. *)

Definition ICMP_Message_Types :=
    [ ICMP_Echo; (* Echo Reply *)
      ICMP_Unreachable; (* Destiniation unreachable *)
      ICMP_SourceQuench; (* Source Quence *)
      ICMP_Redirect; (* Redirect *)
      ICMP_Echo; (* Echo Request *)
      ICMP_RouterAdvertisement; (* Router Advertisement *)
      (unit : Type) ; (* Router Solicitation *)
      ICMP_TimeExceeded; (* Time Exceeded *)
      ICMP_ParameterProblem; (* Parameter Problem *)
      ICMP_Timestamp; (* Timestamp Request *)
      ICMP_Timestamp; (* Timestamp Reply *)
      ICMP_AddressMask; (* Address Mask Request *)
      ICMP_AddressMask]. (* Address Mask Reply *)

Definition ICMP_Message_Codes :=
  Eval simpl in
    [natToWord 8 0;
     natToWord 8 3;
     natToWord 8 4;
     natToWord 8 5;
     natToWord 8 8;
     natToWord 8 9;
     natToWord 8 10;
     natToWord 8 11;
     natToWord 8 12;
     natToWord 8 13;
     natToWord 8 14;
     natToWord 8 17;
     natToWord 8 18].

Definition ICMP_Message :=
  @Tuple <"Code" :: char, "Message" :: SumType ICMP_Message_Types>.

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition encode_ICMP_Echo_Spec
           (icmp : ICMP_Echo) :=
        encode_word_Spec icmp!"ID"
  ThenC encode_word_Spec icmp!"SeqNum"
  ThenC encode_list_Spec encode_word_Spec icmp!"Payload"
  DoneC.

Definition encode_ICMP_Unreachable_Spec
           (icmp : ICMP_Unreachable) :=
        encode_word_Spec (wzero 32)
  ThenC encode_list_Spec encode_word_Spec icmp!"Payload"
  DoneC.

Definition encode_ICMP_SourceQuench_Spec
           (icmp : ICMP_SourceQuench) :=
        encode_word_Spec (wzero 32)
  ThenC encode_list_Spec encode_word_Spec icmp!"Payload"
  DoneC.

Definition encode_ICMP_Redirect_Spec
           (icmp : ICMP_Redirect) :=
        encode_word_Spec icmp!"RouterIP"
  ThenC encode_list_Spec encode_word_Spec icmp!"Payload"
  DoneC.

Definition encode_ICMP_RouterAdvertisement_Spec
           (icmp : ICMP_RouterAdvertisement) :=
        encode_nat_Spec 8 (|icmp!"RoutersPlusPreferences"|)
  ThenC encode_nat_Spec 8 2
  ThenC encode_word_Spec icmp!"TTL"
  ThenC encode_list_Spec (fun p => encode_word_Spec (fst p) ThenC encode_word_Spec (snd p)) icmp!"RoutersPlusPreferences"
  DoneC.

Definition encode_ICMP_RouterSolicitation_Spec
           (icmp : unit) :=
  encode_word_Spec (wzero 32)
  DoneC.

Definition encode_ICMP_TimeExceeded_Spec
           (icmp : ICMP_TimeExceeded) :=
        encode_word_Spec (wzero 32)
  ThenC encode_list_Spec encode_word_Spec icmp!"Payload"
  DoneC.

Definition encode_ICMP_ParameterProblem_Spec
           (icmp : ICMP_ParameterProblem) :=
        encode_word_Spec icmp!"Pointer"
  ThenC encode_word_Spec (wzero 24)
  ThenC encode_list_Spec encode_word_Spec icmp!"Payload"
  DoneC.

Definition encode_ICMP_Timestamp_Spec
           (icmp : ICMP_Timestamp) :=
        encode_word_Spec icmp!"ID"
  ThenC encode_word_Spec icmp!"SeqNum"
  ThenC encode_word_Spec icmp!"Originate"
  ThenC encode_word_Spec icmp!"Received"
  ThenC encode_word_Spec icmp!"Transmit"
  DoneC.

Definition encode_ICMP_AddressMask_Spec
           (icmp : ICMP_AddressMask) :=
        encode_word_Spec icmp!"ID"
  ThenC encode_word_Spec icmp!"SeqNum"
  ThenC encode_word_Spec icmp!"SubnetMask".

Definition encode_ICMP_Message_Spec
           (icmp : ICMP_Message) :=
          encode_enum_Spec ICMP_Message_Codes (SumType_index ICMP_Message_Types icmp!"Message")
    ThenC encode_word_Spec (icmp!"Code")
    ThenChecksum IPChecksum_Valid OfSize 16
    ThenCarryOn
    encode_SumType_Spec ICMP_Message_Types
                        (icons encode_ICMP_Echo_Spec
                        (icons encode_ICMP_Unreachable_Spec
                        (icons encode_ICMP_SourceQuench_Spec
                        (icons encode_ICMP_Redirect_Spec
                        (icons encode_ICMP_Echo_Spec
                        (icons encode_ICMP_RouterAdvertisement_Spec
                        (icons encode_ICMP_RouterSolicitation_Spec
                        (icons encode_ICMP_TimeExceeded_Spec
                        (icons encode_ICMP_ParameterProblem_Spec
                        (icons encode_ICMP_Timestamp_Spec
                        (icons encode_ICMP_Timestamp_Spec
                        (icons encode_ICMP_AddressMask_Spec
                        (icons encode_ICMP_AddressMask_Spec inil)))))))))))))
    icmp!"Message".
