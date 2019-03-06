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
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.SolverOpt
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Formats.Option
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.IPChecksum
        Fiat.Narcissus.Formats.WordOpt.

Require Import Bedrock.Word.

Import Vectors.Vector.VectorNotations.
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

Definition monoid : Monoid ByteString := ByteStringMonoid.

Definition format_ICMP_Echo_Spec
           (icmp : ICMP_Echo) :=
        format_word icmp!"ID"
  ThenC format_word icmp!"SeqNum"
  ThenC format_list format_word icmp!"Payload"
  DoneC.

Definition format_ICMP_Unreachable_Spec
           (icmp : ICMP_Unreachable) :=
        format_word (wzero 32)
  ThenC format_list format_word icmp!"Payload"
  DoneC.

Definition format_ICMP_SourceQuench_Spec
           (icmp : ICMP_SourceQuench) :=
        format_word (wzero 32)
  ThenC format_list format_word icmp!"Payload"
  DoneC.

Definition format_ICMP_Redirect_Spec
           (icmp : ICMP_Redirect) :=
        format_word icmp!"RouterIP"
  ThenC format_list format_word icmp!"Payload"
  DoneC.

Definition format_ICMP_RouterAdvertisement_Spec
           (icmp : ICMP_RouterAdvertisement) :=
        format_nat 8 (|icmp!"RoutersPlusPreferences"|)
  ThenC format_nat 8 2
  ThenC format_word icmp!"TTL"
  ThenC format_list (fun p => format_word (fst p) ThenC format_word (snd p)) icmp!"RoutersPlusPreferences"
  DoneC.

Definition format_ICMP_RouterSolicitation_Spec
           (icmp : unit) :=
  format_word (wzero 32)
  DoneC.

Definition format_ICMP_TimeExceeded_Spec
           (icmp : ICMP_TimeExceeded) :=
        format_word (wzero 32)
  ThenC format_list format_word icmp!"Payload"
  DoneC.

Definition format_ICMP_ParameterProblem_Spec
           (icmp : ICMP_ParameterProblem) :=
        format_word icmp!"Pointer"
  ThenC format_word (wzero 24)
  ThenC format_list format_word icmp!"Payload"
  DoneC.

Definition format_ICMP_Timestamp_Spec
           (icmp : ICMP_Timestamp) :=
        format_word icmp!"ID"
  ThenC format_word icmp!"SeqNum"
  ThenC format_word icmp!"Originate"
  ThenC format_word icmp!"Received"
  ThenC format_word icmp!"Transmit"
  DoneC.

Definition format_ICMP_AddressMask_Spec
           (icmp : ICMP_AddressMask) :=
        format_word icmp!"ID"
  ThenC format_word icmp!"SeqNum"
  ThenC format_word icmp!"SubnetMask".

Definition format_ICMP_Message_Spec
           (icmp : ICMP_Message) :=
          format_enum ICMP_Message_Codes (SumType_index ICMP_Message_Types icmp!"Message")
    ThenC format_word (icmp!"Code")
    ThenChecksum IPChecksum_Valid OfSize 16
    ThenCarryOn
    format_SumType ICMP_Message_Types
                        (icons format_ICMP_Echo_Spec
                        (icons format_ICMP_Unreachable_Spec
                        (icons format_ICMP_SourceQuench_Spec
                        (icons format_ICMP_Redirect_Spec
                        (icons format_ICMP_Echo_Spec
                        (icons format_ICMP_RouterAdvertisement_Spec
                        (icons format_ICMP_RouterSolicitation_Spec
                        (icons format_ICMP_TimeExceeded_Spec
                        (icons format_ICMP_ParameterProblem_Spec
                        (icons format_ICMP_Timestamp_Spec
                        (icons format_ICMP_Timestamp_Spec
                        (icons format_ICMP_AddressMask_Spec
                        (icons format_ICMP_AddressMask_Spec inil)))))))))))))
    icmp!"Message".
