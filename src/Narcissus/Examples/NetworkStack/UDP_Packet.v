Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.

Section UDP_Decoder.

  Open Scope format_scope.

  (* These values are provided by the IP header for checksum calculation.*)
  Variable srcAddr : ByteBuffer.t 4.
  Variable destAddr : ByteBuffer.t 4.
  Variable udpLength : word 16.

  Record UDP_Packet :=
    { SourcePort : word 16;
      DestPort : word 16;
      Payload : { n : _ & ByteBuffer.t n } }.

  Definition UDP_Packet_Format
    : FormatM UDP_Packet ByteString :=
    (format_word ◦ SourcePort
     ++ format_word ◦ DestPort
     ++ format_nat 16 ◦ (plus 8) ◦ projT1 (P := ByteBuffer.t) ◦ Payload)
    ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength (natToWord 8 17)) OfSize 16
    ThenCarryOn (format_bytebuffer ◦ Payload).

  (* The checksum takes three values provided by the IP header for
     checksum calculuation. *)
  Definition UDP_Packet_OK (udp : UDP_Packet) :=
    lt (projT1 (udp.(Payload))) (pow2 16 - 8).

  Ltac new_encoder_rules ::=
    eapply @CorrectAlignedEncoderForPseudoChecksumThenC;
    [ normalize_encoder_format
    | normalize_encoder_format
    | intros; calculate_length_ByteString'].

  (* Step One: Synthesize an encoder and a proof that it is correct. *)
  Definition UDP_encoder :
    CorrectAlignedEncoderFor UDP_Packet_Format.
  Proof.
    synthesize_aligned_encoder.
  Defined.

  (* Step Two: Extract the encoder function, and have it start encoding
     at the start of the provided ByteString [v]. *)
  Definition UDP_encoder_impl r {sz} v :=
    Eval simpl in (projT1 UDP_encoder sz v 0 r tt).

  (* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)
  Ltac apply_new_combinator_rule ::=
    match goal with
    | H : cache_inv_Property ?mnd _
      |- CorrectDecoder _ _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ _ =>  eapply compose_PseudoChecksum_format_correct';
      [ repeat calculate_length_ByteString
      | repeat calculate_length_ByteString
      | exact H
      | solve_mod_8
      | solve_mod_8
      | normalize_format; apply_rules
      | normalize_format; apply_rules
      | solve_Prefix_Format ]
  end.

  (* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
  Definition UDP_Packet_Header_decoder
    : CorrectAlignedDecoderFor UDP_Packet_OK UDP_Packet_Format.
  Proof.
    synthesize_aligned_decoder.
  Defined.

  (* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)

  Definition UDP_decoder_impl {sz} v :=
    Eval simpl in (projT1 UDP_Packet_Header_decoder sz v 0 ()).

End UDP_Decoder.

Print UDP_decoder_impl.

(*Definition udp_packet :=
 {| SourcePort := natToWord 16 1; DestPort := natToWord 16 2;
    Payload := List.map (natToWord 8) [7; 8; 7; 8] |}.

Definition w0 := wzero 8.
Definition len := natToWord 16 (8 + List.length udp_packet.(Payload)).
Definition localhost := Vector.map (natToWord 8) [127; 0; 0; 1].
Definition bs := AlignedByteString.initialize_Aligned_ByteString 12.
Compute (UDP_encoder_impl localhost localhost [split1 8 8 len; split2 8 8 len] udp_packet bs). *)

(*    = Some
        (WO~0~0~0~0~0~0~0~0
         :: WO~0~0~0~0~0~0~0~1
            :: WO~0~0~0~0~0~0~0~0
               :: WO~0~0~0~0~0~0~1~0
                  :: WO~0~0~0~0~0~0~0~0
                     :: WO~0~0~0~0~1~1~0~0
                        :: WO~0~0~0~0~0~0~0~0
                           :: WO~0~0~0~0~0~0~0~0
                              :: WO~0~0~0~0~0~1~1~1
                                 :: WO~0~0~0~0~1~0~0~0
                                    :: WO~0~0~0~0~0~1~1~1
                                       :: WO~0~0~0~0~1~0~0~0
                                          :: WO~1~1~1~0~1~1~1~0 :: WO~0~0~0~0~0~0~0~0 :: [WO~1~1~0~0~0~1~0~1], 15,
        ()) *)
