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
Open Scope format_scope.
Opaque pow2. (* Don't want to be evaluating this. *)
Opaque natToWord. (* Or this. *)

(* Start Example Derivation. *)

Record ARPPacket :=
  {HardType : EnumType ["Ethernet"; "802"; "Chaos"];
   ProtType : EnumType ["IPv4"; "IPv6"]; (* Overlaps with etherType. *)
   Operation : EnumType ["Request";
                           "Reply";
                           "RARP Request";
                           "RARP Reply"];
   SenderHardAddress : list (word 8);
   SenderProtAddress : list (word 8);
   TargetHardAddress : list (word 8);
   TargetProtAddress : list (word 8)}.

Definition HardTypeCodes : Vector.t (word 16) 3 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~1
  ].

Definition EtherTypeCodes : Vector.t (word 16) 2 :=
  [WO~0~0~0~0~1~0~0~0~0~0~0~0~0~0~0~0;
   WO~1~0~0~0~0~1~1~0~1~1~0~1~1~1~0~1
  ].

Definition HardSizeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~0~0~0~1~0
  ].

Definition ProtSizeCodes : Vector.t (word 8) 2 :=
  [WO~0~0~0~0~0~1~0~0;
   WO~0~0~0~1~0~0~0~0 ].

Definition OperationCodes : Vector.t (word 16) 4 :=
  [WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~1~1;
   WO~0~0~0~0~0~0~0~0~0~0~0~0~0~1~0~0
  ].

Definition ARPPacket_Format
  : FormatM ARPPacket ByteString :=
  format_enum HardTypeCodes ◦ HardType
    ++ format_enum EtherTypeCodes ◦ ProtType
    ++ format_word ◦ (Basics.compose (Vector.nth HardSizeCodes) HardType)
    ++ format_word ◦ (Basics.compose (Vector.nth ProtSizeCodes) ProtType)
    ++ format_enum OperationCodes ◦ Operation
    ++ format_list format_word ◦ SenderHardAddress
    ++ format_list format_word ◦ SenderProtAddress
    ++ format_list format_word ◦ TargetHardAddress
    ++ format_list format_word ◦ TargetProtAddress.

Definition ARP_Packet_OK (arp : ARPPacket) :=
  (|arp.(SenderHardAddress)|) = wordToNat HardSizeCodes[@arp.(HardType)]
  /\ (|arp.(SenderProtAddress)|) = wordToNat ProtSizeCodes[@arp.(ProtType)]
  /\ (|arp.(TargetHardAddress)|) = wordToNat HardSizeCodes[@arp.(HardType)]
  /\ (|arp.(TargetProtAddress)|) = wordToNat ProtSizeCodes[@arp.(ProtType)].

Arguments Vector.nth : simpl never.


  (* Step One: Synthesize an encoder and a proof that it is correct. *)
  Definition ARP_encoder :
    CorrectAlignedEncoderFor ARPPacket_Format.
  Proof.
    start_synthesizing_encoder.
    Ltac decompose_aligned_encoder :=
      first [
          eapply @CorrectAlignedEncoderForIPChecksumThenC
        | associate_for_ByteAlignment
        | apply @CorrectAlignedEncoderForThenC
        | apply @CorrectAlignedEncoderForDoneC].
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    Grab Existential Variables.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
  Defined.

  (* Step Two: Extract the encoder function, and have it start encoding
   at the      start of the provided ByteString [v]. *)
  Definition ARP_encoder_impl {sz} v r :=
    Eval simpl in (projT1 ARP_encoder sz v 0 r tt).
  Print ARP_encoder_impl.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition ARP_Packet_Header_decoder
  : CorrectAlignedDecoderFor ARP_Packet_OK ARPPacket_Format.
Proof.
  (* We have to use an extra lemma at the start, because of the 'exotic'
     IP Checksum. *)
  start_synthesizing_decoder.
  normalize_compose ByteStringQueueMonoid.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  unfold ARP_Packet_OK; intros; intuition; rewrite H8 in H4; eassumption.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  unfold ARP_Packet_OK; intros; intuition; rewrite H9 in H5; eassumption.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  unfold ARP_Packet_OK; intros; intuition; rewrite H15, H12; reflexivity.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  unfold ARP_Packet_OK; intros; intuition; rewrite H19, H13; reflexivity.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  cbv beta; synthesize_cache_invariant.
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  cbv beta; align_decoders.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Arguments GetCurrentBytes : simpl never.
Definition ARP_decoder_impl {sz} v :=
  Eval simpl in (projT1 ARP_Packet_Header_decoder sz v 0 ()).
