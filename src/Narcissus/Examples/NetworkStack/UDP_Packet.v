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
  Variable srcAddr : Vector.t (word 8) 4.
  Variable destAddr : Vector.t (word 8) 4.
  Variable udpLength : word 16.

  Record UDP_Packet :=
    { SourcePort : word 16;
      DestPort : word 16;
      Payload : list (word 8)}.

  Definition UDP_Packet_Format
    : FormatM UDP_Packet ByteString :=
    (format_word ◦ SourcePort
     ++ format_word ◦ DestPort
     ++ format_nat 16 ◦ (Basics.compose (plus 8) (Basics.compose (@length _) Payload)))
    ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength (natToWord 8 17)) OfSize 16
    ThenCarryOn (format_list format_word ◦ Payload).

  (* The checksum takes three values provided by the IP header for
     checksum calculuation. *)
  Definition UDP_Packet_OK (udp : UDP_Packet) :=
    lt (|udp.(Payload)|) (pow2 16 - 8).

  (* Step One: Synthesize an encoder and a proof that it is correct. *)
  Definition UDP_encoder :
    CorrectAlignedEncoderFor UDP_Packet_Format.
  Proof.
    start_synthesizing_encoder.
    eapply @CorrectAlignedEncoderForPseudoChecksumThenC.
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    repeat align_encoder_step.
    eapply CorrectAlignedEncoderForFormat2Nat.
    simpl; eauto.
    simpl; eauto.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    intros; calculate_length_ByteString'.
  Defined.

  (* Step Two: Extract the encoder function, and have it start encoding
     at the start of the provided ByteString [v]. *)
  Definition UDP_encoder_impl r {sz} v :=
    Eval simpl in (projT1 UDP_encoder sz v 0 r tt).

(* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)

(*Lemma UDP_Packet_Header_Len_OK
  : forall (a : UDP_Packet) (ctx ctx' ctx'' : CacheFormat) (c : word 16) (b b'' ext : ByteString),
    (format_word (a.(SourcePort))
                      ThenC format_word (a.(DestPort))
                      ThenC format_nat 16 (8 + |a.(Payload)|) DoneC) ctx ↝
                                                                            (b, ctx') ->
    (format_list format_word a.(Payload) DoneC) ctx' ↝ (b'', ctx'') ->
    (lt (|a.(Payload)|) (pow2 16 - 8))%nat ->
    (fun _ : UDP_Packet => 16 + (16 + (16 + length_ByteString ByteString_id))) a +
    (fun a0 : UDP_Packet => (|a0.(Payload) |) * 8 + length_ByteString ByteString_id) a + 16 =
    UDP_Packet_formatd_measure
      (mappend (mappend b (mappend (format_checksum ByteString monoid ByteString_QueueMonoidOpt 16 c) b'')) ext).
Proof.
  unfold UDP_Packet_formatd_measure.
  intros; rewrite <- !mappend_assoc.
  simpl in H0.
  eapply computes_to_compose_decode_unused_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold DecodeBindOpt; unfold BindOpt at 1; unfold If_Opt_Then_Else.
  eapply computes_to_compose_decode_unused_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold DecodeBindOpt; unfold BindOpt at 1; unfold If_Opt_Then_Else.
  eapply computes_to_compose_decode_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold fst.
  rewrite wordToNat_natToWord_idempotent; try reflexivity.
  rewrite !Plus.plus_assoc.
  clear.
  rewrite length_ByteString_id.
  omega.
  rewrite <- BinNat.N.compare_lt_iff.
  rewrite Nnat.N2Nat.inj_compare.
  rewrite Nnat.Nat2N.id.
  rewrite <- Compare_dec.nat_compare_lt.
  rewrite Npow2_nat.
  omega.
Qed. *)

Lemma UDP_Packet_Header_Len_bound
  : forall data : UDP_Packet,
    UDP_Packet_OK data ->
    lt (8 + (| Payload data |)) (pow2 16).
Proof.
  unfold UDP_Packet_OK; intros.
  omega.
Qed.

Opaque pow2.

Hint Resolve UDP_Packet_Header_Len_bound : data_inv_hints.

Arguments GetCurrentBytes : simpl never.
(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition UDP_Packet_Header_decoder
  : CorrectAlignedDecoderFor UDP_Packet_OK UDP_Packet_Format.
Proof.
  (* We have to use an extra lemma at the start, because of the 'exotic'
     IP Checksum. *)
  eapply CorrectAlignedDecoderForUDPChecksumThenC.
  repeat calculate_length_ByteString.
  (* Once that's done, the normal automation works just fine :) *)
  start_synthesizing_decoder.
  match goal with
  | |- CorrectDecoder ?monoid _ _ _ _ _ => normalize_compose monoid
  end.
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
  simpl; intros; intuition; instantiate (1 := proj1 -8); omega.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  cbv beta; synthesize_cache_invariant.
  (* Perform algebraic simplification of the decoder implementation. *)
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  cbv beta; align_decoders.
  Grab Existential Variables.
  shelve.
  synthesize_cache_invariant.
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
