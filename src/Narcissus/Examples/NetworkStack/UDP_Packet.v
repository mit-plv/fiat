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
      Payload : { n & ByteBuffer.t n } }.

  Definition UDP_Packet_Format
    : FormatM UDP_Packet ByteString :=
    (format_word ◦ SourcePort
     ++ format_word ◦ DestPort
     ++ format_nat 16 ◦ (Basics.compose (plus 8) (Basics.compose (projT1 (P := ByteBuffer.t)) Payload)))
    ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr udpLength (natToWord 8 17)) OfSize 16
    ThenCarryOn (format_bytebuffer ◦ Payload).

  (* The checksum takes three values provided by the IP header for
     checksum calculuation. *)
  Definition UDP_Packet_OK (udp : UDP_Packet) :=
    lt (projT1 (udp.(Payload))) (pow2 16 - 8).

  Ltac new_encoder_rules ::=
    eapply @CorrectAlignedEncoderForPseudoChecksumThenC;
    [ | | intros; calculate_length_ByteString'].

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

  Definition UDP_Packet_format_measure (udp_b : ByteString)
    : nat :=
    match (`(u, b') <- decode_unused_word' 16 udp_b;
             `(u, b') <- decode_unused_word' 16 b';
             decode_word' 16 b') with
    | Some n => wordToNat (fst n) * 8
    | None => 0
    end.

  (* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)

  Lemma UDP_Packet_Header_Len_OK
    : forall (a : UDP_Packet) (ctx ctx' ctx'' : CacheFormat) (c : word 16) (b b'' ext : ByteString),
      (format_word ◦ SourcePort ++ format_word ◦ DestPort ++ format_nat 16 ◦ Init.Nat.add 8 ∘ (projT1 (P:=ByteBuffer.t) ∘ Payload)) a
                                                                                                                                    ctx ∋ (b, ctx') ->
      (format_bytebuffer ◦ Payload) a ctx' ∋ (b'', ctx'') ->
      UDP_Packet_OK a ->
      (fun _ : UDP_Packet => 16 + (16 + 16)) a + (fun a' : UDP_Packet => 8 * projT1 (Payload a')) a + 16 =
      UDP_Packet_format_measure
        (mappend
           (mappend b
                    (mappend (format_checksum ByteString AlignedByteString.ByteStringQueueMonoid ByteString_QueueMonoidOpt 16 c) b'')) ext).
  Proof.
    intros; simpl.
    pose proof mappend_assoc as H''; simpl in H'';
      rewrite <- !H''.
    unfold UDP_Packet_format_measure.
    unfold sequence_Format at 1 in H.
    unfold sequence_Format at 1 in H.
    unfold compose, Bind2 in H.
    computes_to_inv; subst.
    destruct v; destruct v1; destruct v2.
    eapply EquivFormat_Projection_Format in H.
    unfold format_word in H; computes_to_inv; subst.
    eapply EquivFormat_Projection_Format in H'.
    unfold format_word in H'; computes_to_inv; subst; simpl in *.
    injections.
Admitted.


  (*eapply computes_to_compose_decode_unused_word in H;
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
      lt (8 + (projT1 (Payload data))) (pow2 16).
  Proof.
    unfold UDP_Packet_OK; intros.
    omega.
  Qed.

  Opaque pow2.

  Hint Resolve UDP_Packet_Header_Len_bound : data_inv_hints.

  Definition aligned_UDP_Packet_encoded_measure
             {sz} (ipv4_b : ByteBuffer.t sz)
     :=
    match nth_opt ipv4_b 4, nth_opt ipv4_b 5 with
    | Some n, Some m => Vector.cons _ n _ (Vector.cons _ m _ (Vector.nil _))
    | _, _ => Vector.cons _ (wzero _) _ (Vector.cons _ (wzero _) _ (Vector.nil _))
    end.

  Definition aligned_UDP_Packet_encoded_Len
             {sz} (v : ByteBuffer.t sz)
    : nat :=
    wordToNat (Word.combine (Vector.hd (aligned_UDP_Packet_encoded_measure v))
                            (Vector.hd (Vector.tl (aligned_UDP_Packet_encoded_measure v)))).

  Definition aligned_UDP_Packet_checksum {sz} :=
    @aligned_Pseudo_checksum srcAddr destAddr udpLength (natToWord 8 17) sz.

  Arguments GetCurrentBytes : simpl never.

  Ltac new_decoder_rules ::=
    match goal with
    | |- _ => intros; eapply unused_word_decode_correct; eauto
    | H : cache_inv_Property ?mnd _
      |- CorrectDecoder _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ =>
      eapply compose_PseudoChecksum_format_correct;
      [ repeat calculate_length_ByteString
      | repeat calculate_length_ByteString
      | exact H
      | solve_mod_8
      | solve_mod_8
      | apply UDP_Packet_Header_Len_OK
      | intros; NormalizeFormats.normalize_format ]
  end.

  (* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
  Definition UDP_Packet_Header_decoder
    : CorrectAlignedDecoderFor UDP_Packet_OK UDP_Packet_Format.
  Proof.
    start_synthesizing_decoder.
    NormalizeFormats.normalize_format.
    apply_rules.
    apply_rules.
    apply_rules.
    eapply (format_sequence_correct H2).
    apply Nat_decode_correct.
    simpl; intros;
      unfold Basics.compose.
    eapply UDP_Packet_Header_Len_bound; eauto; apply H3.
    intros; apply_rules.
    eapply (format_sequence_correct H4).
    intros; eapply @ByteBuffer_decode_correct with (n := s'1 - 8).
    repeat apply_rules.
    solve_side_condition.
    intros; apply_rules.
    cbv beta; synthesize_cache_invariant.
    (* Perform algebraic simplification of the decoder implementation. *)
    Opaque ByteString2ListOfChar.
    cbv beta; unfold decode_nat; optimize_decoder_impl.
    cbv beta; align_decoders.
    eapply @AlignedDecode_ifb_dep.
    intros; eapply (aligned_Pseudo_checksum_OK_1 _ _ _ _
                                                 (fun sz v => UDP_Packet_format_measure (build_aligned_ByteString v))); eauto.
    intros; eapply aligned_Pseudo_checksum_OK_2; eauto.
    align_decoders.
    eapply @AlignedDecodeByteBufferM; intros; eauto.
    align_decoders.
    align_decoders.
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
