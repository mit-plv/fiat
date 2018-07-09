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
(* Start Example Derivation. *)
Section TCPPacketDecoder.

  Record TCP_Packet :=
    {SourcePort : word 16;
     DestPort : word 16;
     SeqNumber : word 32;
     AckNumber : word 32;
     NS : bool; (* ECN-nonce concealment protection flag *)
     CWR : bool; (* Congestion Window Reduced (CWR) flag *)
     ECE : bool; (* ECN-Echo flag *)
    (* We can infer the URG flag from the Urgent Pointer field *)
     ACK : bool; (* Acknowledgment field is significant flag *)
     PSH : bool; (* Push function flag *)
     RST : bool; (* Reset the connection flag *)
     SYN : bool; (* Synchronize sequence numbers flag *)
     FIN : bool; (* No more data from sender flag*)
     WindowSize : word 16;
     UrgentPointer : option (word 16);
     Options : list (word 32);
     Payload : list (word 8)}.

  (* These values are provided by the IP header for checksum calculation.*)

  (* These values are provided by the IP header for checksum calculation.*)
  Variable srcAddr : Vector.t (word 8) 4.
  Variable destAddr : Vector.t (word 8) 4.
  Variable tcpLength : Vector.t (word 8) 2.

  Definition TCP_Packet_Format
    : FormatM TCP_Packet ByteString  :=
         (format_word ◦ SourcePort
          ++ format_word ◦ DestPort
          ++ format_word ◦ SeqNumber
          ++ format_word ◦ AckNumber
          ++ format_nat 4 ◦ (Basics.compose (plus 5) (Basics.compose (@length _) Options))
          ++ format_unused_word 3 (* These bits are reserved for future use. *)
          ++ format_bool ◦ NS
          ++ format_bool ◦ CWR
          ++ format_bool ◦ ECE
          ++ format_bool ◦ (Basics.compose (fun x => match x with
                                                     | Some _ => true
                                                     | _ => false
                                                     end) UrgentPointer)
          ++ format_bool ◦ ACK
          ++ format_bool ◦ PSH
          ++ format_bool ◦ RST
          ++ format_bool ◦ SYN
          ++ format_bool ◦ FIN
          ++ format_word ◦ WindowSize)
          ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr tcpLength (natToWord 8 6)) OfSize 16
          ThenCarryOn (Option.format_option format_word (@format_unused_word 16 _ _ _ _ _ _) ◦ UrgentPointer
                                            ++ format_list format_word ◦ Options
                                            ++ format_list format_word ◦ Payload).

  Definition TCP_Packet_OK (tcp : TCP_Packet) :=
    lt (|tcp.(Options)|) 11
    /\ wordToNat (Core.append_word (Vector.hd tcpLength) (Vector.hd (Vector.tl tcpLength)))
       = 20 (* length of packet header *)
         + (4 * |tcp.(Options)|) (* length of option field *)
         + (|tcp.(Payload)|).

  Local Arguments NPeano.modulo : simpl never.

  Definition TCP_Length :=
    (fun _ : ByteString => wordToNat (Core.append_word (Vector.hd tcpLength) (Vector.hd (Vector.tl tcpLength))) * 8).

  (* Step One: Synthesize an encoder and a proof that it is correct. *)
  Definition TCP_encoder :
    CorrectAlignedEncoderFor TCP_Packet_Format.
  Proof.
    start_synthesizing_encoder.
    eapply @CorrectAlignedEncoderForPseudoChecksumThenC.
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
  Admitted.

  (* Step Two: Extract the encoder function, and have it start encoding
     at the start of the provided ByteString [v]. *)
  Definition UDP_encoder_impl r {sz} v :=
    Eval simpl in (projT1 TCP_encoder sz v 0 r tt).

(* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)

Opaque pow2.
Arguments andb : simpl never.

Arguments GetCurrentBytes : simpl never.
(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition UDP_Packet_Header_decoder
  : CorrectAlignedDecoderFor TCP_Packet_OK TCP_Packet_Format.
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
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  simpl. admit.
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
  eapply unused_word_decode_correct.
  simpl; instantiate (1 := true); simpl; admit.
  simpl.
  destruct a'; simpl; decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  simpl. instantiate (1:= 0); admit.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  simpl. instantiate (1:= 0); admit.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  cbv beta; synthesize_cache_invariant.
  (* Perform algebraic simplification of the decoder implementation. *)
  cbv beta; optimize_decoder_impl.
  cbv beta.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  (* Need decoder for options. *)


Defined.

  Lemma TCP_Packet_Header_Len_OK
    : forall (tcp : TCP_Packet) (ctx ctx' ctx'' : CacheFormat) (c : word 16) (b b'' ext : ByteString),
      (      format_word (tcp!"SourcePort")
          ++ format_word (tcp!"DestPort")
          ++ format_word (tcp!"SeqNumber")
          ++ format_word (tcp!"AckNumber")
          ++ format_nat 4 (5 + |tcp!"Options"|)
          ++ format_unused_word 3 (* These bits are reserved for future use. *)
          ++ format_bool tcp!"NS"
          ++ format_bool tcp!"CWR"
          ++ format_bool tcp!"ECE"
          ++ format_bool (match tcp!"UrgentPointer" with
                                  | Some _ => true
                                  | _ => false
                                  end)
          ++ format_bool tcp!"ACK"
          ++ format_bool tcp!"PSH"
          ++ format_bool tcp!"RST"
          ++ format_bool tcp!"SYN"
          ++ format_bool tcp!"FIN"
          ++ format_word tcp!"WindowSize" DoneC) ctx ↝ (b, ctx') ->
      (format_option format_word (format_unused_word' 16 ByteString_id) tcp!"UrgentPointer"
       ++ format_list format_word tcp!"Options"
       ++ format_list format_word tcp!"Payload" DoneC) ctx' ↝ (b'', ctx'') ->
      (lt (|tcp!"Options"|) 11
       /\ wordToNat tcpLength = 20 (* length of packet header *)
                                + (4 * |tcp!"Options"|) (* length of option field *)
                                + (|tcp!"Payload"|)) ->
      (fun _ : TCP_Packet =>
    16 +
    (16 + (32 + (32 + (4 + (3 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (16 + length_ByteString ByteString_id))))))))))))))))
     tcp +
   (fun a0 : TCP_Packet =>
    16 + ((|a0!"Options"|) * 32 + ((|a0!"Payload" |) * 8 + length_ByteString ByteString_id))) tcp + 16 =
    (TCP_Length
       (mappend (mappend b (mappend (format_checksum ByteString monoid ByteString_QueueMonoidOpt 16 c) b'')) ext)).
Proof.
  intros.
  intros; change mempty with ByteString_id; rewrite length_ByteString_ByteString_id.
  unfold TCP_Length; rewrite (proj2 H1).
  match goal with
    |- context [ @length ?A ?l] => remember (@length A l)
  end.
  match goal with
    |- context [ @length ?A ?l] => remember (@length A l)
  end.
  omega.
Qed.

Definition TCP_Packet_decoder'
  : CorrectDecoderFor TCP_Packet_OK format_TCP_Packet_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose monoid.
  apply_IPChecksum_dep TCP_Packet_Header_Len_OK.

  - unfold TCP_Packet_OK; intros ? H'; repeat split.
    simpl; destruct H'.
    unfold pow2; simpl in *.
    unfold GetAttribute, GetAttributeRaw in H0; simpl in H0.
    revert H0; clear; unfold StringId13; intros; omega.

  - decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.

    simpl in *. intros; split_and; decompose_pair_hyp.
    instantiate (1 := fst (snd (snd (snd (snd (snd (snd (snd (snd proj))))))))).

    first [ rewrite <- H12
          | rewrite <- H13 ].
    match goal with
      |- context [decides (negb match ?b with _ => _ end) (?b' = None) ] =>
      assert (b = b') as H' by reflexivity; rewrite H'; destruct b';
        simpl; intuition eauto
    end.
    discriminate.
    destruct a'; intros; exact I.

    decode_step idtac.
    decode_step idtac.
    decode_step idtac.

    simpl in *. intros; split_and. decompose_pair_hyp.
    simpl; intros; instantiate (1 := fst (snd (snd (snd (snd proj)))) - 5).
    intuition; subst; simpl; auto with arith.
    first [ rewrite <- H12
          | rewrite <- H11]; simpl in *; auto with arith.

    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.

    simpl in *; intros.
    do 4 destruct H3.
    split; eauto.
    instantiate (1 := (wordToNat tcpLength) - 20 - (4 * (fst (snd (snd (snd (snd proj)))) - 5))).
    first [ rewrite <- H6
          | rewrite <- H5].
    rewrite H7.
    unfold snd, fst.
    unfold GetAttribute, GetAttributeRaw in *; simpl in *.
    repeat match goal with
             |- context [ @length ?A (prim_fst ?l)] => remember (@length A (prim_fst l))
           end.
    assert (n = n1) by (subst; reflexivity).
    rewrite H8; clear; omega.

    decode_step idtac.
    decode_step idtac.

  - synthesize_cache_invariant.
  - optimize_decoder_impl.

    Time Defined.

  Definition TCP_Packet_decoder_impl :=
    Eval simpl in (fst (proj1_sig TCP_Packet_decoder')).

End TCPPacketDecoder.

Print TCP_Packet_decoder_impl.
