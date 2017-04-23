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
        Fiat.BinEncoders.Env.Automation.Solver
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

Section UDP_Decoder.

  (* These values are provided by the IP header for checksum calculation.*)
  Variable srcAddr : word 32.
  Variable destAddr : word 32.
  Variable udpLength : word 16.

Definition UDP_Packet :=
  @Tuple <"SourcePort" :: word 16,
          "DestPort" :: word 16,
          "Payload" :: list char >.

Definition UDP_Checksum_Valid
           (srcAddr : word 32)
           (destAddr : word 32)
           (udpLength : word 16)
           (n : nat)
           (b : ByteString)
  := IPChecksum_Valid (96 + n)
                (transform (transform (encode_word srcAddr)
                (transform (encode_word destAddr)
                (transform (encode_word (wzero 8))
                (transform (encode_word (natToWord 8 17))
                           (encode_word udpLength)))))
                b).

Definition encode_UDP_Packet_Spec
           (udp : UDP_Packet) :=
          (encode_word_Spec (udp!"SourcePort")
    ThenC encode_word_Spec (udp!"DestPort")
    ThenC encode_nat_Spec 16 (8 + |udp!"Payload"|) DoneC)
    ThenChecksum (UDP_Checksum_Valid srcAddr destAddr udpLength) OfSize 16
    ThenCarryOn (encode_list_Spec encode_word_Spec udp!"Payload" DoneC).

Definition UDP_Packet_OK (udp : UDP_Packet) :=
lt (|udp!"Payload"|) (pow2 16 - 8).

Definition UDP_Packet_encoded_measure (udp_b : ByteString)
  : nat :=
  match (`(u, b') <- decode_unused_word' 16 udp_b;
         `(u, b') <- decode_unused_word' 16 b';
           decode_word' 16 b') with
  | Some n => 8 * wordToNat (fst n)
  | None => 0
  end.

Arguments NPeano.modulo : simpl never.

Opaque pow2.

Lemma UDP_Packet_Header_Len_OK
  : forall (a : UDP_Packet) (ctx ctx' ctx'' : CacheEncode) (c : word 16) (b b'' ext : ByteString),
    (encode_word_Spec (a!"SourcePort")
                      ThenC encode_word_Spec (a!"DestPort")
                      ThenC encode_nat_Spec 16 (8 + |a!"Payload"|) DoneC) ctx ↝
                                                                            (b, ctx') ->
    (encode_list_Spec encode_word_Spec a!"Payload" DoneC) ctx' ↝ (b'', ctx'') ->
    (lt (|a!"Payload"|) (pow2 16 - 8))%nat ->
    (fun _ : UDP_Packet => 16 + (16 + (16 + length_ByteString ByteString_id))) a +
    (fun a0 : UDP_Packet => (|a0!"Payload" |) * 8 + length_ByteString ByteString_id) a + 16 =
    UDP_Packet_encoded_measure
      (transform (transform b (transform (encode_checksum ByteString transformer ByteString_QueueTransformerOpt 16 c) b'')) ext).
Proof.
  unfold UDP_Packet_encoded_measure.
  intros; rewrite <- !transform_assoc.
  simpl in H0.
  eapply computes_to_compose_decode_unused_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold DecodeBindOpt, If_Opt_Then_Else.
  eapply computes_to_compose_decode_unused_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold DecodeBindOpt, If_Opt_Then_Else.
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
Qed.

Definition UDP_Packet_decoder
  : CorrectDecoderFor UDP_Packet_OK encode_UDP_Packet_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  apply_IPChecksum_dep UDP_Packet_Header_Len_OK.

  unfold UDP_Packet_OK; clear; intros ? H'; simpl; intuition eauto using lt_minus_plus.
  eapply lt_minus_plus with (m := 8); eauto.

  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  simpl; intros; intuition.
  decompose_pair_hyp.
  instantiate (1 := fst (snd (snd proj)) - 8);
    rewrite <- H4.
  auto with arith.
  decode_step idtac.
  decode_step idtac.

  synthesize_cache_invariant.
  repeat optimize_decoder_impl.

Defined.

Definition UDP_Packet_decoder_impl :=
  Eval simpl in (fst (projT1 UDP_Packet_decoder)).

End UDP_Decoder.

Print UDP_Packet_decoder_impl.
