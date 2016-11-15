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

(*Lemma if_computes_to_len {P}
  : forall (b : {P} + {~P}) b' encodeT encodeE n n' ctx ctx',
    (forall b ctx ctx', encodeT ctx ↝ (b, ctx') -> length_ByteString b = n)
    -> (forall b (ctx ctx' : CacheEncode), encodeE ctx ↝ (b, ctx') -> length_ByteString b = n')
    -> (if b then encodeT else encodeE) ctx ↝ (b', ctx')
    -> length_ByteString b' = if b then n else n'.
Proof.
  intros; find_if_inside; eauto.
Qed. *)

Arguments NPeano.modulo : simpl never.

Lemma lt_minus_plus :
  forall n m o,
    lt n (o - m) -> lt (m + n) o.
Proof.
  intros; omega.
Qed.

Lemma lt_minus_minus :
  forall n' n m o,
    lt m o
    -> n' = n - m
    -> lt n o -> lt n' (o - m).
Proof.
  intros; omega.
Qed.

Lemma lt_8_2_16 : lt 8 (pow2 16).
Proof.
  rewrite <- Npow2_nat.
  rewrite Compare_dec.nat_compare_lt.
  rewrite <- (Nnat.Nat2N.id 8) at 1.
  rewrite <- Nnat.N2Nat.inj_compare.
  reflexivity.
Qed.

Lemma lt_minus_plus_idem :
  forall n m o,
    lt m o
    -> lt n o
    -> lt (m + (n - m)) o.
Proof.
  intros; omega.
Qed.

Opaque pow2.

Definition UDP_Packet_decoder'
  : CorrectDecoderFor UDP_Packet_OK encode_UDP_Packet_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  eapply compose_IPChecksum_encode_correct_dep'.
  apply H.
  repeat resolve_Checksum.
  cbv beta; unfold Domain; simpl;
      simpl transform; unfold encode_word;
      rewrite !ByteString_enqueue_ByteString_measure,
      !length_encode_word';
      reflexivity.
  reflexivity.
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  solve_mod_8.
  solve_mod_8.
  { (* Grossest Proof By Far. *)
    intros; change transform_id with ByteString_id; rewrite length_ByteString_ByteString_id.
    instantiate (1 := UDP_Packet_encoded_measure).
    unfold UDP_Packet_encoded_measure.
    rewrite <- !transform_assoc.
    simpl in H0.
    eapply computes_to_compose_decode_unused_word in H0;
      let H' := fresh in
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold DecodeBindOpt, If_Opt_Then_Else.
    eapply computes_to_compose_decode_unused_word in H0;
      let H' := fresh in
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold DecodeBindOpt, If_Opt_Then_Else.
    eapply computes_to_compose_decode_word in H0;
      let H' := fresh in
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold fst.
    rewrite wordToNat_natToWord_idempotent; try reflexivity.
    rewrite !Plus.plus_assoc.
    clear.
    unfold StringId, StringId0, StringId1; clear.
    repeat match goal with
      |- context [ @length ?A (GetAttribute ?z ?l)] => remember (@length A (GetAttribute z l))
           end.
    repeat match goal with
      |- context [ @length ?A (prim_fst ?l)] => remember (@length A (prim_fst l))
    end.
    unfold GetAttribute, GetAttributeRaw in Heqn; simpl in Heqn.
    assert (n = n0).
    rewrite Heqn, Heqn0; reflexivity.
    rewrite H.
    omega.
    revert H2; clear; unfold UDP_Packet_OK; intros.
    unfold GetAttribute, GetAttributeRaw in H2; simpl in H2.
    match goal with
      |- context [ @length ?A (prim_fst ?l)] => remember (@length A (prim_fst l))
    end.
    rewrite <- BinNat.N.compare_lt_iff.
    rewrite Nnat.N2Nat.inj_compare.
    rewrite Nnat.Nat2N.id.
    rewrite <- Compare_dec.nat_compare_lt.
    rewrite Npow2_nat.
    omega.
  }
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  intros; eapply encode_decode_correct_finish.
  build_fully_determined_type.
  decide_data_invariant.
  unfold UDP_Packet_OK; clear; intros ? H'; repeat split.

  simpl; eapply lt_minus_plus with (m := 8); eauto.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.
  decode_step.
  decode_step.
  decode_step.

  simpl; intros; intuition.
  unfold GetAttribute, GetAttributeRaw in *; simpl.
  repeat
    match goal with
    | H : _ = _ |- _ =>
      first [apply decompose_pair_eq in H;
             let H1 := fresh in
             let H2 := fresh in
             destruct H as [H1 H2];
             simpl in H1;
             simpl in H2
            | rewrite H in * ]
    end; subst.
  instantiate (1 := fst (snd (snd proj)) - 8);
    rewrite <- H4.
  auto with arith.

  decode_step.
  decode_step.
  synthesize_cache_invariant.
  repeat optimize_decoder_impl.

Defined.

Definition UDP_Packet_decoder_impl :=
  Eval simpl in (fst (projT1 UDP_Packet_decoder')).

End UDP_Decoder.

Print UDP_Packet_decoder_impl.
