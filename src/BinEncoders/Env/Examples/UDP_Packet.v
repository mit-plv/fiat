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
           (srcAddr : word 32)
           (destAddr : word 32)
           (udpLength : word 16)
           (* These values are provided by the IP header for checksum calculation.*)
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
  : { decodePlusCacheInv |
      forall srcAddr destAddr udpLength,
      exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
         -> encode_decode_correct_f _ transformer UDP_Packet_OK (fun _ _ => True)
                                    (encode_UDP_Packet_Spec srcAddr destAddr udpLength)
                                    ((fst decodePlusCacheInv) srcAddr destAddr udpLength)
                                    (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  unfold encode_UDP_Packet_Spec; pose_string_ids.
  let p := (eval unfold Domain in (fun udp : UDP_Packet => (udp!StringId, (udp!StringId0, |udp!StringId1|)))) in
  let p := eval simpl in p in
      eapply (@compose_IPChecksum_encode_correct_dep
                UDP_Packet
                _
                _
                (word 16 * (word 16 * nat))
                _ _ _ H
                p
                UDP_Packet_OK
                _ _ _
                (fun data' : word 16 * (word 16 * nat) =>
                   (encode_word_Spec (fst data')
              ThenC encode_word_Spec (fst (snd data'))
              ThenC encode_nat_Spec 16 (8 + (snd (snd data')))
              DoneC))).
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
    assert (n = n0) by (rewrite Heqn, Heqn0; f_equal).
    rewrite <- H.
    omega.
    revert H2; clear; unfold UDP_Packet_OK; intros.
    revert H2;
      repeat match goal with
               |- context [ @length ?A (GetAttribute ?z ?l)] => remember (@length A (GetAttribute z l))
             end.
    assert (n = n0) by (rewrite Heqn, Heqn0; f_equal).
    rewrite <- H.
    intros; auto with arith.
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
  (* Automation needs updating here. *)
  let a' := fresh in
  intros a'; repeat destruct a' as [? a'].
    (* Show that it is determined by the constraints (equalities) *)
    (* inferred during parsing. *)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
    (* Decompose data predicate *) intuition.
  assert (H4 = proj1 - 8) as H' by omega; rewrite H' in *; clear H'.
  (* Substitute any inferred equalities *) clear H7. subst.
  (* And unify with original object *) reflexivity.
  (* This needs to be baked into decide_data_invariant *)
  decide_data_invariant.
  (* instantiate (1 := true); simpl.
  eapply (lt_minus_plus_idem proj1 8); auto.
  apply lt_8_2_16. *)
  unfold UDP_Packet_OK; clear; intros ? H'; repeat split.

  simpl; eapply lt_minus_plus with (m := 8); eauto.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.
  decode_step.
  decode_step.
  decode_step.
  (* curried data nonesense *)
  simpl; intros; instantiate (1 := snd (snd proj)).
  intuition; subst; simpl; auto with arith.
  decode_step.
  intros.
  intros; eapply encode_decode_correct_finish.

  let a' := fresh in
  intros a'; repeat destruct a' as [? a'].
    (* Show that it is determined by the constraints (equalities) *)
    (* inferred during parsing. *)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
    (* Decompose data predicate *) intuition.
  (* More currying problems. *)
  generalize (f_equal fst H8);
    generalize (f_equal snd H8); intros.
  generalize (f_equal fst H1);
    generalize (f_equal snd H1); intros; simpl in *.
  clear H8 H1.
  subst.

  (* And unify with original object *) reflexivity.
  decide_data_invariant.
  (* unfold UDP_Packet_OK.
  unfold GetAttribute, GetAttributeRaw; simpl.
  instantiate (1 := true).
  eapply lt_minus_minus; eauto using lt_8_2_16.
  rewrite <- H0; simpl; rewrite <- Minus.minus_n_O; reflexivity. *)
  synthesize_cache_invariant.
Defined.

Definition UDP_Packet_decoder_impl :=
  Eval simpl in (fst (projT1 UDP_Packet_decoder')).

Print UDP_Packet_decoder_impl.
