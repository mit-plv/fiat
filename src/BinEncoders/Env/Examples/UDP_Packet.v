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
          "DestPort" :: word 16, (* Don't fragment flag *)
          "Payload" :: list char >.

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition UDP_Checksum_Valid
           (srcAddr : word 32)
           (destAddr : word 32)
           (udpLength : word 16)
           (n : nat)
           (b : ByteString)
  := IPChecksum_Valid (96 + n)
                (transform (transform (encode_word' 32 srcAddr)
                (transform (encode_word' 32 destAddr)
                (transform (encode_word' 8 (wzero 8))
                (transform (encode_word' 8 (natToWord 8 17))
                           (encode_word' 16 udpLength)))))
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
    ThenCarryOn (encode_list_Spec encode_word_Spec udp!"Payload"
             ThenC (if (Peano_dec.eq_nat_dec (NPeano.modulo (length udp!"Payload") 2) 0) then encode_word_Spec WO else encode_word_Spec (wzero 8))
                                  DoneC).

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

Lemma if_computes_to_len {P}
  : forall (b : {P} + {~P}) b' encodeT encodeE n n' ctx ctx',
    (forall b ctx ctx', encodeT ctx ↝ (b, ctx') -> length_ByteString b = n)
    -> (forall b (ctx ctx' : CacheEncode), encodeE ctx ↝ (b, ctx') -> length_ByteString b = n')
    -> (if b then encodeT else encodeE) ctx ↝ (b', ctx')
    -> length_ByteString b' = if b then n else n'.
Proof.
  intros; find_if_inside; eauto.
Qed.

Arguments NPeano.modulo : simpl never.

Lemma mod_16_even_8 :
  forall n,
    NPeano.modulo n 2 = 0
    -> NPeano.modulo (n * 8 + 0) 16 = 0.
Proof.
  intros; rewrite <- plus_n_O.
  rewrite Mult.mult_comm.
  pose proof (NPeano.Nat.mul_mod_distr_l n 2 8).
  unfold mult at 2 in H0; simpl in H0.
  rewrite H0, H; eauto.
Qed.

Lemma mod_16_odd_8 :
  forall n,
    NPeano.modulo n 2 <> 0
    -> NPeano.modulo (n * 8) 16 = 8.
Proof.
  intros; rewrite Mult.mult_comm.
  pose proof (NPeano.Nat.mul_mod_distr_l n 2 8).
  unfold mult at 2 in H0; simpl in H0.
  rewrite H0; eauto.
  pose proof (NPeano.Nat.mod_upper_bound n 2).
  omega.
Qed.

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
  eexists (_, _); intros; eexists _; split; simpl.
  unfold encode_UDP_Packet_Spec; pose_string_ids.
  intro.
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
  simpl transform; rewrite !transform_ByteString_measure, !length_encode_word';
    reflexivity.
  reflexivity.
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  intros. eapply if_computes_to_len; eauto;
            repeat calculate_length_ByteString.
  solve_mod_16.
  intros; cbv beta; find_if_inside.
  solve_mod_16.
  simpl; rewrite mod_16_even_8; eauto.
  solve_mod_16; simpl.
  intros; rewrite <- NPeano.Nat.add_mod_idemp_l; eauto.
  simpl; rewrite mod_16_odd_8; eauto.
  { (* Grossest Proof By Far. *)
    intros; simpl transform_id; rewrite length_ByteString_ByteString_id.
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
    find_if_inside.
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
    admit.
    clear; admit.
  }
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Nat_decode_correct.
  solve_data_inv.
  solve_data_inv.
  unfold encode_decode_correct_f; intuition eauto.
  simpl in *.
  instantiate
    (1 := fun p b env => if Compare_dec.le_lt_dec p (pow2 16) then
                           _ p b env else None).
  simpl in *.
  assert (b0 = proj1 - 8) by
      (rewrite <- H9; simpl; auto with arith).
  destruct (Compare_dec.le_lt_dec proj1 (pow2 16)).
  rewrite H8; clear H8.
  clear H9.
  computes_to_inv; injections; subst; simpl.
  eexists env'; simpl; intuition eauto.
  rewrite ByteString_transform_id_left.
  match goal with
    |- ?f ?a ?b ?c = ?P =>
    let P' := (eval pattern a, b, c in P) in
    let f' := match P' with ?f a b c => f end in
    try unify f f'; try reflexivity
  end.
  omega.
  simpl in H6.
  find_if_inside; try discriminate.
  simpl in H6; injections; eauto.
  simpl.
  eexists _; eexists tt;
    intuition eauto; injections; eauto using idx_ibound_eq;
      try match goal with
            |-  ?data => destruct data;
                           simpl in *; eauto
          end.
  destruct env; computes_to_econstructor.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  find_if_inside; simpl in *; try discriminate;
    injections.
  reflexivity.
  instantiate (1 := fun _ => True); eauto.
  find_if_inside; try discriminate; injections.
  clear; admit.
  find_if_inside; try discriminate; injections; eauto.
  find_if_inside; try discriminate; injections; eauto.
  find_if_inside; try discriminate; injections; eauto.
  clear; admit.
  unfold UDP_Packet_OK; clear; intros ? H'; repeat split.
  simpl.
  clear; admit.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.
  apply_compose.
  intro H'; eapply FixList_decode_correct.
  eapply Word_decode_correct.
  eapply H'.
  simpl; intros; instantiate (1 := snd (snd proj)).
  intuition.
  destruct proj as [? [? ?] ]; simpl; injections; eauto.
  simpl; intros; eauto using FixedList_predicate_rest_True.
  intros.

  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  intro; eapply FixList_decode_correct.
  revert H3; eapply Word_decode_correct.
  simpl in *; split.
  intuition eauto.
  eapply (f_equal fst H8).
  intros; eauto.
  simpl; intros; eauto using FixedList_predicate_rest_True.
  simpl; intros;
    unfold encode_decode_correct_f; intuition eauto.
  destruct data as [? [? [? [? [? [? [? [? [? [? [ ] ] ] ] ] ] ] ] ] ] ];
    unfold GetAttribute, GetAttributeRaw in *;
    simpl in *.
  pose proof (f_equal fst H14).
  pose proof (f_equal (fun z => fst (snd z)) H14).
  pose proof (f_equal (fun z => fst (snd (snd z))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd z)))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd z))))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd (snd z)))))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd (snd (snd z))))))) H14).
  pose proof (f_equal (fun z => fst (snd (snd (snd (snd (snd (snd z))))))) H14).
  pose proof (f_equal (fun z => snd (snd (snd (snd (snd (snd (snd z))))))) H14).
  simpl in *.
  clear H14.
  computes_to_inv; injections; subst; simpl.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  eexists env'; simpl; intuition eauto.
  simpl in *.
  simpl in H8; injections; eauto.
  simpl in H8; repeat find_if_inside; try discriminate.
  eexists _; eexists tt.
  injections; simpl in *; repeat split.
  destruct env; computes_to_econstructor.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  reflexivity.
  unfold GetAttribute, GetAttributeRaw; simpl.
  rewrite H5; eauto.
  intuition.
  simpl in *.
  unfold pow2 in H9; simpl in H9; auto with arith.
  omega.
  unfold GetAttribute, GetAttributeRaw.
  simpl.
  rewrite H5.
  omega.
  destruct proj as [? [? [? [? [? [? [? ?] ] ] ] ] ] ].
  simpl.
  unfold GetAttribute, GetAttributeRaw; simpl in *.
  repeat f_equal.
  eauto.
  simpl.
  repeat (instantiate (1 := fun _ => True)).
  unfold cache_inv_Property; intuition.
  Grab Existential Variables.
  decide equality.
  decide equality.
  exact (@weq _).
Defined.

Definition IPv4_decoder_impl :=
  Eval simpl in (fst (projT1 EthernetHeader_decoder)).

Print IPv4_decoder_impl.


Lemma UDP_Packet_Headiner_Len_Bound
  : forall (a : UDP_Packet) (a_OK : UDP_Packet_OK a),
    BinNat.N.lt (BinNat.N.of_nat (UDP_Packet_Header_Len a)) (Npow2 4).
Proof.
  unfold IPv4_Packet_Header_Len.
  intros; unfold IPv4_Packet_OK in a_OK.
  destruct a_OK.
  rewrite <- BinNat.N.compare_lt_iff.
  rewrite Nnat.N2Nat.inj_compare.
  rewrite Nnat.Nat2N.id.
  rewrite <- Compare_dec.nat_compare_lt.
  simpl.
  unfold BinPos.Pos.to_nat; simpl.
  auto with arith.
Qed.
