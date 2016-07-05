Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
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
        Fiat.BinEncoders.Env.Lib2.Bool
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

Definition IPv4_Packet :=
  @Tuple <"TotalLength" :: word 16,
          "ID" :: word 16,
          "DF" :: bool, (* Don't fragment flag *)
          "MF" :: bool, (*  Multiple fragments flag *)
          "FragmentOffset" :: word 13,
          "TTL" :: char,
          "Protocol" :: EnumType ["ICMP"; "TCP"; "UDP"],
          (* So many to choose from: http://www.iana.org/assignments/protocol-numbers/protocol-numbers.xhtml*)
          "SourceAddress" :: word 32,
          "DestAddress" :: word 32,
          "Options" :: list (word 32)>.

Definition ProtocolTypeCodes : Vector.t char 3 :=
  [WO~0~0~0~0~0~0~0~1;
   WO~0~0~0~0~0~1~1~0;
   WO~0~0~0~1~0~0~0~1
  ].

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition IPv4_Packet_Header_Len (ip4 : IPv4_Packet) := 5 + |ip4!"Options"|.

Definition encode_IPv4_Packet_Spec (ip4 : IPv4_Packet)  :=
          (encode_word_Spec (natToWord 4 4)
    ThenC encode_nat_Spec 4 (IPv4_Packet_Header_Len ip4)
    ThenC encode_unused_word_Spec 8 (* TOS Field! *)
    ThenC encode_word_Spec ip4!"TotalLength"
    ThenC encode_word_Spec ip4!"ID"
    ThenC encode_unused_word_Spec 1 (* Unused flag! *)
    ThenC encode_bool_Spec ip4!"DF"
    ThenC encode_bool_Spec ip4!"MF"
    ThenC encode_word_Spec ip4!"FragmentOffset"
    ThenC encode_word_Spec ip4!"TTL"
    ThenC encode_enum_Spec ProtocolTypeCodes ip4!"Protocol"
    DoneC)
    ThenChecksum IPChecksum_Valid OfSize 16
    ThenCarryOn (encode_word_Spec ip4!"SourceAddress"
    ThenC encode_word_Spec ip4!"DestAddress"
    ThenC encode_list_Spec encode_word_Spec ip4!"Options"
    DoneC).

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4!"Options"|) 11 /\
  lt (20 + 4 * |ipv4!"Options"|) (wordToNat ipv4!"TotalLength").

Definition IPv4_Packet_encoded_measure (ipv4_b : ByteString)
  : nat :=
  match (`(u, b') <- decode_unused_word' 4 ipv4_b;
           decode_word' 4 b') with
  | Some n => 32 * wordToNat (fst n)
  | None => 0
  end.

Arguments mult : simpl never.
Arguments decode_word' : simpl never.

Lemma IPv4_Packet_Headiner_Len_Bound
  : forall (a : IPv4_Packet) (a_OK : IPv4_Packet_OK a),
    BinNat.N.lt (BinNat.N.of_nat (IPv4_Packet_Header_Len a)) (Npow2 4).
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

(*Lemma IPv4_Packet_encoded_measure_OK_1 :
  forall (a : IPv4_Packet) (ctx ctx' : ()) (b ext : ByteString)
         (a_OK : IPv4_Packet_OK a),
    encode_IPv4_Packet_Spec a ctx ↝ (b, ctx')
    -> IPv4_Packet_encoded_measure (ByteString_transformer b ext)
       = 32 * (IPv4_Packet_Header_Len a).
Proof.
  unfold encode_IPv4_Packet_Spec; intros.
  unfold IPv4_Packet_encoded_measure;
  eapply computes_to_composeChecksum_decode_unused_word in H;
    let H' := fresh in
    destruct H as [? [? [? [? [? [? H'] ] ] ] ] ];
      rewrite H'; simpl.
  rewrite <- !ByteString_transform_assoc.
  intros.
  eapply computes_to_compose_decode_word in H;
    let H' := fresh in
    destruct H as [? [? [? H'] ] ]; rewrite H'.
  unfold fst.
  rewrite wordToNat_natToWord_idempotent; try reflexivity.
  eauto using IPv4_Packet_Headiner_Len_Bound.
Qed. (* Qed takes forever. *) *)

Definition EthernetHeader_decoder
  : { decodePlusCacheInv |
      exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
         -> encode_decode_correct_f _ transformer IPv4_Packet_OK (fun _ _ => True)
                                    encode_IPv4_Packet_Spec
                                    (fst decodePlusCacheInv) (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  eexists (_, _); intros; eexists _; split; simpl.
  unfold encode_IPv4_Packet_Spec; pose_string_ids.
  intro.
  let p := (eval unfold Domain in (fun ip4 : IPv4_Packet => (|ip4!StringId11|, (ip4!StringId, (ip4!StringId0, (ip4!StringId1,
                                                                                                               (ip4!StringId2, (ip4!StringId3, (ip4!StringId4, ip4!StringId5))))))))) in
  let p := eval simpl in p in
      eapply (@compose_IPChecksum_encode_correct
                IPv4_Packet
                (nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))))
                _ _ _ H
                p
                IPv4_Packet_OK
                _ _ _
                (fun data' : nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))) =>
                   (encode_word_Spec (natToWord 4 4)
                                   ThenC encode_nat_Spec 4 (5 + fst data')
                                   ThenC encode_unused_word_Spec 8 (* TOS Field! *)
                                   ThenC encode_word_Spec (fst (snd data'))
                                   ThenC encode_word_Spec (fst (snd (snd data')))
                                   ThenC encode_unused_word_Spec 1
                                   ThenC encode_bool_Spec (fst (snd (snd (snd data'))))
                                   ThenC encode_bool_Spec (fst (snd (snd (snd (snd data')))))
                                   ThenC encode_word_Spec (fst (snd (snd (snd (snd (snd data'))))))
                                   ThenC encode_word_Spec (fst (snd (snd (snd (snd (snd (snd data')))))))
                                   ThenC encode_enum_Spec ProtocolTypeCodes (snd (snd (snd (snd (snd (snd (snd data')))))))
                                   DoneC))).
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  solve_mod_8.
  solve_mod_8.
  { (* Grossest Proof By Far. *)
    intros; simpl transform_id; rewrite length_ByteString_ByteString_id.
    instantiate (1 := IPv4_Packet_encoded_measure).
    unfold IPv4_Packet_encoded_measure.
    rewrite <- !transform_assoc.
    eapply computes_to_compose_decode_unused_word in H0;
      let H' := fresh in
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold DecodeBindOpt, If_Opt_Then_Else.
    eapply computes_to_compose_decode_word in H0;
      let H' := fresh in
      destruct H0 as [? [? [? H'] ] ]; rewrite H'.
    unfold fst.
    rewrite wordToNat_natToWord_idempotent; try reflexivity;
      eauto using IPv4_Packet_Headiner_Len_Bound.
    rewrite !Plus.plus_assoc.
    rewrite Mult.mult_plus_distr_l.
    clear.
    repeat match goal with
             |- context [length ?l] => remember (length l)
           end.
    assert (n = n0) by (rewrite Heqn, Heqn0; f_equal).
    rewrite H.
    omega. }
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Nat_decode_correct.
  solve_data_inv.
  solve_data_inv.
  unfold encode_unused_word_Spec.
  apply_compose.
  eapply unused_word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply unused_word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply bool_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply bool_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
  eapply Enum_decode_correct.
  Discharge_NoDupVector.
  solve_data_inv.
  solve_data_inv.
  unfold encode_decode_correct_f; intuition eauto.
  instantiate
    (1 := fun p b env => if Compare_dec.le_lt_dec proj 4 then None else _ p b env).
  simpl in *.
  rewrite <- H24; simpl.
  assert (a = proj - 5) by
      (rewrite <- H24; simpl; auto with arith).
  instantiate
    (1 := fun p b env => if Compare_dec.le_lt_dec (wordToNat proj0) (4 * proj) then None else _ p b env).
  rewrite H24; clear H24.
  revert H16.
  instantiate (2 := fun data : nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))) => lt (20 + 4 * (fst data)) (wordToNat (fst (snd data)))).
  rewrite H13, H23.
  simpl; intros.
  assert (~ le (wordToNat proj0) (4 * proj)) by omega.
  destruct (Compare_dec.le_lt_dec (wordToNat proj0) (4 * proj)).
  intuition.
  computes_to_inv; injections; subst; simpl.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  eexists env'; simpl; intuition eauto.
  instantiate (1 := fun proj6 ext env' => Some (proj - 5, (proj0, (proj1, (proj2, (proj3, (proj4, (proj5, proj6)))))), ext, env')).
  reflexivity.
  find_if_inside; try discriminate.
  find_if_inside; try discriminate.
  simpl in H14; injections; eauto.
  simpl in H14; repeat find_if_inside; try discriminate.
  injections.
  simpl.
  eexists _; eexists tt;
    intuition eauto; injections; eauto using idx_ibound_eq;
      try match goal with
            |-  ?data => destruct data;
                           simpl in *; eauto
          end.
  destruct env; computes_to_econstructor.
  pose proof transform_id_left as H'; simpl in H'; rewrite H'.
  reflexivity.
  omega.
  omega.
  omega.
  unfold IPv4_Packet_OK; clear; intros ? H'; destruct H' as [? ?]; repeat split.
  simpl.
  eassumption.
  simpl.
  revert H; unfold StringId11; unfold pow2, mult; simpl; auto with arith.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.
  apply_compose.
  eapply Word_decode_correct.
  solve_data_inv.
  solve_data_inv.
  apply_compose.
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

(* This is the decoder function that we should extract. *)

Definition IPv4_decoder_impl :=
  Eval simpl in (fst (projT1 EthernetHeader_decoder)).

Print IPv4_decoder_impl.

Definition pkt' : list char :=
  [WO~1~0~1~0~0~0~1~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~1~1~0~0~1~0~0;
   WO~1~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~0~0;
   WO~0~0~0~0~0~0~0~0;

   WO~0~0~0~0~0~0~1~1;
   WO~0~0~0~1~0~1~0~1;

   WO~0~1~1~1~1~0~1~1;
   WO~0~1~0~1~0~0~0~0;

   WO~0~0~0~0~0~0~1~1;
   WO~0~0~0~1~0~1~0~1;

   WO~0~1~1~1~1~0~1~1;
   WO~1~0~0~0~0~0~0~0]%list.

Definition pkt : list char :=
    Eval compute in map (@natToWord 8) [69;0;0;0;0;0;0;0;38;1;87;160;192;168;222;10;192;168;222;1].

Lemma zero_lt_eight : (lt 0 8)%nat.
  Proof. omega. Qed.

  Definition fiat_ipv4_decode (buffer: list char) : option (IPv4_Packet * list char) :=
    let bs := {| padding := 0; front := WO; paddingOK := zero_lt_eight; byteString := buffer |} in
    match IPv4_decoder_impl bs () with
    | Some (pkt, bs, _) => Some (pkt, bs.(byteString))
    | None => None
    end.

  Compute (fiat_ipv4_decode pkt).

  Compute (InternetChecksum.checksum pkt').
