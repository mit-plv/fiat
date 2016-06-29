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
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

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

Variable onesComplement : list char -> word 16.

Fixpoint transformer_pop_word {B}
         {transformer : Transformer B}
         {transformer_opt : TransformerUnitOpt transformer bool}
         (sz : nat)
         (b : B)
  : (word sz * B) :=
  match sz with
  | 0 => (WO, b)
  | S sz' =>
    match transform_pop_opt b with
    | Some (v, b') =>
      let (w', b'') := transformer_pop_word sz' b' in
      (WS v w', b'')
    | _ => (wzero (S sz'), b)
    end
  end.

Fixpoint ByteString2ListOfChar (n : nat)
           (b : ByteString) : list char :=
  match n with
  | 0 => nil
  | S n' =>
    let (c, b') := transformer_pop_word 8 b in
    cons c (ByteString2ListOfChar n' b')
  end.

Definition IPChecksum (b : ByteString) : ByteString :=
  encode_word' _ (onesComplement
                    match padding b with
                    | 0 => ByteString2ListOfChar (length (byteString b)) b
                    | _ => ByteString2ListOfChar (1 + length (byteString b)) b
                    end).

Definition transformer : Transformer ByteString := ByteStringTransformer.

Definition encode_IPv4_Packet_Spec (ip4 : IPv4_Packet)  :=
          (encode_word_Spec (natToWord 4 4)
    ThenC encode_nat_Spec 4 (5 + |ip4!"Options"|)
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
    ThenChecksum IPChecksum
    ThenCarryOn (encode_word_Spec ip4!"SourceAddress"
    ThenC encode_word_Spec ip4!"DestAddress"
    ThenC encode_list_Spec encode_word_Spec ip4!"Options"
    DoneC).

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4!"Options"|) 11 /\ lt (20 + 4 * |ipv4!"Options"|) (wordToNat ipv4!"TotalLength").

Definition IPChecksum_Valid (n : nat) (b : ByteString) : Prop :=
  onesComplement (ByteString2ListOfChar n b) = wones 16.

Definition IPChecksum_Valid_dec (n : nat) (b : ByteString)
  : {IPChecksum_Valid n b} + {~IPChecksum_Valid n b} := weq _ _.

Definition decode_IPChecksum
  : ByteString -> CacheDecode -> option (() * ByteString * CacheDecode) :=
  decode_unused_word 16.

Lemma IPChecksum_OK :
  forall (b ext : ByteString),
    IPChecksum_Valid (bin_measure (transform b (IPChecksum b)))
                     (transform (transform b (IPChecksum b)) ext).
Proof.
  simpl; intros.
Admitted.

Lemma IPChecksum_commute :
  forall (b b' : ByteString),
    IPChecksum (transform b b') = IPChecksum (transform b' b).
Proof.
  simpl; intros.
Admitted.

Lemma IPChecksum_Valid_commute :
  forall (b b' ext : ByteString),
    IPChecksum_Valid (bin_measure (transform b b')) (transform (transform b b') ext)
    <-> IPChecksum_Valid (bin_measure (transform b' b)) (transform (transform b' b) ext).
Admitted.

Definition IPv4_Packet_encoded_measure (ipv4_b : ByteString)
  : nat :=
  match (`(u, b') <- decode_unused_word' 4 ipv4_b;
           decode_word' 4 b') with
  | Some n => 32 * wordToNat (fst n)
  | None => 0
  end.

Lemma decode_IPChecksum_pf
  : forall (b b' ext : ByteString) (ctx ctx' ctxD : ()),
    True ->
    decode_IPChecksum (ByteString_transformer (ByteString_transformer (IPChecksum (ByteString_transformer b b')) b') ext) ctxD = Some ((), ByteString_transformer b' ext, ctxD).
Proof.
  intros; pose proof transform_assoc as H'; simpl in H'; rewrite <- H'; clear H'.
  unfold IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
  pose proof transformer_pop_encode_word' as H'; simpl in H'; rewrite H'; simpl; eauto.
Qed.

Lemma ByteString_pop_eq_push
  : forall b b' b'',
    ByteString_pop b = Some (b', b'')
    -> b = ByteString_push b' b''.
Proof.
  destruct b; unfold ByteString_pop; simpl.
  destruct padding; simpl.
  - destruct byteString; simpl; intros.
    + discriminate.
    + injections.
      unfold ByteString_push; simpl.
      f_equal.
      rewrite (shatter_word front); reflexivity.
      eapply le_uniqueness_proof.
      rewrite (shatter_word c); simpl; f_equal.
  - intros; rewrite (shatter_word front); injections.
    unfold ByteString_push; simpl.
    destruct (Peano_dec.eq_nat_dec padding 7).
    subst; elimtype False; omega.
    f_equal.
    eapply le_uniqueness_proof.
Qed.

Lemma decode_IPChecksum_pf'
  : forall (u : ()) (b b' : ByteString),
    () -> forall ctxD ctxD' : (), True -> decode_IPChecksum b ctxD = Some (u, b', ctxD') -> True /\ (exists b'' : ByteString, b = ByteString_transformer b'' b').
Proof.
  unfold IPChecksum, decode_IPChecksum, decode_unused_word, decode_unused_word'.
  intros; destruct (WordOpt.transformer_pop_word 16 b) eqn : ? ;
    simpl in H1; try discriminate.
  injections.
  intuition eauto.
  simpl in Heqo.
  pose proof ByteString_transform_push_step_opt as H''; simpl in H''.
  repeat match goal with
    H : context[ByteString_pop ?b] |- _ =>
    let H' := fresh in
    let b := fresh in
    destruct (ByteString_pop b) as [ [b ?] | ] eqn : H';
      try discriminate;
      eapply ByteString_pop_eq_push in H';
      rewrite H'; clear H'
  end; intros.
  injections.
  simpl.
  eexists (ByteString_push H2
       (ByteString_push H3
          (ByteString_push H4
             (ByteString_push H5
                (ByteString_push H6
                   (ByteString_push H7
                      (ByteString_push H8
                         (ByteString_push H9
                            (ByteString_push H10
                               (ByteString_push H11
                                  (ByteString_push H12
                                     (ByteString_push H13
                                        (ByteString_push H14
                                           (ByteString_push H15
                                              (ByteString_push H16 (ByteString_push H17 transform_id)))))))))))))))).
  rewrite !H''; reflexivity.
Admitted.

Lemma length_encode_word' sz :
  forall (w : word sz), bin_measure (encode_word' sz w) = sz.
Proof.
  induction sz; intros;
    rewrite (shatter_word w); simpl.
  - pose proof (transform_measure transform_id transform_id) as H';
      rewrite transform_id_left in H'.
    simpl bin_measure in H'; simpl transform_id in H'; omega.
  - pose proof measure_push as H'; simpl in H'.
    rewrite H', IHsz; omega.
Qed.

Lemma IPv4_Packet_encoded_measure_OK :
  forall (a : IPv4_Packet) (ctx ctx' : ()) (b ext : ByteString)
         (a_OK : IPv4_Packet_OK a),
    encode_IPv4_Packet_Spec a ctx ↝ (b, ctx')
    -> length_ByteString b = IPv4_Packet_encoded_measure (ByteString_transformer b ext).
Proof.
  unfold encode_IPv4_Packet_Spec, composeChecksum, compose, Bind2; intros.
  revert H; pose_string_ids; simpl; intros.
  repeat apply refine_bind_bind' in H.
  apply Bind_inv in H; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H1.
  apply Bind_inv in H1; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H2.
  apply Bind_inv in H2; destruct_ex; split_and.
  apply refine_bind_unit' in H3.
  repeat apply refine_bind_bind' in H3.
  apply Bind_inv in H3; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H4.
  apply Bind_inv in H4; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H5.
  apply Bind_inv in H5; destruct_ex; split_and.
  apply refine_bind_unit' in H6.
  repeat apply refine_bind_bind' in H6.
  apply Bind_inv in H6; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H7.
  apply Bind_inv in H7; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H8.
  apply Bind_inv in H8; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H9.
  apply Bind_inv in H9; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H10.
  apply Bind_inv in H10; destruct_ex; split_and.
  repeat apply refine_bind_bind' in H11.
  repeat apply refine_bind_unit' in H11.
  simpl in H11.
  repeat apply refine_bind_bind' in H11.
  apply Bind_inv in H11; destruct_ex; split_and.
  computes_to_inv.
  simpl in *.
  injections.
  simpl.
  rewrite !transform_ByteString_measure.
  unfold IPChecksum.
  rewrite !length_encode_word'.
  unfold IPv4_Packet_encoded_measure.
  unfold encode_word_Spec in H0.
  computes_to_inv.
  rewrite <- H0.
  simpl fst.
  pose proof transform_assoc as H'; simpl in H'.
  rewrite <- !H'.
  simpl fst.
  unfold decode_unused_word'.
  pose proof transformer_pop_encode_word' as H''; simpl in H''.
  unfold fst.
  rewrite H''.
  unfold DecodeBindOpt.
  unfold If_Opt_Then_Else.
  unfold snd.
  unfold encode_nat_Spec, encode_word_Spec in H1.
  computes_to_inv; rewrite <- H1.
  rewrite <- transformer_pop_word_eq_decode_word'.
  rewrite H''.
  unfold encode_word_Spec in *.
  computes_to_inv.
  subst.
  rewrite !length_encode_word'.
  unfold encode_bool_Spec in *.
  computes_to_inv.
  subst.
  let H' := fresh in
  pose proof measure_push as H'; simpl in H'; rewrite !H'.
  simpl transform_id; unfold ByteString_id; simpl length_ByteString.
  unfold length_ByteString at 1; simpl padding; simpl byteString.
  unfold length_ByteString at 1; simpl padding; simpl byteString.
  simpl length.
  unfold encode_enum_Spec, encode_word_Spec in H10;
    computes_to_inv.
  subst.
  rewrite !length_encode_word'.
  unfold length_ByteString at 1; simpl padding; simpl byteString.
  unfold length_ByteString at 2; simpl padding; simpl byteString.
  simpl length.
  destruct v3.
  let H' := fresh in
  pose proof (measure_encode_length_Spec (A := word 32)) as H';
    eapply H' in H12'1.
  2: clear; intros; computes_to_inv; injections;
    apply length_encode_word'.
  simpl bin_measure in H12'1.
  rewrite H12'1.
  rewrite wordToNat_natToWord_idempotent.
  rewrite !Mult.mult_0_r.
  rewrite <- !plus_n_O.
  rewrite !plus_O_n.
  omega.
  unfold IPv4_Packet_OK in a_OK.
  destruct a_OK.
  revert H1; clear.
  simpl.
  rewrite <- BinNat.N.compare_lt_iff.
  rewrite Nnat.N2Nat.inj_compare.
  rewrite <- Znat.positive_nat_N.
  rewrite !Pnat.Pos2Nat.inj_succ.
  rewrite Nnat.Nat2N.id.
  rewrite Pnat.SuccNat2Pos.id_succ.
  rewrite <- Compare_dec.nat_compare_lt.
  simpl.
  unfold BinPos.Pos.to_nat; simpl.
  unfold StringId11.
  simpl.
  auto with arith.
Admitted. (* Qed takes forever on this proof. *)

Transparent pow2.
Arguments pow2 : simpl never.

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
  intros.
  unfold encode_IPv4_Packet_Spec; pose_string_ids.
  let p := (eval unfold Domain in (fun ip4 : IPv4_Packet => (|ip4!StringId11|, (ip4!StringId, (ip4!StringId0, (ip4!StringId1,
                                                                                                               (ip4!StringId2, (ip4!StringId3, (ip4!StringId4, ip4!StringId5))))))))) in
  let p := eval simpl in p in
      eapply (@composeChecksum_encode_correct
                IPv4_Packet _ transformer IPChecksum
                IPChecksum_Valid IPChecksum_Valid_dec
                IPChecksum_OK IPChecksum_commute IPChecksum_Valid_commute _
                (nat * (word 16 * (word 16 * (bool * (bool * (word 13 * (char * EnumType ["ICMP"; "TCP"; "UDP"])))))))
                _ _ _ decode_IPChecksum H
                p
                (IPv4_Packet_OK)
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
  simpl.
  idtac.
  intros; eapply IPv4_Packet_encoded_measure_OK; eassumption.
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
  destruct (Compare_dec.le_lt_dec (wordToNat proj0) (proj + (proj + (proj + (proj + 0))))).
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
  revert H; unfold StringId11; unfold pow2; simpl; auto with arith.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.
  intros; eapply decode_IPChecksum_pf; eauto.
  intros; eapply decode_IPChecksum_pf'; eauto.
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
  intros; clear; admit. (* Proof that checksum is valid. *)
  repeat (instantiate (1 := fun _ => True)).
  unfold cache_inv_Property; intuition.
  Grab Existential Variables.
  decide equality.
  decide equality.
  exact (@weq _).
Defined.
