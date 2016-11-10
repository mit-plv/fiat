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
        Fiat.BinEncoders.Env.Lib2.Bool
        Fiat.BinEncoders.Env.Lib2.Option
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

Definition TCP_Packet :=
  @Tuple <"SourcePort" :: word 16,
          "DestPort" :: word 16,
          "SeqNumber" :: word 32,
          "AckNumber" :: word 32,
          "NS" :: bool, (* ECN-nonce concealment protection flag *)
          "CWR" :: bool, (* Congestion Window Reduced (CWR) flag *)
          "ECE" :: bool, (* ECN-Echo flag *)
          (* We can infer the URG flag from the Urgent Pointer field *)
          "ACK" :: bool, (* Acknowledgment field is significant flag *)
          "PSH" :: bool, (* Push function flag *)
          "RST" :: bool, (* Reset the connection flag *)
          "SYN" :: bool, (* Synchronize sequence numbers flag *)
          "FIN" :: bool, (* No more data from sender flag*)
          "WindowSize" :: word 16,
          "UrgentPointer" :: option (word 16),
          "Options" :: list (word 32),
          "Payload" :: list char >.

Definition TCP_Checksum_Valid
           (srcAddr : word 32)
           (destAddr : word 32)
           (tcpLength : word 16)
           (n : nat)
           (b : ByteString)
  := IPChecksum_Valid (96 + n)
                (transform (transform (encode_word srcAddr)
                (transform (encode_word destAddr)
                (transform (encode_word (wzero 8))
                (transform (encode_word (natToWord 8 6))
                           (encode_word tcpLength)))))
                b).

Definition encode_TCP_Packet_Spec
           (srcAddr : word 32)
           (destAddr : word 32)
           (tcpLength : word 16)
           (* These values are provided by the IP header for checksum calculation.*)
           (tcp : TCP_Packet) :=
          (encode_word_Spec (tcp!"SourcePort")
    ThenC encode_word_Spec (tcp!"DestPort")
    ThenC encode_word_Spec (tcp!"SeqNumber")
    ThenC encode_word_Spec (tcp!"AckNumber")
    ThenC encode_nat_Spec 4 (5 + |tcp!"Options"|)
    ThenC encode_unused_word_Spec 3 (* These bits are reserved for future use. *)
    ThenC encode_bool_Spec tcp!"NS"
    ThenC encode_bool_Spec tcp!"CWR"
    ThenC encode_bool_Spec tcp!"ECE"
    ThenC encode_bool_Spec (match tcp!"UrgentPointer" with
                            | Some _ => true
                            | _ => false
                            end)
    ThenC encode_bool_Spec tcp!"ACK"
    ThenC encode_bool_Spec tcp!"PSH"
    ThenC encode_bool_Spec tcp!"RST"
    ThenC encode_bool_Spec tcp!"SYN"
    ThenC encode_bool_Spec tcp!"FIN"
    ThenC encode_word_Spec tcp!"WindowSize" DoneC)
    ThenChecksum (TCP_Checksum_Valid srcAddr destAddr tcpLength) OfSize 16
    ThenCarryOn (encode_option_Spec encode_word_Spec (encode_unused_word_Spec' 16 ByteString_id) tcp!"UrgentPointer"
    ThenC encode_list_Spec encode_word_Spec tcp!"Options"
    ThenC encode_list_Spec encode_word_Spec tcp!"Payload" DoneC).

Definition TCP_Packet_OK (tcpLength : word 16) (tcp : TCP_Packet) :=
  lt (|tcp!"Options"|) 11
  /\ wordToNat tcpLength = 20 (* length of packet header *)
                 + (4 * |tcp!"Options"|) (* length of option field *)
                 + (|tcp!"Payload"|).

Definition TCP_Packet_decoder'
  : { decodePlusCacheInv |
      forall srcAddr destAddr tcpLength,
      exists P_inv,
        (cache_inv_Property (snd decodePlusCacheInv) P_inv
         -> encode_decode_correct_f _ transformer (TCP_Packet_OK tcpLength) (fun _ _ => True)
                                    (encode_TCP_Packet_Spec srcAddr destAddr tcpLength)
                                    ((fst decodePlusCacheInv) srcAddr destAddr tcpLength)
                                    (snd decodePlusCacheInv))
        /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  unfold encode_TCP_Packet_Spec; pose_string_ids.
  let p := (eval unfold Domain in
               (fun tcp : TCP_Packet =>
                  (tcp!StringId,
                   (tcp!StringId0,
                   (tcp!StringId1,
                   (tcp!StringId2,
                   (|tcp!StringId13|,
                   (tcp!StringId3,
                   (tcp!StringId4,
                   (tcp!StringId5,
                   (match tcp!StringId12 with
                            | Some _ => true
                            | _ => false
                            end,
                   (tcp!StringId6,
                   (tcp!StringId7,
                   (tcp!StringId8,
                   (tcp!StringId9,
                   (tcp!StringId10,
                    tcp!StringId11
           )))))))))))))))) in
  let p := eval simpl in p in
      eapply (@compose_IPChecksum_encode_correct_dep
                TCP_Packet
                _
                _
                _
                _ _ _ H
                p
                (TCP_Packet_OK tcpLength)
                _ _ _
                (fun data' =>
                   (encode_word_Spec (fst data')
              ThenC encode_word_Spec (fst (snd data'))
              ThenC encode_word_Spec (fst (snd (snd data')))
              ThenC encode_word_Spec (fst (snd (snd (snd data'))))
              ThenC encode_nat_Spec 4 (5 + (fst (snd (snd (snd (snd data'))))))
              ThenC encode_unused_word_Spec 3 (* These bits are reserved for future use. *)
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd data'))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd data')))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd data'))))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd (snd data')))))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd data'))))))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd data')))))))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd data'))))))))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd data')))))))))))))
              ThenC encode_bool_Spec (fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd data'))))))))))))))
              ThenC encode_word_Spec (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd data')))))))))))))) DoneC))).
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
    instantiate (1 := fun _ => (wordToNat tcpLength) * 8);
      cbv beta.
    unfold TCP_Packet_OK in H2.
    rewrite (proj2 H2).
    unfold StringId13, StringId14.
    clear.
    repeat match goal with
             |- context [ @length ?A (@GetAttribute ?heading ?z ?l)] => remember (@length A (@GetAttribute heading z l))
           end.
    assert (n = n1) by (subst; reflexivity).
    assert (n0 = n2) by (subst; reflexivity).
    rewrite H, H0.
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
  decode_step.
  decode_step.
  decode_step. (* intros; eapply bool_decode_correct. *)

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
  decode_step.
  decode_step.
  intros; eapply encode_decode_correct_finish.

  let a' := fresh in
  intros a'; repeat destruct a' as [? a'].
    (* Show that it is determined by the constraints (equalities) *)
    (* inferred during parsing. *)
  unfold GetAttribute, GetAttributeRaw in *;
  simpl in *; intros;
    (* Decompose data predicate *) intuition.
  (* need to clean this up as well *)
  assert (proj3 - 5 = n) as H' by omega; rewrite <- H'; clear H' H30.
  subst.
  reflexivity.

  decide_data_invariant.

  unfold TCP_Packet_OK; clear; intros ? H'; repeat split.
  simpl; destruct H'.
  revert H; unfold pow2; simpl; clear.
  unfold StringId13; intros; omega.
  instantiate (1 := fun _ _ => True);
    simpl; intros; exact I.

  decode_step.
  decode_step.
  decode_step.
  decode_step.
  simpl; intros; split_and.
  instantiate (1 := fst (snd (snd (snd (snd (snd (snd (snd (snd proj))))))))).
  repeat match goal with
           H : prod _ _ |- _ => destruct H
         end.
  simpl in *; injections.
  match goal with
    |- context [decides (negb match ?b with _ => _ end) (?b' = None) ] =>
    assert (b = b') as H' by reflexivity; rewrite H'; destruct b';
      simpl; intuition eauto
  end.
  discriminate.
  destruct a'; intros; exact I.

  decode_step.
  decode_step.
  decode_step.

  simpl; intros; instantiate (1 := fst (snd (snd (snd (snd proj))))).
  intuition; subst; simpl; auto with arith.
  decode_step.
  decode_step.
  decode_step.
  decode_step.
  simpl in *; intros.
  unfold TCP_Packet_OK in H3.
  do 4 destruct H3.
  split; eauto.
  instantiate (1 := (wordToNat tcpLength) - 20 - (4 * fst (snd (snd (snd (snd proj)))))).
  rewrite <- H6.
  rewrite H7.
  unfold snd, fst.
  fold StringId14; fold StringId13.
  clear.
  repeat match goal with
           |- context [ @length ?A (@GetAttribute ?heading ?z ?l)] => remember (@length A (@GetAttribute heading z l))
         end.
  assert (n = n1) by (subst; reflexivity).
  assert (n0 = n2) by (subst; reflexivity).
  rewrite H, H0.
  omega.
  decode_step.

  intros; eapply encode_decode_correct_finish.

    let a' := fresh in
  intros a'; repeat destruct a' as [? a'].
    (* Show that it is determined by the constraints (equalities) *)
    (* inferred during parsing. *)
  unfold GetAttribute, GetAttributeRaw in *;
    simpl in *; intros;
    (* Decompose data predicate *) intuition.
  rename H14 into H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  let H' := fresh in
  pose proof (f_equal fst H17) as H'; simpl in H';
    apply (f_equal snd) in H17; simpl in H17.
  subst; reflexivity.
  decide_data_invariant.
  synthesize_cache_invariant.
Time Defined.

(*Definition TCP_Packet_decoder_impl :=
  Eval simpl in (fst (projT1 TCP_Packet_decoder')).

Print TCP_Packet_decoder_impl. *)
