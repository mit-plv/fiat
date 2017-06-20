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
Section TCPPacketDecoder.

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

  (* These values are provided by the IP header for checksum calculation.*)

  Variable srcAddr : word 32.
  Variable destAddr : word 32.
  Variable tcpLength : word 16.

  Definition TCP_Checksum_Valid
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
             (tcp : TCP_Packet) :=
         (      encode_word_Spec (tcp!"SourcePort")
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
ThenChecksum (TCP_Checksum_Valid) OfSize 16
ThenCarryOn (encode_option_Spec encode_word_Spec (encode_unused_word_Spec' 16 ByteString_id) tcp!"UrgentPointer"
       ThenC encode_list_Spec encode_word_Spec tcp!"Options"
       ThenC encode_list_Spec encode_word_Spec tcp!"Payload" DoneC).

  Definition TCP_Packet_OK (tcp : TCP_Packet) :=
    lt (|tcp!"Options"|) 11
    /\ wordToNat tcpLength = 20 (* length of packet header *)
                             + (4 * |tcp!"Options"|) (* length of option field *)
                             + (|tcp!"Payload"|).

  Local Arguments NPeano.modulo : simpl never.

  Definition TCP_Length :=
    (fun _ : ByteString => (wordToNat tcpLength) * 8).

  Lemma TCP_Packet_Header_Len_OK
    : forall (tcp : TCP_Packet) (ctx ctx' ctx'' : CacheEncode) (c : word 16) (b b'' ext : ByteString),
      (      encode_word_Spec (tcp!"SourcePort")
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
          ThenC encode_word_Spec tcp!"WindowSize" DoneC) ctx ↝ (b, ctx') ->
      (encode_option_Spec encode_word_Spec (encode_unused_word_Spec' 16 ByteString_id) tcp!"UrgentPointer"
       ThenC encode_list_Spec encode_word_Spec tcp!"Options"
       ThenC encode_list_Spec encode_word_Spec tcp!"Payload" DoneC) ctx' ↝ (b'', ctx'') ->
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
       (transform (transform b (transform (encode_checksum ByteString transformer ByteString_QueueTransformerOpt 16 c) b'')) ext)).
Proof.
  intros.
  intros; change transform_id with ByteString_id; rewrite length_ByteString_ByteString_id.
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
  : CorrectDecoderFor TCP_Packet_OK encode_TCP_Packet_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
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
    Eval simpl in (fst (projT1 TCP_Packet_decoder')).

End TCPPacketDecoder.

Print TCP_Packet_decoder_impl.
