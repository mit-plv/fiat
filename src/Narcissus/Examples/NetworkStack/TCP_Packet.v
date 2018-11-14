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
     Payload : { n & ByteBuffer.t n }}.

  (* These values are provided by the IP header for checksum calculation.*)

  (* These values are provided by the IP header for checksum calculation.*)
  Variable srcAddr : ByteBuffer.t 4.
  Variable destAddr : ByteBuffer.t 4.
  Variable tcpLength : word 16.

  Section ByteBuffer.
    Context {sz : nat}.

    Context {T : Type}.
    Context {cache : Cache}.
    Context {cacheAddNat : CacheAdd cache nat}.
    Context {monoid : Monoid T}.
    Context {monoidUnit : QueueMonoidOpt monoid bool}.

    Definition format_bytebuffer (b : { n & ByteBuffer.t n }) (ce : CacheFormat) : Comp (T * CacheFormat) :=
      format_list format_word (ByteBuffer.to_list (projT2 b)) ce.
  End ByteBuffer.

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
          ++ format_bool ◦ (Basics.compose (fun urg_opt => Ifopt urg_opt as urg Then true Else false) UrgentPointer)
          ++ format_bool ◦ ACK
          ++ format_bool ◦ PSH
          ++ format_bool ◦ RST
          ++ format_bool ◦ SYN
          ++ format_bool ◦ FIN
          ++ format_word ◦ WindowSize)
          ThenChecksum (Pseudo_Checksum_Valid srcAddr destAddr tcpLength (natToWord 8 6)) OfSize 16
          ThenCarryOn (Option.format_option format_word (@format_unused_word 16 _ _ _ _ _ _) ◦ UrgentPointer
                                            ++ format_list format_word ◦ Options
                                            ++ format_bytebuffer ◦ Payload).

  Definition TCP_Packet_OK (tcp : TCP_Packet) :=
    lt (|tcp.(Options)|) 11
    /\ wordToNat tcpLength
       = 20 (* length of packet header *)
         + (4 * |tcp.(Options)|) (* length of option field *)
         + (projT1 tcp.(Payload)).

  Local Arguments NPeano.modulo : simpl never.

  Definition TCP_Length :=
    (fun _ : ByteString => wordToNat tcpLength * 8).

  (* Step One: Synthesize an encoder and a proof that it is correct. *)
  Definition TCP_encoder :
    CorrectAlignedEncoderFor TCP_Packet_Format.
  Proof.
    start_synthesizing_encoder.
    eapply @CorrectAlignedEncoderForPseudoChecksumThenC.
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
    (decompose_aligned_encoder; eauto).
    (decompose_aligned_encoder; eauto).
    align_encoder_step.
    unfold format_bytebuffer.
    
    apply CorrectAlignedEncoderForFormatCharList.
    repeat align_encoder_step.
    repeat align_encoder_step.
    repeat align_encoder_step.
    intros; calculate_length_ByteString'.
  Defined.

  (* Step Two: Extract the encoder function, and have it start encoding
     at the start of the provided ByteString [v]. *)
  Definition TCP_encoder_impl r {sz} v :=
    Eval simpl in (projT1 TCP_encoder sz v 0 r tt).

(* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)

Lemma TCP_Packet_Len_OK
  : forall tcp,
    TCP_Packet_OK tcp ->
    (lt (5 + (| Options tcp |)) (pow2 4)).
Proof.
  unfold TCP_Packet_OK; simpl; intros.
  intuition; intros.
  unfold pow2, mult; simpl.
  omega.
Qed.

Opaque pow2.
Arguments andb : simpl never.

Hint Resolve TCP_Packet_Len_OK : data_inv_hints.

  Arguments GetCurrentBytes : simpl never.
(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition TCP_Packet_Header_decoder
  : CorrectAlignedDecoderFor TCP_Packet_OK TCP_Packet_Format.
Proof.
  (* We have to use an extra lemma at the start, because of the 'exotic'
     IP Checksum. *)
  eapply CorrectAlignedDecoderForUDPChecksumThenC.
  intros; calculate_length_ByteString'; rewrite H; higher_order_reflexivity.
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
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  simpl; instantiate (1 := proj7); simpl.
  intro; destruct (UrgentPointer data); simpl; intuition;
    subst; simpl; congruence.
  destruct a'; simpl; decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  simpl; instantiate (1 := proj3 - 5); intuition.
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  decode_step ltac:(idtac).
  simpl in *; unfold TCP_Packet_OK in *; intuition.
  instantiate (1 := wordToNat tcpLength
                    - (20 + 4 * (proj3 - 5))); omega.
  unfold Vector.nth; simpl.
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
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.

  eapply @AlignedDecodeCharListM; intros; eauto.
  (* align_decoders_step. *)
  (* align_decoders_step. *)
  align_decoders_step.
  align_decoders_step.
  align_decoders_step.
  Grab Existential Variables.
  eauto.
  eauto.
  eauto.
  eauto.
  shelve.
  synthesize_cache_invariant.
  synthesize_cache_invariant.
Defined.

(*Lemma TCP_Packet_Header_Len_OK
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
Qed. *)

Definition TCP_decoder_impl {sz} v :=
  Eval simpl in (projT1 TCP_Packet_Header_decoder sz v 0 ()).

End TCPPacketDecoder.

Print TCP_decoder_impl.

Definition tcp_decode_input :=
  Vector.map
    (natToWord 8)
    [144; 42; 0; 80; 19; 125; 120; 241; 243; 111; 68; 47; 128; 24;
     0; 229; 29; 216; 0; 0; 1; 1; 8; 10; 228; 110; 2; 137;
     80; 206; 41; 110; 71; 69; 84; 32; 47; 32; 72; 84; 84; 80;
     47; 49; 46; 49; 13; 10; 72; 111; 115; 116; 58; 32; 110; 121;
     116; 105; 109; 101; 115; 46; 99; 111; 109; 13; 10; 85; 115; 101;
     114; 45; 65; 103; 101; 110; 116; 58; 32; 99; 117; 114; 108; 47;
     55; 46; 52; 55; 46; 48; 13; 10; 65; 99; 99; 101; 112; 116;
     58; 32; 42; 47; 42; 13; 10; 13; 10].

Definition srcAddr := (Vector.map (natToWord 8) [192; 168; 1; 109]).
Definition destAddr := (Vector.map (natToWord 8) [151; 101; 129; 164]).
Definition Vector_length {A n} (v: Vector.t A n) := n.

Definition out :=
Eval compute in
    match (@TCP_decoder_impl srcAddr destAddr (natToWord _ (Vector_length tcp_decode_input)) _ tcp_decode_input) with
    | Some (p, _, _) =>
      (Some (List.fold_right (fun c s => String (Ascii.ascii_of_N (wordToN c)) s) EmptyString p.(Payload)),
       match (@TCP_encoder_impl srcAddr destAddr (natToWord _ (Vector_length tcp_decode_input))
                                p _ (Vector.const (natToWord 8 0) (Vector_length tcp_decode_input))) with
       | Some (v, _, _) => Some (Vector.map (@wordToNat 8) v)
       | None => None
       end)
    | None => (None, None)
    end.
