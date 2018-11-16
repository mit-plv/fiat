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

  Ltac new_encoder_rules ::=
    eapply @CorrectAlignedEncoderForPseudoChecksumThenC;
    [ | | intros; calculate_length_ByteString'].

  (* Step One: Synthesize an encoder and a proof that it is correct. *)
  Definition TCP_encoder :
    CorrectAlignedEncoderFor TCP_Packet_Format.
  Proof.
    synthesize_aligned_encoder.
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

Lemma TCP_Packet_Header_Len_OK
      : forall (a : TCP_Packet) (ctx ctx' ctx'' : CacheFormat) (c : word 16) (b b'' ext : ByteString),
  (format_word ◦ SourcePort ++
   format_word ◦ DestPort ++
   format_word ◦ SeqNumber ++
   format_word ◦ AckNumber ++
   format_nat 4 ◦ Init.Nat.add 5 ∘ (Datatypes.length (A:=word 32) ∘ Options) ++
   format_unused_word 3 ++
   format_bool ◦ NS ++
   format_bool ◦ CWR ++
   format_bool ◦ ECE ++
   format_bool ◦ (fun urg_opt : option (word 16) => Ifopt urg_opt as _ Then true Else false) ∘ UrgentPointer ++
   format_bool ◦ ACK ++
   format_bool ◦ PSH ++ format_bool ◦ RST ++ format_bool ◦ SYN ++ format_bool ◦ FIN ++ format_word ◦ WindowSize) a ctx ∋
  (b, ctx') ->
  (Option.format_option format_word (format_unused_word 16) ◦ UrgentPointer ++
   format_list format_word ◦ Options ++ format_bytebuffer ◦ Payload) a ctx' ∋ (b'', ctx'') ->
  TCP_Packet_OK a ->
  (fun _ : TCP_Packet => 16 + (16 + (32 + (32 + (4 + (3 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + (1 + 16))))))))))))))) a +
  (fun a' : TCP_Packet => 16 + ((| Options a' |) * 32 + 8 * projT1 (Payload a'))) a + 16 =
  TCP_Length
    (mappend
       (mappend b
          (mappend (format_checksum ByteString AlignedByteString.ByteStringQueueMonoid ByteString_QueueMonoidOpt 16 c) b'')) ext).
Proof.
  intros.
  unfold TCP_Length; rewrite (proj2 H1).
  omega.
Qed.

Definition aligned_TCP_Packet_checksum
           {sz}
           (v : t Core.char sz)
           (idx : nat)
  : bool :=
  if weqb (InternetChecksum.ByteBuffer_checksum_bound 20 v) (wones 16) then true
  else false.

Lemma aligned_TCP_Packet_checksum_OK_1 {sz}
  : forall (v : t Core.char sz),
    weqb
    (InternetChecksum.add_bytes_into_checksum (wzero 8) (natToWord 8 6)
       (onesComplement
          (ByteString2ListOfChar (96 + TCP_Length (build_aligned_ByteString v)) (build_aligned_ByteString v) ++
                                 to_list srcAddr ++ to_list destAddr ++ to_list (splitLength tcpLength)))) WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1
    = aligned_TCP_Packet_checksum v 0.
Proof.
Admitted.

Lemma aligned_TCP_Packet_checksum_OK_2 {sz}
  : forall (v : ByteBuffer.t (S sz)) (idx : nat),
    aligned_TCP_Packet_checksum v (S idx) =
    aligned_TCP_Packet_checksum (Vector.tl v) idx.
Proof.
Admitted.

Hint Resolve aligned_TCP_Packet_checksum_OK_1.
Hint Resolve aligned_TCP_Packet_checksum_OK_2.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition TCP_Packet_Header_decoder
  : CorrectAlignedDecoderFor TCP_Packet_OK TCP_Packet_Format.
Proof.
  start_synthesizing_decoder.
  NormalizeFormats.normalize_format.
  eapply compose_PseudoChecksum_format_correct.
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  exact H.
  solve_mod_8.
  solve_mod_8.
  apply TCP_Packet_Header_Len_OK.
  intros; NormalizeFormats.normalize_format.
  repeat apply_rules.
  eapply (format_sequence_correct H4).
  apply Nat_decode_correct.
  simpl; intros;
    unfold Basics.compose.
  eapply TCP_Packet_Len_OK; intuition eauto.
  intros; repeat apply_rules.
  eapply (format_sequence_correct H16).
  Opaque CorrectDecoder.
  intros; eapply Option.option_format_correct'.
  exact H16.
  intros; apply_rules.
  intros; eapply unused_word_decode_correct; eauto.
  simpl.
  intros; intuition.
  unfold Basics.compose in H25.
  instantiate (1 := s'7).
  destruct s; simpl in *.
  destruct UrgentPointer0; simpl in *; subst; simpl; eauto.
  congruence.
  destruct s; destruct UrgentPointer0; eauto.
  intros.
  eapply (format_sequence_correct H16).
  intros; repeat apply_rules.
  intros.
  instantiate (1 := s'3 - 5); simpl; intuition.
  unfold Basics.compose in H32; omega.
  intros; eapply (format_sequence_correct).
  eauto.
  intros; eapply ByteBuffer_decode_correct
            with (n := wordToNat tcpLength - (20 + 4 * (s'3 - 5))).
  intros; repeat apply_rules.
  simpl; eauto.
  intros; repeat apply_rules.
  cbv beta; synthesize_cache_invariant.
  (* Perform algebraic simplification of the decoder implementation. *)
  Opaque ByteString2ListOfChar.
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  unfold Basics.compose; simpl.
  cbv beta; align_decoders.
  eapply @AlignedDecodeByteBufferM; intros; eauto.
  align_decoders.
  Grab Existential Variables.
  eauto.
  eauto.
Defined.

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

(*Definition out :=
Eval compute in
    match (@TCP_decoder_impl (wzero _ ) srcAddr destAddr (natToWord _ (Vector_length tcp_decode_input)) _ tcp_decode_input) with
    | Some (p, _, _) =>
      (Some (Vector.fold_right (fun c s => String (Ascii.ascii_of_N (wordToN c)) s) (projT2 p.(Payload)) EmptyString),
       match (@TCP_encoder_impl srcAddr destAddr (natToWord _ (Vector_length tcp_decode_input))
                                p _ (Vector.const (natToWord 8 0) (Vector_length tcp_decode_input))) with
       | Some (v, _, _) => Some (Vector.map (@wordToNat 8) v)
       | None => None
       end)
    | None => (None, None)
    end. *)
