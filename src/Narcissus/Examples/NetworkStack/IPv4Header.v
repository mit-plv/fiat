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
Open Scope string_scope.
Open Scope Tuple_scope.

(* Our source data type for IP packets. *)
Record IPv4_Packet :=
  { TotalLength : word 16;
    ID : word 16;
    DF : bool; (* Don't fragment flag *)
    MF : bool; (*  Multiple fragments flag *)
    FragmentOffset : word 13;
    TTL : word 8;
    Protocol : EnumType ["ICMP"; "TCP"; "UDP"];
    SourceAddress : word 32;
    DestAddress : word 32;
    Options : list (word 32) }.

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
     WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
     WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Header_Len (ip4 : IPv4_Packet) := 5 + |ip4.(Options)|.

Definition IPv4_Packet_Format : FormatM IPv4_Packet ByteString :=
  (format_word ◦ (fun _ => natToWord 4 4)
               ++ (format_nat 4) ◦ IPv4_Packet_Header_Len
               ++ format_unused_word 8 (* TOS Field! *)
               ++ format_word ◦ TotalLength
               ++ format_word ◦ ID
               ++ format_unused_word 1 (* Unused flag! *)
               ++ format_bool ◦ DF
               ++ format_bool ◦ MF
               ++ format_word ◦ FragmentOffset
               ++ format_word ◦ TTL
               ++ format_enum ProtocolTypeCodes ◦ Protocol)%format
                                                           ThenChecksum IPChecksum_Valid OfSize 16
                                                           ThenCarryOn (format_word ◦ SourceAddress
                                                                                    ++ format_word ◦ DestAddress
                                                                                    ++ format_list format_word ◦ Options)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4.(Options)|) 11 /\
  lt (20 + 4 * |ipv4.(Options)|) (wordToNat ipv4.(TotalLength)).

(* Step One: Synthesize an encoder and a proof that it is correct. *)

Ltac new_encoder_rules ::=
  match goal with
    |- CorrectAlignedEncoder (_ ThenChecksum _ OfSize _ ThenCarryOn _) _ =>
    eapply @CorrectAlignedEncoderForIPChecksumThenC
  end.

Definition IPv4_encoder :
  CorrectAlignedEncoderFor IPv4_Packet_Format.
Proof.
  start_synthesizing_encoder;
    repeat align_encoder_step.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition IPv4_encoder_impl {sz} v r :=
  Eval simpl in (projT1 IPv4_encoder sz v 0 r tt).
Print IPv4_encoder_impl.

(* Step Two and a Half: Add some simple facts about correct packets
   for the decoder automation. *)
Lemma IPv4_Packet_Header_Len_eq
  : forall packet len,
    IPv4_Packet_Header_Len packet = len
    -> ((|packet.(Options) |) = len - 5).
Proof.
  unfold IPv4_Packet_Header_Len; intros.
  apply Minus.plus_minus.
  rewrite H; reflexivity.
Qed.

Lemma IPv4_Packet_Header_Len_bound
  : forall packet,
    IPv4_Packet_OK packet ->
    lt (IPv4_Packet_Header_Len packet) (pow2 4)%nat.
Proof.
  intros; replace (pow2 4) with 16 by reflexivity.
  unfold IPv4_Packet_OK in H; unfold IPv4_Packet_Header_Len.
  omega.
Qed.

Hint Resolve IPv4_Packet_Header_Len_eq : data_inv_hints.
Hint Resolve IPv4_Packet_Header_Len_bound : data_inv_hints.

Definition IPv4_Packet_encoded_measure (ipv4_b : ByteString)
  : nat :=
  match decode_word' 8 ipv4_b with
       | Some n => wordToNat (split2 4 4 (fst n))
       | None => 0
       end * 32.

Lemma IPv4_Packet_Header_Len_OK
  : forall ip4 ctx ctx' ctx'' c b b'' ext,
    (   format_word ◦ (fun _ => natToWord 4 4)
                    ++ (format_nat 4) ◦ IPv4_Packet_Header_Len
                    ++ format_unused_word 8 (* TOS Field! *)
                    ++ format_word ◦ TotalLength
                    ++ format_word ◦ ID
                    ++ format_unused_word 1 (* Unused flag! *)
                    ++ format_bool ◦ DF
                    ++ format_bool ◦ MF
                    ++ format_word ◦ FragmentOffset
                    ++ format_word ◦ TTL
                    ++ format_enum ProtocolTypeCodes ◦ Protocol)%format
                                                                ip4 ctx ∋ (b, ctx') ->
    (   format_word ◦ SourceAddress
                    ++ format_word ◦ DestAddress
                    ++ format_list format_word ◦ Options)%format ip4 ctx' ∋ (b'', ctx'') ->
    IPv4_Packet_OK ip4 ->
    (fun _ => 128) ip4 + (fun a => 16 + |ip4.(Options)| * 32) ip4 + 16
    = IPv4_Packet_encoded_measure (mappend (mappend b (mappend (format_checksum _ _ _ 16 c) b'')) ext).
Proof.
  intros; simpl.
  pose proof mappend_assoc as H''; simpl in H'';
    rewrite <- !H''.
  unfold IPv4_Packet_encoded_measure.
  unfold sequence_Format at 1 in H.
  unfold sequence_Format at 1 in H.
  unfold compose, Bind2 in H.
  computes_to_inv; subst.
  destruct v; destruct v1.
  eapply EquivFormat_Projection_Format in H.
  unfold format_word in H; computes_to_inv; subst.
  eapply EquivFormat_Projection_Format in H'.
  unfold format_word in H'; computes_to_inv; subst; simpl in *.
  injections.
  simpl.
  replace ((ByteString_enqueue_ByteString
            (ByteString_enqueue false
               (ByteString_enqueue false (ByteString_enqueue true (ByteString_enqueue false ByteString_id))))
            (ByteString_enqueue_ByteString b1 (fst v2))))
    with (encode_word' 8 (Word.combine (natToWord 4 4) (natToWord 4 (IPv4_Packet_Header_Len ip4))) mempty).
  pose proof (@decode_encode_word' ByteString _ _) as H''''; simpl in H''''.
  rewrite H''''.
  simpl.
  rewrite split2_combine.
  rewrite wordToNat_natToWord_idempotent;
    unfold IPv4_Packet_Header_Len; try omega.
  unfold IPv4_Packet_OK in H1.
  eapply Nomega.Nlt_in.
  rewrite Nnat.Nat2N.id.
  unfold Npow2; simpl.
  unfold Pos.to_nat; simpl; intuition.
  simpl.
Admitted.

Definition aligned_IPv4_Packet_encoded_measure
           {sz} (ipv4_b : ByteBuffer.t sz)
  : nat :=
  match nth_opt ipv4_b 0 with
  | Some n => wordToNat (split2 4 4 n)
  | None => 0
  end * 32.

Fixpoint aligned_IPv4_Packet_Checksum {sz}
         (v : t Core.char sz) (idx : nat)
  := match idx with
     | 0 => weqb (InternetChecksum.ByteBuffer_checksum_bound (aligned_IPv4_Packet_encoded_measure v) v) (wones 16)
     | S idx' =>
       match v with
       | Vector.cons _ _ v' => aligned_IPv4_Packet_Checksum v' idx'
       | _ => false
       end
     end.

Lemma aligned_IPv4_Packet_encoded_measure_OK_1 {sz}
  : forall (v : t Core.char sz),
    (if
        IPChecksum_Valid_dec (IPv4_Packet_encoded_measure (build_aligned_ByteString v)) (build_aligned_ByteString v)
      then true
      else false) =
    aligned_IPv4_Packet_Checksum v 0.
Proof.
  intros.
  unfold IPChecksum_Valid_dec.
  unfold IPv4_Packet_encoded_measure.
  destruct v.
  - reflexivity.
  - rewrite aligned_decode_char_eq.
    unfold aligned_IPv4_Packet_Checksum, aligned_IPv4_Packet_encoded_measure.
    simpl.
    replace (wordToNat (split2 4 4 h) * 32) with ((wordToNat (split2 4 4 h) * 4) * 8) by omega.
    rewrite <- InternetChecksum_To_ByteBuffer_Checksum.
    unfold onesComplement.
    find_if_inside.
    rewrite e.
    reflexivity.
    destruct (weqb (InternetChecksum.checksum (ByteString2ListOfChar (wordToNat (split2 4 4 h) * 4 * 8) (build_aligned_ByteString (h :: v))))
    WO~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1~1) eqn: ? ; eauto.
    apply weqb_sound in Heqb; congruence.
Qed.

Lemma aligned_IPv4_Packet_encoded_measure_OK_2 {sz}
  : forall (v : ByteBuffer.t (S sz)) (idx : nat),
    aligned_IPv4_Packet_Checksum v (S idx) =
    aligned_IPv4_Packet_Checksum (Vector.tl v) idx.
Proof.
  intros v; pattern sz, v.
  apply Vector.caseS; reflexivity.
Qed.

Arguments andb : simpl never.

Hint Resolve aligned_IPv4_Packet_encoded_measure_OK_1.
Hint Resolve aligned_IPv4_Packet_encoded_measure_OK_2.

(* Step Three: Synthesize a decoder and a proof that /it/ is correct. *)
Definition IPv4_Packet_Header_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.
  (* We have to use an extra lemma at the start, because of the 'exotic'
     IP Checksum. *)
  start_synthesizing_decoder.
  Opaque CorrectDecoder.
  match goal with
  | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ =>
    eapply compose_IPChecksum_format_correct with (format1 := fmt1)
  end.
  apply H.
  repeat calculate_length_ByteString.
  repeat calculate_length_ByteString.
  solve_mod_8.
  solve_mod_8.
  pose proof (mult_32_mod_8 0 (| Options a|));
    rewrite <- plus_n_O in H0; eauto.
  apply IPv4_Packet_Header_Len_OK.
  intros.
  NormalizeFormats.normalize_format.
  repeat apply_rules.
  synthesize_cache_invariant.
  cbv beta; unfold decode_nat, sequence_Decode; optimize_decoder_impl.
  let H := fresh in pose proof @AlignedDecode_if_Sumb_dep as H;
                      eapply H; clear H.
  eauto using aligned_IPv4_Packet_encoded_measure_OK_1.
  eauto using aligned_IPv4_Packet_encoded_measure_OK_2.
  repeat align_decoders_step.
  repeat align_decoders_step.
Defined.

(* Step Four: Extract the decoder function, and have /it/ start decoding
   at the start of the provided ByteString [v]. *)
Arguments GetCurrentBytes : simpl never.
Definition IPv4_decoder_impl {sz} v :=
  Eval simpl in (projT1 IPv4_Packet_Header_decoder sz v 0 ()).

Section BP.
  Local Opaque ByteBuffer.of_vector.

  (* Some example uses of the encoder and decoder functions. *)
  (* A binary version of a packet, sourced directly from the web. *)
  Definition bin_pkt : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0]).

  Definition bin_pkt' : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;0;0;192;168;222;10;192;168;222;1;0;0;0;0]).
End BP.

(* An source version of a packet, different from binary packet above. *)
Definition pkt :=
  {| TotalLength := WO~0~1~1~1~0~1~0~0~0~0~0~0~0~0~0~0;
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Definition bad_pkt :=
  {| TotalLength := wzero _; (* length is too short *)
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Eval vm_compute in (IPv4_decoder_impl bin_pkt).

(* This should succeed, *)
Eval compute in
    Ifopt (IPv4_encoder_impl (initialize_Aligned_ByteString 100) pkt)
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* This should fail because the total length field is too short, *)
Eval compute in
    Ifopt (IPv4_encoder_impl (initialize_Aligned_ByteString 100) bad_pkt)
  as bs Then IPv4_decoder_impl (fst (fst bs))
        Else None.
(* and it does! *)

(* Some addition checksum sanity checks. *)
Compute
  match IPv4_decoder_impl bin_pkt with
  | Some (p, _, _) => Some ((wordToN p.(SourceAddress)), wordToN p.(DestAddress))
  | None => None
  end.

Goal match AlignedIPChecksum.calculate_IPChecksum bin_pkt' 0 ()()  with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  reflexivity.
Qed.

Definition pkt' := {|
                    TotalLength := WO~0~1~1~0~0~1~0~0~0~0~0~0~0~0~0~0;
                    ID := WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    DF := false;
                    MF := false;
                    FragmentOffset := WO~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    TTL := WO~0~0~1~0~0~1~1~0;
                    Protocol := Fin.F1;
                    SourceAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~1~0~1~0;
                    DestAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~0~0~0~1;
                    Options := [] |}.

Goal match IPv4_encoder_impl (initialize_Aligned_ByteString 24) pkt'  with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  compute.
  reflexivity.
Qed.
