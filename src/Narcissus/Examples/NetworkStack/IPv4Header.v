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
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Stores.EmptyStore.

Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope Tuple_scope.

(* Our source data type for IP packets. *)
Definition IPv4_Packet :=
  @Tuple <"TotalLength" :: word 16,
  "ID" :: word 16,
  "DF" :: bool, (* Don't fragment flag *)
  "MF" :: bool, (*  Multiple fragments flag *)
  "FragmentOffset" :: word 13,
  "TTL" :: word 8,
  "Protocol" :: EnumType ["ICMP"; "TCP"; "UDP"],
  "SourceAddress" :: word 32,
  "DestAddress" :: word 32,
  "Options" :: list (word 32)>.

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
     WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
     WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Header_Len (ip4 : IPv4_Packet) := 5 + |ip4!"Options"|.

Definition IPv4_Packet_Format (ip4 : IPv4_Packet)  :=
  (format_word (natToWord 4 4)
               ThenC format_nat 4 (IPv4_Packet_Header_Len ip4)
               ThenC format_unused_word 8 (* TOS Field! *)
               ThenC format_word ip4!"TotalLength"
               ThenC format_word ip4!"ID"
               ThenC format_unused_word 1 (* Unused flag! *)
               ThenC format_bool ip4!"DF"
               ThenC format_bool ip4!"MF"
               ThenC format_word ip4!"FragmentOffset"
               ThenC format_word ip4!"TTL"
               ThenC format_enum ProtocolTypeCodes ip4!"Protocol"
               DoneC)
    ThenChecksum IPChecksum_Valid' OfSize 16
    ThenCarryOn (format_word ip4!"SourceAddress"
                             ThenC format_word ip4!"DestAddress"
                             ThenC format_list format_word ip4!"Options"
                             DoneC)%format.

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4!"Options"|) 11 /\
  lt (20 + 4 * |ipv4!"Options"|) (wordToNat ipv4!"TotalLength").

(* Step One: Synthesize an encoder and a proof that it is correct. *)

Definition ipv4_encoder :
  CorrectAlignedEncoderFor IPv4_Packet_Format IPv4_Packet_OK.
Proof.
  synthesize_aligned_encoder.
Defined.

(* Step Two: Extract the encoder function, and have it start encoding
   at the start of the provided ByteString [v]. *)
Definition ipv4_encoder_impl r {sz} v :=
  Eval simpl in (projT1 ipv4_encoder r sz v 0 tt).

Lemma IPv4_Packet_Header_Len_eq
  : forall data len,
    IPv4_Packet_Header_Len data = len
    -> ((|data!"Options" |) = len - 5).
Proof.
  unfold IPv4_Packet_Header_Len; intros.
  apply Minus.plus_minus.
  rewrite H; reflexivity.
Qed.

Hint Resolve IPv4_Packet_Header_Len_eq : data_inv_hints.

Arguments wordToNat : simpl never.

Definition EthernetHeader_decoder
  : CorrectAlignedDecoderFor IPv4_Packet_OK IPv4_Packet_Format.
Proof.
  eapply CorrectAlignedDecoderForIPChecksumThenC.
  cbv beta; unfold Domain; simpl; repeat calculate_length_ByteString.
  unfold IPv4_Packet_OK.
  start_synthesizing_decoder.
  normalize_compose AlignedByteString.ByteStringQueueMonoid.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  admit.
  repeat decode_step idtac.
  repeat decode_step idtac.
  cbv beta; synthesize_cache_invariant.
  cbv beta; unfold decode_nat; optimize_decoder_impl.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply @AlignedDecode_CollapseWord; eauto.
  eapply @AlignedDecodeBindCharM; intros.
  intros; apply @AlignedDecode_Sumb.
  eapply @AlignedDecodeBindUnusedCharM; simpl;
    eapply DecodeMEquivAlignedDecodeM_trans;
      [ | intros; reflexivity
        |  ].
  eapply @AlignedDecodeBind2CharM; intros; eauto.
  eapply @AlignedDecodeBind2CharM; intros; eauto.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply AlignedDecode_CollapseWord';
    eauto using decode_word_eq_decode_unused_word,
    decode_word_eq_decode_bool,
    decode_word_eq_decode_word.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply AlignedDecode_CollapseWord';
    eauto using decode_word_eq_decode_unused_word,
    decode_word_eq_decode_bool,
    decode_word_eq_decode_word.
  eapply @AlignedDecoders.AlignedDecode_Sumb.
  eapply AlignedDecode_CollapseWord';
    eauto using decode_word_eq_decode_unused_word,
    decode_word_eq_decode_bool,
    decode_word_eq_decode_word.
  eapply @AlignedDecodeBind2CharM; intros; eauto.
  eapply @AlignedDecodeBindCharM; intros; eauto.
  eapply @AlignedDecodeBindEnumM; intros; eauto.
  eapply @AlignedDecodeBindUnused2CharM; simpl;
    eapply DecodeMEquivAlignedDecodeM_trans;
      [ | intros; reflexivity
        |  ].
  eapply @AlignedDecodeBind4CharM; intros; eauto.
  eapply @AlignedDecodeBind4CharM; intros; eauto.
  eapply @AlignedDecodeListM; intros; eauto.
  eapply (fun H H' => @AlignedDecodeNCharM _ _ H H' 4); eauto; simpl; intros.
  eapply @AlignedDecode_ifb.
  eapply @Return_DecodeMEquivAlignedDecodeM.
  intros; higher_order_reflexivity.
  intros; higher_order_reflexivity.
Defined.

Definition IPv4_decoder_impl {sz} v :=
  Eval simpl in (projT1 EthernetHeader_decoder sz v 0 ()).

Definition pkt' : Vector.t (word 8) _ :=
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
     WO~1~0~0~0~0~0~0~0].

Definition pkt : Vector.t (word 8) _ :=
  Eval compute in Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0].

Eval vm_compute in (IPv4_decoder_impl _ pkt 0 ()).

Compute (InternetChecksum.checksum pkt).

Definition address : list char :=
  Eval compute in map (@natToWord 8) [172;16;254;1].

Lemma zero_lt_eight : (lt 0 8)%nat.
Proof. omega. Qed.

Definition fiat_ipv4_decode (buffer: list char) : option (IPv4_Packet * list char) :=
  let bs := {| padding := 0; front := WO; paddingOK := zero_lt_eight; byteString := buffer |} in
  match IPv4_decoder_impl bs () with
  | Some (pkt', bs, _) => Some (pkt', bs.(byteString))
  | None => None
  end.

Compute (fiat_ipv4_decode pkt).

Compute (InternetChecksum.checksum pkt).
