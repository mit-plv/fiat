Require Import
        Coq.omega.Omega
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Automation.Solver.

Require Import Bedrock.Word.

Ltac start_synthesizing_decoder :=
  match goal with
  | |- CorrectAlignedDecoderFor ?Invariant ?Spec =>
    try unfold Spec (*; try unfold Invariant *)
  end;

  (* Memoize any string constants *)
  (* pose_string_hyps; *)
  eapply Start_CorrectAlignedDecoderFor; simpl; intros.

Ltac align_decoders_step :=
  first [
      eapply @AlignedDecodeNatM; intros
    | eapply @AlignedDecodeBind2CharM; intros; eauto
    | eapply @AlignedDecodeBindCharM; intros; eauto
    | eapply @AlignedDecodeBind4CharM; intros; eauto
    | eapply @AlignedDecodeBindEnumM; intros; eauto
    | eapply @AlignedDecodeBindUnused2CharM; simpl;
      eapply DecodeMEquivAlignedDecodeM_trans;
      [ | intros; reflexivity
        |  ]
    |   eapply @AlignedDecodeBindUnusedCharM; simpl;
        eapply DecodeMEquivAlignedDecodeM_trans;
        [ | intros; reflexivity
          | intros ]
    | eapply @AlignedDecodeListM; intros; eauto
    | eapply @AlignedDecodeCharM; intros; eauto
    | eapply (fun H H' => @AlignedDecodeNCharM _ _ H H' 4); eauto; simpl; intros
    | eapply @AlignedDecode_shift_if_Sumb
    | eapply @AlignedDecode_shift_if_bool
    | eapply @Return_DecodeMEquivAlignedDecodeM
    | eapply @AlignedDecode_Sumb
    | eapply @AlignedDecode_ifb
    | intros; higher_order_reflexivity
    |   eapply AlignedDecode_CollapseWord';
        eauto using decode_word_eq_decode_unused_word,
        decode_word_eq_decode_bool,
        decode_word_eq_decode_word
    ].

Ltac align_decoders := repeat align_decoders_step.

Ltac synthesize_aligned_decoder :=
  start_synthesizing_decoder;
  [ match goal with
      |- CorrectDecoder ?monoid _ _ _ _ _ => normalize_compose monoid
    end;
    repeat decode_step idtac
  | cbv beta; synthesize_cache_invariant
  | cbv beta; unfold decode_nat; optimize_decoder_impl
  | ];
  cbv beta; align_decoders.

Lemma length_encode_word' sz :
  forall (w : word sz) (b : ByteString),
    bin_measure (encode_word' _ w b) = sz + bin_measure b.
Proof.
  simpl; intros.
  rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b).
  rewrite !length_ByteString_ByteStringToBoundedByteString_eq.
  rewrite <- length_encode_word' with (w := w).
  induction sz; intros;
    rewrite (shatter_word w); simpl.
  - reflexivity.
  - rewrite Core.length_ByteString_enqueue, <- IHsz.
    rewrite (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq b).
    rewrite <- (ByteStringToBoundedByteString_BoundedByteStringToByteString_eq (encode_word' _ _ _)).
    rewrite ByteString_enqueue_ByteStringToBoundedByteString_eq.
    rewrite !length_ByteString_ByteStringToBoundedByteString_eq.
    rewrite Core.length_ByteString_enqueue; reflexivity.
Qed.

Lemma length_ByteString_word
  : forall (sz : nat) (w : word sz) (b : ByteString) (ctx ctx' : CacheFormat),
    format_word w ctx ↝ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold WordOpt.format_word; simpl.
  intros; computes_to_inv; injections.
  rewrite length_encode_word'; simpl.
  unfold ByteString_id, length_ByteString; simpl; omega.
Qed.

Lemma length_ByteString_unused_word
  : forall (sz : nat) (b : ByteString) (ctx ctx' : CacheFormat),
    format_unused_word sz ctx ↝ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold format_unused_word, format_unused_word';
    intros; computes_to_inv; injections.
  rewrite length_encode_word'; simpl.
  unfold ByteString_id, length_ByteString; simpl; omega.
Qed.

Lemma length_ByteString_bool
  : forall (b : bool) (bs : ByteString) (ctx ctx' : CacheFormat),
    format_bool b ctx ↝ (bs, ctx') -> length_ByteString bs = 1.
Proof.
  unfold format_bool, format_unused_word';
    intros; computes_to_inv; injections.
  reflexivity.
Qed.

Lemma length_ByteString_ret
  : forall (b' b : ByteString) (ctx ctx' : CacheFormat),
    ret (b', ctx) ↝ (b, ctx') -> length_ByteString b = length_ByteString b'.
Proof.
  intros; computes_to_inv; injections; eauto.
Qed.

Lemma length_ByteString_compose:
  forall (format1 format2 : CacheFormat -> Comp (ByteString * CacheFormat))
         (b : ByteString) (ctx ctx' : CacheFormat)
         (n n' : nat),
    (format1 ThenC format2) ctx ↝ (b, ctx') ->
    (forall (ctx0 : CacheFormat) (b0 : ByteString) (ctx'0 : CacheFormat),
        format1 ctx0 ↝ (b0, ctx'0) -> length_ByteString b0 = n) ->
    (forall (ctx0 : CacheFormat) (b0 : ByteString) (ctx'0 : CacheFormat),
        format2 ctx0 ↝ (b0, ctx'0) -> length_ByteString b0 = n') ->
    length_ByteString b = n + n'.
Proof.
  intros.
  unfold compose, Bind2 in H; computes_to_inv.
  destruct v; destruct v0; simpl in *; injections.
  erewrite length_ByteString_enqueue_ByteString, H0, H1; eauto with arith.
Qed.

Ltac eapply_in_hyp lem :=
  match goal with
  | H:_ |- _ => eapply lem in H; [ | clear H | .. | clear H]
  end.

Ltac associate_for_ByteAlignment :=
  eapply @Guarded_CorrectAlignedEncoderThenCAssoc;
  [clear; intros ce bs ce' Comp;
   repeat first [ apply_in_hyp length_ByteString_word
                | apply_in_hyp length_ByteString_unused_word
                | apply_in_hyp length_ByteString_bool
                | eapply_in_hyp length_ByteString_compose;
                  [ | clear; intros | .. | clear; intros ]
                | eassumption]; omega
  | ].

(*Lemma CollapseCorrectAlignedEncoderFormatWord
      (addE_addE_plus :
         forall ce n m, addE (addE ce n) m = addE ce (n + m))
  : forall sz {sz'} (w' : word sz') k encoder,
    CorrectAlignedEncoder
      ((format_word (combine w' (wzero sz)))
         ThenC k)
      encoder
    -> CorrectAlignedEncoder
         ((format_unused_word sz)
            ThenC (format_word w')
            ThenC k)
         encoder.
Proof.
  intros; eapply refine_CorrectAlignedEncoder; eauto.
  intros; rewrite <- CollapseFormatWord; eauto.
  unfold compose, Bind2; f_equiv.
  unfold format_unused_word, format_unused_word'.
  repeat computes_to_econstructor; eauto.
Qed. *)

Lemma refine_format_unused_word
  : forall sz ce,
    refine (format_unused_word sz ce) (format_word (wzero sz) ce).
Proof.
  intros; unfold format_unused_word, format_unused_word'.
  repeat computes_to_econstructor; eauto.
Qed.

Lemma refine_format_bool
  : forall b ce,
    refine (format_bool b ce) (format_word (WS b WO) ce).
Proof.
  intros; unfold format_bool.
  reflexivity.
Qed.

Ltac calculate_length_ByteString :=
  intros;
  match goal with
  | H:_ ↝ _
    |- _ =>
    (first
       [ eapply (length_ByteString_composeChecksum _ _ _ _ _ _ _ H);
         try (simpl mempty; rewrite length_ByteString_ByteString_id)
       | eapply (length_ByteString_composeIf _ _ _ _ _ _ _ H);
         try (simpl mempty; rewrite length_ByteString_ByteString_id)
       | eapply (length_ByteString_compose _ _ _ _ _ _ _ H);
         try (simpl mempty; rewrite length_ByteString_ByteString_id)
       | eapply (fun H' H'' => length_ByteString_format_option _ _ _ _ _ _ _ H' H'' H)
       | eapply (length_ByteString_unused_word _ _ _ _ H)
       | eapply (length_ByteString_bool _ _ _ _ H)
       | eapply (length_ByteString_word _ _ _ _ _ H)
       | eapply (fun H' => length_ByteString_format_list _ _ _ _ _ _ H' H)
       | eapply (length_ByteString_ret _ _ _ _ H) ]);
    clear H
  end.


Ltac collapse_unaligned_words :=
  intros; eapply refine_CorrectAlignedEncoder;
  [ eauto ; intros; try set_refine_evar; repeat eapply refine_CollapseFormatWord; intros;
    unfold format_nat; eauto using refine_format_bool, refine_format_unused_word;
    reflexivity
  | ].

Ltac decompose_aligned_encoder :=
  repeat first [
           eapply @CorrectAlignedEncoderForIPChecksumThenC
         | associate_for_ByteAlignment
         | match goal with
             |- context[ByteString_id] => apply @CorrectAlignedEncoderForThenC
           end
         | apply @CorrectAlignedEncoderForDoneC].

Ltac start_synthesizing_encoder :=
  lazymatch goal with
  | |- CorrectAlignedEncoderFor ?Invariant ?Spec =>
    try unfold Spec; try unfold Invariant
  end;
  (* Memoize any string constants *)
  (*pose_string_hyps; *)
  eexists; simpl; intros.

Ltac align_encoder_step :=
  first
    [ (*apply CorrectAlignedEncoderForFormatList*) fail
    | apply CorrectAlignedEncoderForFormatChar; eauto
    | apply CorrectAlignedEncoderForFormatNat
    | intros; eapply CorrectAlignedEncoderForFormatNChar with (sz := 2); eauto
    | intros; eapply CorrectAlignedEncoderForFormatNChar with (sz := 3); eauto
    | intros; eapply CorrectAlignedEncoderForFormatNChar with (sz := 4); eauto
    | intros; eapply CorrectAlignedEncoderForFormatNChar with (sz := 5); eauto
    | collapse_unaligned_words].

Ltac align_encoder :=
  repeat align_encoder_step.

Ltac synthesize_aligned_encoder :=
  start_synthesizing_encoder;
  decompose_aligned_encoder;
  repeat align_encoder_step.
