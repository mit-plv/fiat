Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Coq.ZArith.ZArith
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Formats
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.NormalizeFormats.

Require Import Bedrock.Word.

Ltac start_synthesizing_decoder :=
  match goal with
  | |- CorrectAlignedDecoderFor ?Invariant ?Spec =>
    try unfold Spec (*; try unfold Invariant *)
  end;

  (* Memoize any string constants *)
  (* pose_string_hyps; *)
  eapply Start_CorrectAlignedDecoderFor; simpl; intros.

Ltac eapply_formatnchars_thm_simplified thm sz :=
  let tm := constr:(fun cache cacheAddNat p1 p2 => thm cache cacheAddNat p1 p2 sz) in
  let tm_t := type of tm in
  let tm_t := (eval unfold GetCurrentBytes, SetCurrentBytes in tm_t) in
  let tm_t := (eval simpl in tm_t) in
  eapply (tm: tm_t).

Ltac align_decoders_step :=
  first [
      match goal with
      | |- IterateBoundedIndex.prim_and _ _ =>
        apply IterateBoundedIndex.Build_prim_and; intros;
        [ eapply DecodeMEquivAlignedDecodeM_trans;
          [ | intros; symmetry;
              cbv beta; simpl; unfold decode_nat, sequence_Decode; optimize_decoder_impl |
            try (instantiate (1 := ilist.icons _ _); simpl; intros; higher_order_reflexivity)]
        | try exact I]
      | |- IterateBoundedIndex.Iterate_Ensemble_BoundedIndex _ =>
        apply IterateBoundedIndex.Build_prim_and; intros;
        [ eapply DecodeMEquivAlignedDecodeM_trans;
          [ | intros; symmetry;
              cbv beta; simpl; unfold decode_nat, sequence_Decode; optimize_decoder_impl |
            try (instantiate (1 := ilist.icons _ _); simpl; intros; higher_order_reflexivity)]
        | try exact I]
      | |- context [ decode_string_with_term_char ?term_char _ _] =>
      eapply (fun H H' => @AlignedDecodeStringTermM _ _ H H' _ (NToWord 8 (Ascii.N_of_ascii term_char))); intros; eauto
      end
    | eapply @AlignedDecodeNatM; intros
    | eapply @AlignedDecodeByteBufferM; intros; eauto
    | eapply @AlignedDecodeBind2CharM; intros; eauto
    | eapply @AlignedDecodeBindCharM; intros; eauto
    | eapply @AlignedDecodeBind3CharM; intros; eauto
    | eapply @AlignedDecodeBind4CharM; intros; eauto
    | eapply @AlignedDecodeBind8CharM; intros; eauto
    | eapply @AlignedDecodeBindEnum; intros; eauto
    | let H' := fresh in
      pose proof (fun C D => @AlignedDecodeBindEnumM _ _ C D 2) as H';
      simpl in H'; eapply H'; eauto; intros
    | let H' := fresh in
      pose proof (fun C D => @AlignedDecodeBindEnumM _ _ C D 3) as H';
      simpl in H'; eapply H'; eauto; intros
    | let H' := fresh in
      pose proof (fun C D => @AlignedDecodeBindEnumM _ _ C D 4) as H';
      simpl in H'; eapply H'; eauto; intros
    | eapply @AlignedDecodeBindUnused2CharM; simpl; eauto;
      eapply DecodeMEquivAlignedDecodeM_trans;
      [ | intros; reflexivity
        |  ]
    | eapply @AlignedDecodeBindUnusedCharM; simpl; eauto;
      eapply DecodeMEquivAlignedDecodeM_trans;
      [ | intros; reflexivity
        |  ]
    | eapply @AlignedDecodeSumTypeM; intros; eauto
    | eapply @AlignedDecodeListM; intros; eauto
    | eapply @AlignedDecodeCharM; intros; eauto
    | eapply (fun H H' => @AlignedDecodeNCharM _ _ H H' 8); eauto; simpl; intros
    | eapply (fun H H' => @AlignedDecodeNCharM _ _ H H' 4); eauto; simpl; intros
    | eapply (fun H H' => AlignedDecodeNCharM H H'  (m := 2)); eauto; simpl; intros
    | eapply (AlignedDecodeNUnusedCharM _ _ (m := 2)); eauto; simpl; intros
    | eapply @AlignedDecode_shift_if_Sumb
    | eapply @AlignedDecode_shift_if_bool
    | eapply @Return_DecodeMEquivAlignedDecodeM
    | eapply @AlignedDecode_Sumb
    | eapply AlignedDecode_ifopt; intros
    | match goal with
      |- DecodeMEquivAlignedDecodeM (fun b c => If_Opt_Then_Else _ _ _) _ =>
      eapply DecodeMEquivAlignedDecodeM_trans;
        [ eapply AlignedDecode_ifopt | intros; reflexivity | intros; higher_order_reflexivity ];
        intros
    end
    | let H := fresh in pose proof @AlignedDecode_if_Sumb_dep as H;
                        eapply H; clear H;
                        [ solve [eauto] | solve [eauto] | | ]
    | eapply @AlignedDecode_ifb
    | eapply @AlignedDecode_ifb_both
    | eapply @AlignedDecode_ifb_dep; [ solve [eauto] | solve [eauto] | | ]
    | eapply @AlignedDecodeBindOption; intros; eauto
    | eapply @AlignedDecode_Throw
    | intros; higher_order_reflexivity
    | eapply @AlignedDecode_CollapseEnumWord
    | eapply @AlignedDecode_CollapseWord';
      eauto using decode_word_eq_decode_unused_word,
      decode_word_eq_decode_bool,
      decode_word_eq_decode_nat,
      decode_word_eq_decode_word
    | eapply @AlignedDecodeBindDuplicate;
      [ simpl; intros;
        f_equiv; apply functional_extensionality; intros;
        repeat (apply functional_extensionality; intros);
        symmetry;
        repeat match goal with
                 |- (if ?b then ?tt else ?te) = ?t' (?f ?d) ?a ?v' ?cd =>
                 etransitivity;
                   [ eapply (FindFuncIf a v' cd b d f tt te);
                     [ try higher_order_reflexivity | higher_order_reflexivity | higher_order_reflexivity]
                   | higher_order_reflexivity ]
               |  |- (`(a, t'', cd'') <- ?decode_A' ?v' ?cd'; @?t' a t'' cd'') = _ ?d' _ _ _ =>
                  etransitivity;
                    [eapply FindFuncBind with (decode_A := decode_A')
                                              (v0 := v') (cd0 := cd')
                                              (t := t')
                                              (d := d'); intros
                    | higher_order_reflexivity ]
               end
        | simpl; intros
        | intros; eapply functional_extensionality_dep; intros; eauto
        | intros; eapply functional_extensionality_dep; intros; eauto ]
    ].

Ltac align_decoders := repeat align_decoders_step.

Ltac synthesize_aligned_decoder :=
  sequence_four_tactics
    ltac:(start_synthesizing_decoder)
           ltac:(NormalizeFormats.normalize_format; apply_rules)
                  ltac:(cbv beta; synthesize_cache_invariant)
                         ltac:(cbv beta; unfold decode_nat, sequence_Decode;
                               optimize_decoder_impl)
                                ltac:(cbv beta; align_decoders)
    continue_on_fail_2
    continue_on_fail_1
    continue_on_fail
.

Lemma length_encode_word' sz :
  forall (w : word sz) (b : ByteString),
    bin_measure (encode_word' _ w b) = sz + bin_measure b.
Proof.
  simpl; intros.
  rewrite <- length_encode_word' with (w := w).
  induction sz; intros;
    rewrite (shatter_word w); simpl.
  - reflexivity.
  - reflexivity.
Qed.

Lemma length_ByteString_word
  : forall (sz : nat) (w : word sz) (b : ByteString) (ctx ctx' : CacheFormat),
    format_word w ctx ↝ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold WordOpt.format_word; simpl.
  intros; computes_to_inv; injections.
  rewrite length_encode_word'; simpl.
  unfold ByteString_id, length_ByteString; simpl; Lia.lia.
Qed.

Lemma length_ByteString_unused_word {S}
  : forall (s : S) (sz : nat) (b : ByteString) (ctx ctx' : CacheFormat),
    format_unused_word sz s ctx ↝ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold format_unused_word, Compose_Format;
    intros; rewrite unfold_computes in H; destruct_ex; split_and.
  unfold format_word in H0; computes_to_inv; injections.
  rewrite length_encode_word'; simpl.
  unfold ByteString_id, length_ByteString; simpl; Lia.lia.
Qed.

Lemma length_ByteString_bool
  : forall (b : bool) (bs : ByteString) (ctx ctx' : CacheFormat),
    format_bool b ctx ↝ (bs, ctx') -> length_ByteString bs = 1.
Proof.
  unfold format_bool;
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

Lemma length_ByteString_map {S S'}
  : forall (sz : nat) (f : S -> S') (format : FormatM S' _) (s : S) (b : ByteString) (ctx ctx' : CacheFormat),
    (format (f s) ctx ∋ (b, ctx') -> length_ByteString b = sz)
    -> Projection_Format format f s ctx ∋ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold Projection_Format, Compose_Format; intros.
  rewrite unfold_computes in H0; destruct_ex; intuition; subst.
  eapply H; eauto.
Qed.

Corollary length_ByteString_map_word {S}
  : forall (sz : nat) (f : S -> word sz) (s : S) (b : ByteString) (ctx ctx' : CacheFormat),
    Projection_Format format_word f s ctx ∋ (b, ctx') -> length_ByteString b = sz.
Proof.
  intros; eapply length_ByteString_map; eauto using length_ByteString_word.
Qed.

Corollary length_ByteString_map_nat {S}
  : forall (sz : nat) (f : S -> nat) (s : S) (b : ByteString) (ctx ctx' : CacheFormat),
    Projection_Format (format_nat sz) f s ctx ∋ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold format_nat; intros.
  apply EquivFormat_Projection_Format in H.
  eauto using length_ByteString_word.
Qed.

Corollary length_ByteString_map_bool {S}
  : forall (f : S -> bool) (s : S) (b : ByteString) (ctx ctx' : CacheFormat),
    Projection_Format format_bool f s ctx ∋ (b, ctx') -> length_ByteString b = 1.
Proof.
  intros; eapply length_ByteString_map; eauto using length_ByteString_bool.
Qed.

Lemma length_ByteString_map_option {S S'}
  : forall (sz : nat) (f : S -> option S')
           (format_Some : FormatM S' _)
           (format_None : FormatM () _)
           (s : S) (b : ByteString) (ctx ctx' : CacheFormat),
    (forall s', format_Some s' ctx ∋ (b, ctx') -> length_ByteString b = sz)
    -> (format_None () ctx ∋ (b, ctx') -> length_ByteString b = sz)
    -> Projection_Format (Option.format_option format_Some format_None) f s ctx ∋ (b, ctx') -> length_ByteString b = sz.
Proof.
  unfold Projection_Format, Compose_Format; intros.
  rewrite unfold_computes in H1; destruct_ex; intuition; subst.
  destruct (f s); simpl in *; eauto.
Qed.

Corollary length_ByteString_map_enum {S'}
  : forall (len sz : nat)
           (codes : Vector.t (word sz) (S len))
           (f : S' -> Fin.t (S len)) (s : S') (b : ByteString) (ctx ctx' : CacheFormat),
    Projection_Format (format_enum codes) f s ctx ∋ (b, ctx') -> length_ByteString b = sz.
Proof.
  intros; eapply length_ByteString_map; eauto.
  eauto using length_ByteString_word.
Qed.

Lemma length_ByteString_Projection_compose {S S' S''}:
    forall (format1 : FormatM S ByteString)
           (f : S'' -> S')
           (g : S' -> S)
           (b : ByteString) s (ctx ctx' : CacheFormat)
           (n : nat),
      (Projection_Format (Projection_Format format1 g) f) s ctx ↝ (b, ctx') ->
      (forall (ctx0 : CacheFormat) (b0 : ByteString) (ctx'0 : CacheFormat),
          (Projection_Format format1 (Basics.compose g f)) s ctx0 ↝ (b0, ctx'0)
          -> length_ByteString b0 = n) ->
      length_ByteString b = n.
  Proof.
    intros.
    eapply H0.
    eapply EquivFormat_Projection_Format in H.
    eapply EquivFormat_Projection_Format in H.
    eapply EquivFormat_Projection_Format; eauto.
  Qed.

  Lemma encoder_empty_cache_OK {S1 S2}
        (format_A : FormatM S1 ByteString)
        (format_B : FormatM S2 ByteString)
        (encode_B : forall sz, AlignedEncodeM sz)
        (encoder_B_OK : CorrectAlignedEncoder format_B encode_B)
    : forall (s1 : S1) (s2 : S2) (env : CacheFormat) (tenv' tenv'' : ByteString * CacheFormat),
      format_B s2 env ∋ tenv' ->
      format_A s1 (snd tenv') ∋ tenv'' ->
      exists tenv3 tenv4 : _ * CacheFormat,
        projT1 encoder_B_OK s2 env = Some tenv3
        /\ format_A s1 (snd tenv3) ∋ tenv4.
  Proof.
    intros.
    destruct tenv'; destruct tenv''; simpl in *.
    match goal with
      |- exists _ _, ?b = _ /\ _ =>  destruct b as [ [? ?] | ] eqn: ?
    end.
    - eexists _, _; simpl in *; split; intros; eauto.
      simpl in *.
      destruct c; destruct c1; eauto.
    - eapply (proj1 (projT2 encoder_B_OK)) in Heqo.
      eapply Heqo in H; intuition.
  Qed.

  Ltac calculate_length_ByteString' :=
    repeat first [ apply_in_hyp @length_ByteString_map_word
               | apply_in_hyp
               | apply_in_hyp @length_ByteString_map_bool
               | apply_in_hyp @length_ByteString_word
               | apply_in_hyp @length_ByteString_unused_word
               | apply_in_hyp @length_ByteString_bool
               | eapply_in_hyp;
                 [ | clear; intros | .. | clear; intros ]
               | match goal with
                 | H :_ ↝ _ |- _  =>
                   eapply (length_ByteString_Projection_compose _ _ _ _ _ _ _ _ H);
                   clear H; intros ? ? ? H
                 end
               | eapply_in_hyp @length_ByteString_map_option;
                 [ | clear; intros | .. | clear; intros ]
               | apply_in_hyp @length_ByteString_map_nat
               | apply_in_hyp @length_ByteString_map_enum
               | eapply_in_hyp @length_ByteString_compose;
                 [ | clear; intros | .. | clear; intros ]
               | eassumption].

Ltac associate_for_ByteAlignment :=
  eapply @Guarded_CorrectAlignedEncoderThenCAssoc;
  [clear; intros ce bs ce' Comp ? ;
   calculate_length_ByteString'; Lia.lia
  | ].

(*Lemma CorrectAlignedEncoderForFormatOption {S}
     : forall (format_Some : FormatM S ByteString) (encode_A : forall sz : nat, AlignedEncodeM sz),
       CorrectAlignedEncoder format_A encode_A ->
       CorrectAlignedEncoder (format_list format_A) (AlignedEncodeList encode_A)

Lemma
  CorrectAlignedEncoder
    (Option.format_option format_word (format_unused_word 16) ◦ UrgentPointer ++
     format_list format_word ◦ Options ++ format_list format_word ◦ Payload) ?encode_A *)

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

Lemma refine_format_unused_word {S}
  : forall sz (s : S) ce,
    refine (format_unused_word sz s ce) (format_word (wzero sz) ce).
Proof.
  intros; unfold format_unused_word, Compose_Format;
    intros ? ?.
  apply unfold_computes; eexists; split; eauto.
  apply unfold_computes; eauto.
Qed.

Lemma refine_format_bool
  : forall b ce,
    refine (format_bool b ce) (format_word (WS b WO) ce).
Proof.
  intros; unfold format_bool.
  reflexivity.
Qed.

Lemma refine_format_bool_map {S}
      (f : S -> bool)
  : forall s ce,
    refine (FMapFormat.Projection_Format format_bool f s ce) (FMapFormat.Projection_Format format_word (fun s => (WS (f s) WO)) s ce).
Proof.
  intros; unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format; intros ? ?.
  rewrite unfold_computes in H; destruct_ex; intuition.
  apply unfold_computes; eexists; split; eauto; subst.
  eapply refine_format_bool; eauto.
Qed.

Lemma refine_format_option sz {S}
      (Some_format : FormatM S _)
      (None_format : FormatM () _)
      (f : S -> word sz)
      (f' : word sz)
      (refine_Some : forall (s : S) (env : CacheFormat), refine (Some_format s env) ((format_word ◦ f) s env))
      (refine_None : forall (env : CacheFormat), refine (None_format () env) ((format_word ◦ (fun _ => f')) () env))
  : forall (s : option S) ce,
    refine (Option.format_option Some_format None_format s ce)
           ((format_word ◦ (fun s => Ifopt s as s' Then f s' Else f')) s ce).
Proof.
  intros; destruct s; simpl; eauto.
  eapply refine_Some.
Qed.

Lemma refine_format_option_map sz {S S'}
      (g : S' -> option S)
      (Some_format : FormatM S _)
      (None_format : FormatM () _)
      (f : S -> word sz)
      (f' : word sz)
      (refine_Some : forall (s : S) (env : CacheFormat), refine (Some_format s env) ((format_word ◦ f) s env))
      (refine_None : forall (env : CacheFormat), refine (None_format () env) ((format_word ◦ (fun _ => f')) () env))
  : forall s ce,
    refine (FMapFormat.Projection_Format (Option.format_option Some_format None_format) g s ce)
           (FMapFormat.Projection_Format format_word
                                         ((fun s => Ifopt (g s) as s' Then f s' Else f')) s ce).
Proof.
  intros; unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format; intros ? ?.
  rewrite unfold_computes in H; destruct_ex; intuition.
  apply unfold_computes; eexists; split; eauto; subst.
  eapply refine_format_option; eauto.
  apply EquivFormat_Projection_Format in H0; eauto.
Qed.

Lemma refine_format_compose_map sz {S S' S''}
      (format_S'' : FormatM S'' _)
      (f : S -> S')
      (g : S' -> S'')
      (f' : S -> word sz)
      (refine_proj : forall (s : S) (env : CacheFormat),
          refine (FMapFormat.Projection_Format format_S'' (Basics.compose g f) s env)
                 ((format_word ◦ f') s env))
  : forall s ce,
    refine (FMapFormat.Projection_Format (FMapFormat.Projection_Format format_S'' g) f s ce)
           (FMapFormat.Projection_Format format_word f' s ce).
Proof.
  intros; rewrite <- refine_proj.
  intros; unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format; intros ? ?.
  rewrite unfold_computes in H; destruct_ex; intuition.
  apply unfold_computes; eexists; split; eauto; subst.
  apply unfold_computes.
  eauto.
Qed.

Lemma refine_format_nat_map {S}
      {sz}
      (f : S -> nat)
  : forall s ce,
    refine (FMapFormat.Projection_Format (format_nat sz) f s ce)
           (FMapFormat.Projection_Format format_word (Basics.compose (natToWord sz) f) s ce).
Proof.
  intros; unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format, format_nat; intros ? ?.
  rewrite unfold_computes in H; destruct_ex; intuition.
  apply unfold_computes; eexists; split; eauto; subst.
  try rewrite <- plus_n_O with (n := f s).
  eauto.
Qed.

Lemma refine_format_enum_map {S}
      {sz sz'}
      (f : S -> Fin.t (1 + sz'))
      (tb : Vector.t (word sz) _)
  : forall s ce,
    refine (FMapFormat.Projection_Format (format_enum tb) f s ce)
           (FMapFormat.Projection_Format format_word (Basics.compose (Vector.nth tb) f) s ce).
Proof.
  intros; unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format, format_enum; intros ? ?.
  rewrite unfold_computes in H; destruct_ex; intuition.
  apply unfold_computes; eexists; split; eauto; subst.
  eauto.
Qed.

Lemma refine_format_unused_word_map {S}
  : forall sz (s : S) ce,
    refine (format_unused_word sz s ce) (FMapFormat.Projection_Format format_word (fun s => wzero sz) s ce).
Proof.
  unfold format_unused_word, FMapFormat.Projection_Format, Compose_Format; intros;
    intros ? ?.
  rewrite unfold_computes in H; destruct_ex; intuition; subst.
  apply unfold_computes; eexists; split; eauto.
  apply unfold_computes; eauto.
Qed.

Lemma refine_format_word_map {S}
      {sz}
      (f : S -> word sz)
  : forall s ce,
    refine (FMapFormat.Projection_Format format_word f s ce) (format_word (f s) ce).
Proof.
  intros; unfold FMapFormat.Projection_Format, FMapFormat.Compose_Format; intros ? ?.
  apply unfold_computes; eexists; split; eauto.
Qed.

Lemma length_ByteString_bytebuffer
  : forall (ctx : CacheFormat) (b : ByteString) (ctx' : CacheFormat) (bb : { n : nat & ByteBuffer.t n}),
    format_bytebuffer bb ctx ∋ (b, ctx') -> length_ByteString b = 8 * projT1 bb.
  intros.
  destruct bb; simpl in *.
  unfold format_bytebuffer in H.
  revert ctx b ctx' H; induction t; intros.
  - simpl in *; computes_to_inv; subst; injections.
    reflexivity.
  - simpl in *; unfold Bind2 in *; computes_to_inv; subst;
      injections; destruct v; simpl in *.
    destruct v0.
    rewrite length_ByteString_enqueue_ByteString.
    apply IHt in H'.
    simpl; rewrite H'.
    apply length_ByteString_word in H; subst; Lia.lia.
Qed.

Lemma length_ByteString_Projection {S S'}:
  forall (format1 : FormatM S ByteString)
         (f : S' -> S)
         (b : ByteString) s (ctx ctx' : CacheFormat)
         (n : nat),
    (Projection_Format format1 f)%format s ctx ↝ (b, ctx') ->
    (forall (ctx0 : CacheFormat) (b0 : ByteString) (ctx'0 : CacheFormat),
        format1 (f s) ctx0 ↝ (b0, ctx'0) -> length_ByteString b0 = n) ->
    length_ByteString b = n.
Proof.
  intros.
  eapply H0.
  eapply EquivFormat_Projection_Format; eauto.
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
       | eapply (length_ByteString_Projection _ _ _ _ _ _ _ H)
       | eapply (length_ByteString_Projection_compose _ _ _ _ _ _ _ _ H);
         clear H; intros ? ? ? H; calculate_length_ByteString
       | eapply (fun H' H'' => length_ByteString_format_option _ _ _ _ _ _ _ H' H'' H)
       | eapply (length_ByteString_unused_word _ _ _ _ _ H)
       | eapply (length_ByteString_bool _ _ _ _ H)
       | eapply (length_ByteString_word _ _ _ _ _ H)
       | eapply (fun H' => length_ByteString_format_list _ _ _ _ _ _ H' H)
       | eapply (length_ByteString_Projection _ _ _ _ _ _ _ H)
       | eapply (length_ByteString_bytebuffer _ _ _ _ H)
       | eapply (length_ByteString_ret _ _ _ _ H) ]);
    clear H
  end.

  Lemma format_word_inhabited' {S} (P : Prop)
        {sz : nat}
        (f : S -> word sz)
        s env
    : (forall (v : ByteString * CacheFormat), (format_word ◦ f) s env ∌ v) ->
      P.
  Proof.
    intros; elimtype False.
    eapply H.
    eapply refine_Projection_Format.
    unfold format_word.
    eauto.
  Qed.

  Lemma format_word_inhabited {S}
        {sz : nat}
        (f : S -> word sz)
        (format_S : FormatM S ByteString)
        s env
    : (forall (v : ByteString * CacheFormat), (format_word ◦ f) s env ∌ v) ->
      forall v : ByteString * CacheFormat,
        format_S s env ∌ v.
  Proof.
    intros; intro.
    eapply H.
    eapply refine_Projection_Format.
    unfold format_word.
    eauto.
  Qed.

  Ltac collapse_unaligned_words :=
    intros;
    eapply refine_CorrectAlignedEncoder;
    [ split;
      [repeat (eauto ; intros; eapply refine_CollapseFormatWord'; eauto);
       unfold format_nat;
       repeat first [ eapply refine_format_compose_map; intros
                    | eapply refine_format_option_map; intros
                    | eapply refine_format_bool_map
                    | eauto using refine_format_bool, refine_format_unused_word_map,
                      refine_format_bool_map, refine_format_unused_word,
                      refine_format_option_map, refine_format_enum_map,
                      refine_format_nat_map];
       reflexivity
      | eapply format_word_inhabited ]
    | ].


  Ltac start_synthesizing_encoder :=
    lazymatch goal with
    | |- CorrectAlignedEncoderFor ?Spec =>
      try unfold Spec
    end;
    (* Memoize any string constants *)
    (*pose_string_hyps; *)
    eexists; simpl; intros.

(* Redefine this tactic to implement new encoder rules *)
Ltac new_encoder_rules := fail.

Ltac align_encoder_step :=
  first
    [ match goal with
    | |- CorrectAlignedEncoder (_ ++ _ ++ _) _ => associate_for_ByteAlignment
    end
  | match goal with
    | |- CorrectAlignedEncoder (Either _ Or _) _ =>
      eapply CorrectAlignedEncoderEither_E;
      unshelve (instantiate (1 := _));
      [ repeat align_encoder_step
      | eexists; reflexivity ]
    end
  | new_encoder_rules
  | eapply CorrectAlignedEncoderForFormatList; unshelve (instantiate (1 := _));
    eauto using encoder_empty_cache_OK
  | eapply CorrectAlignedEncoderForFormatVector; unshelve (instantiate (1 := _));
    eauto using encoder_empty_cache_OK
  | apply CorrectAlignedEncoderForFormatChar; eauto
  | apply CorrectAlignedEncoderForFormatNat
  | apply CorrectAlignedEncoderForFormat2Nat; eauto
  | apply CorrectAlignedEncoderForFormatEnum
  | eapply CorrectAlignedEncoderForFormatByteBuffer; eauto using encoder_empty_cache_OK
  | eapply CorrectAlignedEncoderProjection
  | eapply (fun H H' => CorrectAlignedEncoderForFormatNEnum H H' 2); [ solve [ eauto ] | solve [ eauto ] ]
  | eapply (fun H H' => CorrectAlignedEncoderForFormatNEnum H H' 3); [ solve [ eauto ] | solve [ eauto ] ]
  | eapply CorrectAlignedEncoderForFormatUnusedWord
  | eapply CorrectAlignedEncoderForFormatOption
  | intros; try collapse_unaligned_words; eapply CorrectAlignedEncoderProjection; (solve
     [ eapply CorrectAlignedEncoderForFormatNChar with (sz := 2); eauto ])
  | intros;
    match goal with
    | |- CorrectAlignedEncoder (format_word (sz:=?bsz)) _ =>
        (* Probably should check if [bsz] is closed. *)
        let csz := eval compute in (bsz / 8) in
        eapply CorrectAlignedEncoderForFormatNChar with (sz := csz); eauto
    end
  | match goal with
    | |- CorrectAlignedEncoder empty_Format _ =>
      eapply CorrectAlignedEncoderForDoneC
    end
  | match goal with
    | |- CorrectAlignedEncoder (_ ++ _) _ =>
      eapply @CorrectAlignedEncoderForThenC; [  | unshelve (instantiate (1 := _));
                                                  [try collapse_unaligned_words
                                                  | try eauto using encoder_empty_cache_OK ] ]
    end ].

Ltac normalize_encoder_format :=
  eapply CorrectAlignedEncoder_morphism;
  [ repeat (normalize_step ByteStringQueueMonoid)
  | intros; reflexivity
  | idtac ].

Ltac synthesize_aligned_encoder :=
  start_synthesizing_encoder;
  normalize_encoder_format;
  repeat align_encoder_step.


Global Opaque cache_inv_Property.
Global Opaque CorrectDecoder.
Global Arguments andb : simpl never.
Global Arguments pow2 : simpl never.
Arguments word_indexed : simpl never.
Arguments weqb : simpl never.

Ltac encoder_reflexivity :=
  match goal with
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c ?d ?e ?f), ?store' ?a ?b ?c ?d ?e ?f)) =>
    let encoder'' := (eval pattern a, b, c, d, e, f in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c, d, e, f in store) in
    let store'' := (match store'' with ?store _ _ _ _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c ?d ?e), ?store' ?a ?b ?c ?d ?e)) =>
    let encoder'' := (eval pattern a, b, c, d, e in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c, d, e in store) in
    let store'' := (match store'' with ?store _ _ _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c ?d), ?store' ?a ?b ?c ?d)) =>
    let encoder'' := (eval pattern a, b, c, d in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c, d in store) in
    let store'' := (match store'' with ?store _ _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b ?c), ?store' ?a ?b ?c)) =>
    let encoder'' := (eval pattern a, b, c in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ _ => encoder end) in
    let store'' := (eval pattern a, b, c in store) in
    let store'' := (match store'' with ?store _ _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?a ?b), ?store' ?a ?b)) =>
    let encoder'' := (eval pattern a, b in encoder) in
    let encoder'' := (match encoder'' with ?encoder _ _ => encoder end) in
    let store'' := (eval pattern a, b in store) in
    let store'' := (match store'' with ?store _ _ => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  | |- refine (ret (build_aligned_ByteString ?encoder, ?store))
              (ret (build_aligned_ByteString (?encoder' ?p), ?store' ?p)) =>
    let encoder'' := (eval pattern p in encoder) in
    let encoder'' := (match encoder'' with ?encoder p => encoder end) in
    let store'' := (eval pattern p in store) in
    let store'' := (match store'' with ?store p => store end) in
    unify encoder' encoder''; unify store' store'';
    reflexivity
  end.

  Ltac rewrite_DecodeOpt2_fmap :=
    set_refine_evar;
    progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
    ?DecodeOpt2_fmap_if_bool;
    subst_refine_evar.
