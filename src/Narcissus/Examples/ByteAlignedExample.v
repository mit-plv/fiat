Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.BinLib.AlignedMonads
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore.

Instance ByteStringQueueMonoid : Monoid ByteString := ByteStringQueueMonoid.

Definition simple_record := ((word 16) * list (word 8))%type.

Definition Simple_Format
           (p : simple_record) :=
        format_nat 8 (|snd p|)
  ThenC format_word (fst p)
  ThenC format_list format_word (snd p)
  DoneC.

Definition Simply_OK (p : simple_record) :=
  ((|snd p|) < pow2 8)%nat.

Arguments split1 : simpl never.
Arguments split2 : simpl never.
Arguments weq : simpl never.
Arguments natToWord : simpl never.
Arguments Guarded_Vector_split : simpl never.
Arguments Core.append_word : simpl never.

Definition refine_simple_format
  : { numBytes : _ &
    { v : _ &
    { c : _ & forall (p : simple_record)
                     (p_OK : Simply_OK p),
          refine (Simple_Format p ())
                 (ret (@build_aligned_ByteString (numBytes p) (v p), c p)) } } }.
Proof.
  unfold Simple_Format.
  eexists _, _, _; intros.
  (* Step 1: simplification with monad laws so that any complex
       subformats are inlined properly. (Not needed for this example) *)
  eapply refine_refineEquiv_Proper;
    [ unfold flip;
      repeat first
             [ etransitivity; [ apply refineEquiv_compose_compose with (monoid := monoid) | idtac ]
             | etransitivity; [ apply refineEquiv_compose_Done with (monoid := monoid) | idtac ]
             | apply refineEquiv_under_compose with (monoid := monoid) ];
      intros; higher_order_reflexivity
    | reflexivity | ].
    etransitivity.
    (* Replace formats with byte-aligned versions. *)
    eapply AlignedFormatChar; eauto.
    eapply AlignedFormat2Char; eauto.
    eapply AlignedFormatListDoneC with (A_OK := fun _ => True); intros; eauto.
    rewrite aligned_format_char_eq.
    encoder_reflexivity.
    encoder_reflexivity.
Defined.

Definition byte_aligned_simple_encoder
             (r : simple_record)
  := Eval simpl in (projT1 (projT2 refine_simple_format) r).

Import Vectors.Vector.VectorNotations.
Print byte_aligned_simple_encoder.

Definition Simple_Format_decoder
  : CorrectDecoderFor Simply_OK Simple_Format.
Proof.
  start_synthesizing_decoder.
  normalize_compose monoid.
  repeat decode_step idtac.
  intros; eauto using FixedList_predicate_rest_True.
  synthesize_cache_invariant.
  cbv beta; optimize_decoder_impl.
Defined.

Definition SimpleDecoderImpl
    := Eval simpl in (proj1_sig Simple_Format_decoder).

Ltac rewrite_DecodeOpt2_fmap :=
  set_refine_evar;
  progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
  ?DecodeOpt2_fmap_if_bool;
  subst_refine_evar.

Local Open Scope AlignedDecodeM_scope.

Definition ByteAligned_SimpleDecoderTrial
  : {impl : _ & DecodeMEquivAlignedDecodeM (fst SimpleDecoderImpl) impl}.
Proof.
  eexists; intros.
  unfold SimpleDecoderImpl.
  eapply (AlignedDecodeNatM (C := simple_record) (cache := test_cache)); intros.
  eapply (AlignedDecodeBind2CharM (cache := test_cache)); intros; eauto.
  instantiate (1 := fun b0 numBytes => l <- ListAlignedDecodeM _ b; return (b0, l)).
  simpl.
  eapply DecodeMEquivAlignedDecodeM_trans; simpl; intros.
  eapply AlignedDecodeListM with (A_decode := decode_word (sz := 8)) (n := b) (t := fun l bs cd' => Some (b0, l, bs, cd')).
  eapply (AlignedDecodeCharM (cache := test_cache)); intros; eauto.
  intros; eapply Return_DecodeMEquivAlignedDecodeM.
  simpl; reflexivity.
  simpl; reflexivity.
Defined.

Definition ByteAligned_SimpleDecoderTrial_Impl := Eval simpl in projT1 ByteAligned_SimpleDecoderTrial.

Print ByteAligned_SimpleDecoderTrial_Impl.

Definition ByteAligned_SimpleDecoderImpl {A}
           (f : _ -> A)
           n
  : {impl : _ & forall (v : Vector.t _ (3 + n)),
         f (fst SimpleDecoderImpl (build_aligned_ByteString v) ()) =
         impl v () }.
Proof.
  eexists _; intros.
  etransitivity.
  unfold SimpleDecoderImpl.
  set_refine_evar; simpl.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  rewrite (@AlignedDecodeNat test_cache).
  subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  rewrite (@AlignedDecode2Char test_cache).
  subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  erewrite optimize_align_decode_list.
  rewrite Ifopt_Ifopt; simpl.
  etransitivity.
  eapply optimize_under_if_opt; simpl; intros.
  higher_order_reflexivity.
  reflexivity.
  Focus 2.
  clear H; intros.
  etransitivity.
  match goal with
    |- ?b = _ =>
    let b' := (eval pattern (build_aligned_ByteString v0) in b) in
    let b' := match b' with ?f _ => f end in
      eapply (@optimize_Guarded_Decode n0 _ 1 b')
  end.
  destruct n0 as [ | [ | ?] ]; intros; try omega.
  apply (@decode_word_aligned_ByteString_overflow test_cache) with (sz := 1); auto.
  destruct n0 as [ | ?]; intros; try omega.
  higher_order_reflexivity.
  instantiate (1 := fun n1 v1 (cd0 : CacheDecode) =>
                      If NPeano.leb 1 n1 Then (Some ((Vector.hd (Guarded_Vector_split 1 n1 v1), @existT _ (Vector.t _) _ (Vector.tl (Guarded_Vector_split 1 n1 v1))), cd0)) Else None).
  simpl; find_if_inside; simpl; try reflexivity.
  pattern n0, v0; apply Vector.caseS; simpl; intros.
  unfold decode_word, WordOpt.decode_word.
  rewrite aligned_decode_char_eq; reflexivity.
  subst_refine_evar; higher_order_reflexivity.
  higher_order_reflexivity.
Defined.

Definition ByteAligned_SimpleDecoderImpl' n :=
  Eval simpl in (projT1 (ByteAligned_SimpleDecoderImpl id n)).

Print ByteAligned_SimpleDecoderImpl'.
