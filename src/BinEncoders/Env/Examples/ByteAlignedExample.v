Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.BinLib.AlignedByteString
        Fiat.BinEncoders.Env.BinLib.AlignWord
        Fiat.BinEncoders.Env.BinLib.AlignedDecoders
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt.

Instance ByteStringQueueTransformer : Transformer ByteString := ByteStringQueueTransformer.

Definition simple_record := ((word 16) * list (word 8))%type.

Definition Simple_Format_Spec
           (p : simple_record) :=
        encode_nat_Spec 8 (|snd p|)
  ThenC encode_word_Spec (fst p)
  ThenC encode_list_Spec encode_word_Spec (snd p)
  DoneC.

Definition Simply_OK (p : simple_record) :=
  ((|snd p|) < pow2 8)%nat.

Arguments split1' : simpl never.
Arguments split2' : simpl never.
Arguments weq : simpl never.
Arguments natToWord : simpl never.
Arguments Guarded_Vector_split : simpl never.
Arguments Core.append_word : simpl never.

Definition refine_simple_encode
  : { b : _ & forall (p : simple_record)
                     (p_OK : Simply_OK p),
          refine (Simple_Format_Spec p ())
                 (ret (b p)) }.
Proof.
  unfold Simple_Format_Spec.
  eexists; intros.
  eapply AlignedEncodeChar; eauto.
  eapply AlignedEncode2Char; eauto.
  etransitivity.
  apply refine_under_bind_both.
  eapply optimize_align_encode_list.
  etransitivity.
  eapply aligned_encode_char_eq.
  instantiate (1 := fun a ce => (existT _ _ _, _)); simpl.
  reflexivity.
  intros; unfold Bind2; simplify with monad laws; higher_order_reflexivity.
  simpl.
  match goal with
    |- context [let (v, c) := ?z in ret (@?b v c)] =>
    rewrite (zeta_inside_ret z _)
  end.
  simplify with monad laws; simpl.
  rewrite zeta_to_fst; simpl.
  replace ByteString_id
  with (build_aligned_ByteString (Vector.nil _)).
  erewrite <- build_aligned_ByteString_append.
  reflexivity.
  eapply ByteString_f_equal;
    instantiate (1 := eq_refl _); reflexivity.
Defined.

Definition byte_aligned_simple_encoder
             (r : simple_record)
  := Eval simpl in (projT1 refine_simple_encode r).

Import Vectors.VectorDef.VectorNotations.
Print byte_aligned_simple_encoder.

Definition Simple_Format_decoder
  : CorrectDecoderFor Simply_OK Simple_Format_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  repeat decode_step idtac.
  intros; eauto using FixedList_predicate_rest_True.
  synthesize_cache_invariant.
  cbv beta; optimize_decoder_impl.
Defined.

Definition SimpleDecoderImpl
    := Eval simpl in (projT1 Simple_Format_decoder).

  Ltac rewrite_DecodeOpt2_fmap :=
    set_refine_evar;
    progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
    ?DecodeOpt2_fmap_if_bool;
    subst_refine_evar.

Definition ByteAligned_SimpleDecoderImpl {A}
           (f : _ -> A)
           n
  : {impl : _ & forall (v : Vector.t _ (3 + n)),
         f (fst SimpleDecoderImpl (build_aligned_ByteString v) ()) =
         impl v () }.
Proof.
  eexists _; intros.
  etransitivity.
  set_refine_evar; simpl.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  rewrite (@AlignedDecodeNat NoCache.test_cache).
  subst_refine_evar; apply rewrite_under_LetIn; intros; set_refine_evar.
  unfold DecodeBindOpt2 at 1; rewrite_DecodeOpt2_fmap.
  rewrite (@AlignedDecode2Char NoCache.test_cache).
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
  apply (@decode_word_aligned_ByteString_overflow NoCache.test_cache) with (sz := 1); auto.
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
