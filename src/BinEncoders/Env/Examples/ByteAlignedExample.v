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

Lemma zeta_to_fst {A B C}
  : forall (ab : A * B) (k : A -> B -> C),
    (let (a, b) := ab in (k a b)) =
    k (fst ab) (snd ab).
Proof.
  destruct ab; reflexivity.
Qed.

Lemma zeta_inside_ret {A B C}
  : forall (ab : A * B) (k : A -> B -> C),
    refine (let (a, b) := ab in ret (k a b))
           (ret (let (a, b) := ab in k a b)).
Proof.
  destruct ab; reflexivity.
Qed.

Arguments split1' : simpl never.
Arguments split2' : simpl never.
Arguments weq : simpl never.
Arguments natToWord : simpl never.
Arguments Guarded_Vector_split : simpl never.

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
      rewrite (zeta_inside_ret z b)
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

Print byte_aligned_simple_encoder.

Ltac rewrite_DecodeOpt2_fmap :=
  set_refine_evar;
  progress rewrite ?BindOpt_map, ?DecodeOpt2_fmap_if,
    ?DecodeOpt2_fmap_if_bool;
  subst_refine_evar.

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

Lemma Ifopt_Ifopt {A A' B}
  : forall (a_opt : option A)
           (t : A -> option A')
           (e : option A')
           (t' : A' -> B)
           (e' :  B),
    Ifopt (Ifopt a_opt as a Then t a Else e) as a' Then t' a' Else e' =
                                                Ifopt a_opt as a Then (Ifopt (t a) as a' Then t' a' Else e') Else (Ifopt e as a' Then t' a' Else e').
Proof.
  destruct a_opt; simpl; reflexivity.
Qed.

Corollary AlignedDecodeNat {C}
            {numBytes}
    : forall (v : Vector.t (word 8) (S numBytes))
             (t : _ -> C)
             e
             cd,
    Ifopt (decode_nat (transformerUnit := ByteString_QueueTransformerOpt) 8 (build_aligned_ByteString v) cd) as w
    Then t w Else e
     =
      Let n := wordToNat (Vector.nth v Fin.F1) in
        t (n, build_aligned_ByteString (snd (Vector_split 1 _ v)), addD cd 8).
  Proof.
    unfold CacheDecode.
    unfold decode_nat, DecodeBindOpt2; intros.
    unfold BindOpt at 1.
    rewrite AlignedDecodeChar.
    reflexivity.
  Qed.

  Lemma optimize_Guarded_Decode {sz} {C} n
    : forall (a_opt : ByteString -> C)
             (a_opt' : ByteString -> C) v c,
      (~ (n <= sz)%nat
       -> a_opt (build_aligned_ByteString v) = c)
      -> (le n sz -> a_opt  (build_aligned_ByteString (Guarded_Vector_split n sz v))
                     = a_opt'
                         (build_aligned_ByteString (Guarded_Vector_split n sz v)))
      -> a_opt (build_aligned_ByteString v) =
         If NPeano.leb n sz Then
            a_opt' (build_aligned_ByteString (Guarded_Vector_split n sz v))
            Else c.
  Proof.
    intros; destruct (NPeano.leb n sz) eqn: ?.
    - apply NPeano.leb_le in Heqb.
      rewrite <- H0.
      simpl; rewrite <- build_aligned_ByteString_eq_split'; eauto.
      eauto.
    - rewrite H; simpl; eauto.
      intro.
      rewrite <- NPeano.leb_le in H1; congruence.
  Qed.

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
  pose CacheEncode.
  rewrite (@AlignedDecodeNat).
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
  subst_refine_evar; higher_order_reflexivity.
  clear H; intros.
  etransitivity.
  match goal with
    |- ?b = _ =>
    let b' := (eval pattern (build_aligned_ByteString v0) in b) in
    let b' := match b' with ?f _ => f end in
      eapply (@optimize_Guarded_Decode n0 _ 1 b')
  end.
  destruct n0 as [ | [ | ?] ]; intros; try omega.
  pose proof (@decode_word_aligned_ByteString_overflow _ _ 1) as H';
        simpl in H'; rewrite H'; try reflexivity; auto.
  destruct n0 as [ | ?]; intros; try omega.
  higher_order_reflexivity.
  instantiate (1 := fun n1 v1 cd0 =>
                      If NPeano.leb 1 n1 Then (Some ((Vector.hd (Guarded_Vector_split 1 n1 v1), existT _ _ (Vector.tl (Guarded_Vector_split 1 n1 v1))), cd0)) Else None).
  simpl; find_if_inside; simpl; try reflexivity.
  pattern n0, v0; apply Vector.caseS; simpl; intros.
  unfold decode_word, WordOpt.decode_word.
  rewrite aligned_decode_char_eq; reflexivity.
  higher_order_reflexivity.
Defined.

Definition ByteAligned_SimpleDecoderImpl' n :=
  Eval simpl in (projT1 (ByteAligned_SimpleDecoderImpl id n)).

Print ByteAligned_SimpleDecoderImpl'.
