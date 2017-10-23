Require Import
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.BinEncoders.Env.BinLib.CharString
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.WordFacts
        Fiat.BinEncoders.Env.Common.ComposeCheckSum
        Fiat.BinEncoders.Env.Common.ComposeIf
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.CInt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        compcert.lib.Integers.

Module IntEncoder := CInt.Make(Wordsize_32).

Import IntEncoder.

Instance ByteStringQueueTransformer : Transformer ByteString := ByteStringQueueTransformer.

Definition Simple_Format_Spec
           (p : int * list int) :=
        encode_nat_Spec 8 (|snd p|)
  ThenC encode_int_Spec Int.wordsize (fst p)
  ThenC encode_list_Spec (encode_int_Spec Int.wordsize) (snd p)
  DoneC.

Definition Simply_OK (p : int * list int) :=
  ((|snd p|) < pow2 8)%nat.

Definition Simple_Format_decoder
  : CorrectDecoderFor Simply_OK Simple_Format_Spec.
Proof.
  start_synthesizing_decoder.
  normalize_compose transformer.
  repeat first [apply innt_decode_correct; auto
               | solve [ intros; apply intrange]
               | intros; simpl; match goal with |- _ /\ _ => split; intuition eauto end
               | decode_step idtac].
  synthesize_cache_invariant.
  cbv beta; optimize_decoder_impl.
Defined.

Definition Simple_Format_decoder_impl :=
  Eval simpl in (fst (projT1 Simple_Format_decoder)).

Print Simple_Format_decoder_impl.


Lemma foo {C} {numBytes}
  : forall (v : Vector.t byte (S numBytes)) (k : int -> ByteString -> unit -> option (C * ByteString * unit)),
    (`(a, b0, d) <- decode_int
      (transformerUnit := ByteString_QueueTransformerOpt) 8 (build_aligned_ByteString v) tt;
       k a b0 d) =
    Let n := byteToInt32 (Vector.nth v Fin.F1) in
    k n (build_aligned_ByteString (Vector.tl v)) ().
Proof.
  unfold LetIn; intros.
  unfold decode_int, WordOpt.decode_word.
  rewrite aligned_decode_char_eq; simpl.
  f_equal.
  pattern numBytes, v; apply Vector.caseS; simpl; intros.
  destruct h.
  destruct intval0; simpl; intros; intuition eauto.
  - compute; apply mkint_eq; reflexivity.
  - repeat first [compute in intrange0; destruct intrange0; congruence
                 | destruct p as [p | p | ]; simpl
                 | compute; apply mkint_eq; reflexivity].
  - compute in intrange0; destruct p; destruct intrange0; congruence.
Qed.

Lemma foo2 {C} {numBytes}
  : forall (v : Vector.t byte (S numBytes)) (k : nat -> ByteString -> unit -> option (C * ByteString * unit)),
    (`(a, b0, d) <- decode_nat
      (transformerUnit := ByteString_QueueTransformerOpt) 8 (build_aligned_ByteString v) tt;
       k a b0 d) =
    Let n := BinInt.Z.to_nat (Byte.intval (Vector.nth v Fin.F1)) in
    k n (build_aligned_ByteString (Vector.tl v)) ().
Proof.
  intros.
  unfold decode_nat, WordOpt.decode_word.
  rewrite aligned_decode_char_eq; simpl.
  f_equal.
  pattern numBytes, v; apply Vector.caseS; simpl; intros.
  destruct h.
  destruct intval0; simpl; intros; intuition eauto.
  - repeat first [compute in intrange0; destruct intrange0; congruence
                 | destruct p as [p | p | ]; simpl
                 | compute; reflexivity].
Qed.

Lemma foo3 {C} {numBytes}
  : forall (v : Vector.t byte (S (S (S (S numBytes))))) (k : int -> ByteString -> unit -> option (C * ByteString * unit)),
    (`(a, b0, d) <- decode_int
      (transformerUnit := ByteString_QueueTransformerOpt) Int.wordsize (build_aligned_ByteString v) tt;
       k a b0 d) =
    Let n := wordToInt (Core.append_word (byteToWord (Vector.nth v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
                                         (Core.append_word (byteToWord (Vector.nth v (Fin.FS (Fin.FS Fin.F1))))
                                            (Core.append_word (byteToWord (Vector.nth v (Fin.FS Fin.F1)))
                                                              (byteToWord (Vector.nth v Fin.F1)))))
    in
    k n (build_aligned_ByteString (Vector.tl (Vector.tl (Vector.tl (Vector.tl v))))) ().
Proof.
  unfold LetIn; intros.
  unfold decode_int, WordOpt.decode_word.
  unfold Int.wordsize, Wordsize_32.wordsize.
  rewrite DecodeBindOpt2_assoc.
  pose proof (@aligned_decode_char_eq' _ 3 v).
  match goal with
    |- context[Ifopt ?Z as _ Then _ Else _] => replace Z with
                                               (let (v', v'') := Vector_split 4 numBytes v in Some (VectorByteToWord v', build_aligned_ByteString v'')) by (rewrite <- H; reflexivity)
  end.
  unfold Vector_split, If_Opt_Then_Else, DecodeBindOpt2 at 1, If_Opt_Then_Else.
  unfold DecodeBindOpt2 at 1, If_Opt_Then_Else.
  repeat f_equal.
  rewrite Core.append_word_assoc; erewrite VectorByteToWord_cons; repeat f_equal.
  rewrite Core.append_word_assoc, <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
  f_equal.
  erewrite VectorByteToWord_cons; f_equal.
  rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec; f_equal.
  erewrite VectorByteToWord_cons; f_equal.
  rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec; f_equal.
  erewrite VectorByteToWord_cons; f_equal.
  rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec; f_equal.
  simpl; f_equal; rewrite !Vector_nth_tl, Vector_nth_hd; reflexivity.
  simpl; f_equal; rewrite !Vector_nth_tl, Vector_nth_hd; reflexivity.
  simpl; f_equal; rewrite !Vector_nth_tl, Vector_nth_hd; reflexivity.
  simpl; f_equal; rewrite Vector_nth_hd; reflexivity.
  Grab Existential Variables.
  omega.
  omega.
  omega.
Qed.

Definition ofbytes (hi himid hilo lo: byte) : int :=
  or (shl (repr (Byte.unsigned hi)) (repr 24))
     (or (shl (repr (Byte.unsigned himid)) (repr 16))
         (or (shl (repr (Byte.unsigned hilo)) (repr 8))
             (repr (Byte.unsigned lo)))).

Lemma wordToInt_ofbytes_eq
  : forall (hi himid hilo lo: byte),
    wordToInt (Core.append_word
                 (byteToWord lo)
                 (Core.append_word (byteToWord hilo) (Core.append_word (byteToWord himid)
                                                                       (byteToWord hi)))) =
    ofbytes hi himid hilo lo.
Proof.
Admitted.

Lemma foo4 {C} {numBytes}
  : forall (v : Vector.t byte (S (S (S (S numBytes))))) (k : int -> ByteString -> unit -> option (C * ByteString * unit)),
    (`(a, b0, d) <- decode_int
      (transformerUnit := ByteString_QueueTransformerOpt) Int.wordsize (build_aligned_ByteString v) tt;
       k a b0 d) =
    Let n := ofbytes (Vector.nth v Fin.F1)
                     (Vector.nth v (Fin.FS Fin.F1))
                     (Vector.nth v (Fin.FS (Fin.FS Fin.F1)))
                     (Vector.nth v (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
    in
    k n (build_aligned_ByteString (Vector.tl (Vector.tl (Vector.tl (Vector.tl v))))) ().
Proof.
  intros; rewrite foo3.
  rewrite wordToInt_ofbytes_eq.
  reflexivity.
Qed.

Definition aligned_Simple_Format_decoder_impl (bs : Vector.t byte 32) :
  {n : option (int * list int * ByteString * ()) & n =
                                                        Simple_Format_decoder_impl (build_aligned_ByteString bs) ()}.
  eexists.
  symmetry; unfold Simple_Format_decoder_impl.
  erewrite (foo2 bs).
  apply f_equal; apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intro.
  rewrite foo4.
  etransitivity.
  apply f_equal; apply Coq.Logic.FunctionalExtensionality.functional_extensionality; intro.
Abort.
