Require Import
        Coq.Logic.Eqdep_dec
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Compose
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt.

Require Import
        Coq.Vectors.Vector
        Coq.omega.Omega
        Bedrock.Word.

Section AlignWord.
  Context {len : nat}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Variable addD_addD_plus :
    forall cd n m, addD (addD cd n) m = addD cd (n + m).

  Lemma If_Opt_Then_Else_DecodeBindOpt {A ResultT ResultT'}
    : forall (a_opt : option A)
             (t : A -> option (ResultT * B * CacheDecode))
             (e : option (ResultT * B * CacheDecode))
             (k : _ -> _ -> _ -> option (ResultT' * B * CacheDecode)),
      (`(w, b', cd') <- Ifopt a_opt as a Then t a Else e;
         k w b' cd') =
      (Ifopt a_opt as a Then
                        (`(w, b', cd') <- t a; k w b' cd')
                        Else (`(w, b', cd') <- e; k w b' cd')).
  Proof.
    destruct a_opt; simpl; intros; reflexivity.
  Qed.

  Fixpoint split1' (sz sz' : nat) : word (sz + sz') -> word sz :=
    match sz return word (sz + sz') -> word sz with
    | 0 => fun _ => WO
    | S n' => fun w => SW_word (word_split_hd w)
                               (split1' n' sz' (word_split_tl w))
    end.

  Fixpoint split2' (sz sz' : nat) : word (sz + sz') -> word sz' :=
    match sz return word (sz + sz') -> word sz' with
    | 0 => fun w => w
    | S n' => fun w => split2' n' sz' (word_split_tl w)
    end.

  Definition trans_S_comm : forall n m : nat, S (n + m) = n + S m.
  Proof.
    fix 1; destruct n.
    - intro; reflexivity.
    - simpl; intro; destruct (trans_S_comm n m); reflexivity.
  Defined.

  Lemma trans_plus_comm : forall n m, n + m = m + n.
  Proof.
    fix 1.
    destruct n.
    - fix 1.
      destruct m.
      + reflexivity.
      + simpl.
        destruct (trans_plus_comm0 m); reflexivity.
    - simpl; intro; rewrite (trans_plus_comm n m).
      apply trans_S_comm.
  Defined.

  Lemma wtl_eq_rect_S : forall sz sz' w eq_comm eq_comm',
      wtl (eq_rect (S sz) word w (S sz') eq_comm) =
      eq_rect sz word (wtl w) sz' eq_comm'.
  Proof.
    intros.
    destruct (shatter_word_S w) as (?, (w', H)); rewrite H in *; clear.
    revert w' eq_comm.
    rewrite eq_comm'; clear eq_comm'; intros.
    unfold eq_rect; simpl.
    revert w'.
    pattern eq_comm.
    apply K_dec_set; eauto; decide equality.
  Qed.

  Lemma wtl_eq_rect_comm : forall sz sz' w eq_comm eq_comm',
      wtl (eq_rect (S (sz + sz')) word w (S (sz' + sz)) eq_comm) =
      eq_rect (sz + sz') word (wtl w) (sz' + sz) eq_comm'.
  Proof.
    intros.
    eapply wtl_eq_rect_S.
  Qed.

  Lemma whd_eq_rect_comm : forall sz sz' w eq_comm,
      whd (eq_rect (S (sz + sz')) word w (S (sz' + sz)) eq_comm) =
      whd w.
  Proof.
    intros ? ?; rewrite trans_plus_comm; intros.
    destruct (shatter_word_S w) as (?, (w', H)); rewrite H in *; clear.
    unfold eq_rect; simpl.
    pattern eq_comm.
    apply K_dec_set; eauto; decide equality.
  Qed.

  Lemma eq_rect_WS : forall b sz sz' w e e',
      eq_rect (S sz) _ (WS b w) (S sz') e = WS b (eq_rect sz _ w sz' e').
  Proof.
    simpl; intros.
    revert e w.
    rewrite e'; intro; pattern e.
    apply K_dec_set; eauto; decide equality.
  Qed.

  Lemma eq_rect_split_tl
    : forall (sz sz' : nat) (x0 : bool) (w'' : word (sz' + sz)) (e : sz' + sz = sz + sz') (e1 : sz + sz' = sz' + sz),
      word_split_tl (WS x0 w'') =
      eq_rect (sz + sz') word (word_split_tl (WS x0 (eq_rect (sz' + sz) word w'' (sz + sz') e))) (sz' + sz) e1.
  Proof.
    induction sz; simpl.
    - intro; rewrite <- plus_n_O; intros.
      pattern e1.
      apply K_dec_set; eauto; try decide equality; clear e1.
      pattern e.
      apply K_dec_set; eauto; try decide equality; clear e.
    - intro; rewrite <- (trans_S_comm sz' sz); intros.
      intros; destruct (shatter_word_S w'') as (?, (w', H)); rewrite H in *; clear H.
      simpl.
      rewrite (IHsz sz' x w' (trans_plus_comm _ _) (trans_plus_comm _ _)); repeat f_equal.
      erewrite !eq_rect_WS; reflexivity.
  Qed.

  Lemma split1'_eq : forall sz sz' w,
      split1' sz sz' w = split2 sz' sz (eq_rect _ _ w _ (trans_plus_comm _ _)).
  Proof.
    induction sz; simpl; intros.
    - induction sz'; simpl.
      + shatter_word w; reflexivity.
      + destruct (shatter_word_S w) as (?, (w', H)); rewrite H in *; clear H.
        erewrite wtl_eq_rect_comm.
        eapply IHsz'.
    - intros; destruct (shatter_word_S w) as (?, (w', H)); rewrite H in *; clear H.
      simpl; rewrite IHsz; clear.
      generalize (eq_ind_r (fun n : nat => S n = sz' + S sz) (trans_S_comm sz' sz) (trans_plus_comm sz sz')).
      generalize (trans_plus_comm sz sz').
      fold (plus sz sz').
      revert x sz w'; induction sz'; simpl.
      + intros ? ?; rewrite <- (plus_n_O sz); simpl.
        intros.
        pattern e.
        apply K_dec_set; eauto; try decide equality.
        pattern e0.
        apply K_dec_set; eauto; try decide equality.
        unfold eq_rect; simpl.
        rewrite <- word_split_SW; reflexivity.
      + intros ? ?.
        rewrite <- !trans_S_comm.
        rewrite trans_plus_comm.
        intros; pattern e.
        apply K_dec_set; eauto; try decide equality; clear e.
        intros; destruct (shatter_word_S w') as (?, (w'', H)); rewrite H in *; clear H.
        rewrite (wtl_eq_rect_S _ _ _ e0 (trans_S_comm _ _)); simpl.
        assert (S (sz + sz') = sz' + S sz) by omega.
        replace (eq_rect (S (sz' + sz)) word (WS x0 w'') (sz' + S sz) (trans_S_comm sz' sz)) with
        (eq_rect (S (sz + sz')) word (WS x0 (eq_rect _ _ w'' _ (trans_plus_comm _ _))) (sz' + S sz) H).
        erewrite <- (IHsz' x0 sz _ (trans_plus_comm _ _)).
        repeat f_equal.
        { generalize (trans_plus_comm sz' sz); intros; clear.
          revert sz' x0 w'' e; induction sz; simpl.
          - intro; rewrite <- plus_n_O; intros.
            destruct e; reflexivity.
          - intro; rewrite <- (trans_S_comm sz' sz); intros.
            intros; destruct (shatter_word_S w'') as (?, (w', H)); rewrite H in *; clear H.
            simpl.
            rewrite (IHsz sz' x w' (trans_plus_comm _ _)); repeat f_equal.
            erewrite eq_rect_WS; eauto.
        }
        { eapply eq_rect_split_tl. }
        revert H; clear. revert w''; generalize (trans_S_comm sz' sz).
        rewrite (trans_plus_comm sz' sz); intros; simpl.
        destruct e; simpl.
        rewrite eq_rect_WS with (e' := eq_refl _); reflexivity.
  Qed.

  Lemma split2'_eq : forall sz sz' w,
      split2' sz sz' w = split1 sz' sz (eq_rect _ _ w _ (trans_plus_comm _ _)).
  Proof.
    induction sz; simpl; intros.
    - induction sz'; simpl.
      + shatter_word w; reflexivity.
      + destruct (shatter_word_S w) as (?, (w', H)); rewrite H in *; clear H.
        rewrite whd_eq_rect_comm; simpl.
        erewrite wtl_eq_rect_comm.
        rewrite (IHsz' w') at 1; reflexivity.
    - intros; destruct (shatter_word_S w) as (?, (w', H)); rewrite H in *; clear H.
      simpl; rewrite IHsz; clear.
      generalize (eq_ind_r (fun n : nat => S n = sz' + S sz) (trans_S_comm sz' sz) (trans_plus_comm sz sz')).
      generalize (trans_plus_comm sz sz').
      fold (plus sz sz').
      revert x sz w'; induction sz'; simpl; eauto.
      intros.
      assert (sz + S sz' = sz' + S sz) by omega.
      rewrite eq_rect_WS with (e' := H); simpl.
      revert w' e0 H; rewrite e; intros.
      destruct (shatter_word_S w') as (?, (w'', H')); rewrite H' in *; clear H'; simpl.
      f_equal.
      assert (S (sz + sz') = sz' + S sz) by omega.
      replace (eq_rect (S (sz' + sz)) word (WS x0 w'') (sz' + S sz) H)
      with (eq_rect (S (sz + sz')) word (WS x0 (eq_rect _ _ w'' _ (trans_plus_comm _ _))) (sz' + S sz) H0)
        by (revert w'' H H0; clear;
            rewrite (trans_plus_comm sz' sz); intros; simpl;
            destruct H; simpl;
            erewrite eq_rect_WS with (e' := eq_refl _); reflexivity).
      rewrite <- IHsz' with (e := trans_plus_comm _ _);
        f_equal; simpl.
      eapply eq_rect_split_tl.
  Qed.

    Lemma CollapseWord {ResultT}
    : forall sz sz' (b : B)
             (cd : CacheDecode)
             (k : _ -> _ -> _ -> _ -> option (ResultT * B * CacheDecode)),
      (`(w, b', cd') <- decode_word (sz:=sz) b cd;
         `(w', b', cd') <- decode_word (sz:=sz') b' cd';
         k w w' b' cd') =
      (`(w , b', cd') <- decode_word (sz:=sz + sz') b cd;
         k (split1' sz sz' w)
           (split2' sz sz' w) b' cd').
  Proof.
    unfold decode_word; repeat setoid_rewrite If_Opt_Then_Else_DecodeBindOpt; simpl.
    induction sz; simpl; intros.
    - rewrite !If_Opt_Then_Else_DecodeBindOpt; simpl.
      rewrite addD_addD_plus; reflexivity.
    - destruct (dequeue_opt b) as [ [? ?] | ]; simpl; eauto.
      pose proof (IHsz sz' b1 (addD cd 1) (fun w => k (SW_word b0 w))).
      destruct (decode_word' sz b1) as [ [? ?] | ]; simpl in *.
      + rewrite !If_Opt_Then_Else_DecodeBindOpt;
          rewrite !If_Opt_Then_Else_DecodeBindOpt in H; simpl in *;
            rewrite !addD_addD_plus in H;
            rewrite !addD_addD_plus; simpl in *.
        rewrite H.
        destruct (decode_word' (sz + sz') b1) as [ [? ?] | ]; simpl; eauto.
        repeat f_equal; clear.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w0; simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w0; simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w0; simpl; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w0); destruct_ex; subst;
            simpl; f_equal; eauto.
      + destruct (decode_word' (sz + sz') b1) as [ [? ?] | ]; simpl in *; eauto.
        rewrite addD_addD_plus in H; simpl in *.
        rewrite H; repeat f_equal; clear.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w; simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w; simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
        * induction sz; simpl in *.
          induction sz'; simpl in *; try shatter_word w; simpl; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
          pose proof (shatter_word_S w); destruct_ex; subst;
            simpl; f_equal; eauto.
  Qed.

  Lemma CollapseWord' {ResultT}
    : forall sz' sz (b : B)
             (cd : CacheDecode)
             (k : _ -> _ -> _ -> _ -> option (ResultT * B * CacheDecode)),
      (`(w, b', cd') <- decode_word (sz:=sz) b cd;
         `(w', b', cd') <- decode_word (sz:=sz') b' cd';
         k w w' b' cd') =
      (`(w , b', cd') <- decode_word (sz:=sz + sz') b cd;
         k (split2 sz' sz (eq_rect _ _ w _ (trans_plus_comm sz sz')))
           (split1 sz' sz (eq_rect _ _ w _ (trans_plus_comm sz sz'))) b' cd').
  Proof.
    intros; rewrite CollapseWord.
    destruct (decode_word b cd) as [ [ [? ?] ?] | ]; simpl.
    rewrite split2'_eq, split1'_eq; eauto.
    reflexivity.
  Qed.

  Lemma CollapseWord'' {ResultT}
    : forall sz' sz (b : B)
             (cd : CacheDecode)
             (k : _ -> _ -> _ -> _ -> option (ResultT * B * CacheDecode)),
      (`(w, b', cd') <- decode_word (sz:=sz) b cd;
         `(w', b', cd') <- decode_word (sz:=sz') b' cd';
         k w w' b' cd') =
      (`(w , b', cd') <- decode_word (sz:=sz' + sz) b cd;
         k (split2 sz' sz w)
           (split1 sz' sz w) b' cd').
  Proof.
    intros; rewrite CollapseWord'.
    replace (decode_word (sz:=sz' + sz) b cd) with (eq_rect _ (fun n => option (word n * B * _)) (decode_word (sz:=sz + sz') b cd) _ (trans_plus_comm _ _)).
    - destruct (decode_word b cd) as [ [ [? ?] ?] | ]; simpl.
      + revert w; rewrite (trans_plus_comm sz sz'); simpl; eauto.
      + rewrite (trans_plus_comm sz sz'); simpl; eauto.
    - rewrite (trans_plus_comm sz sz'); simpl; reflexivity.
  Qed.

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).

  Lemma format_word_S {n}
    : forall (w : word (S n)) (bs : B),
      encode_word' (S n) w bs =
      encode_word' n (word_split_tl w) (enqueue_opt (word_split_hd w) bs).
  Proof.
    intros; pose proof (shatter_word_S w); destruct_ex; subst.
    simpl.
    clear; revert x; induction x0; simpl; intros.
    - simpl; reflexivity.
    - rewrite IHx0.
      reflexivity.
  Qed.

  Lemma word_split_hd_SW_word {n}
    : forall b (w : word n),
      word_split_hd (SW_word b w) = b.
  Proof.
    induction w; simpl; intros; eauto.
  Qed.

  Lemma word_split_tl_SW_word {n}
    : forall b (w : word n),
      word_split_tl (SW_word b w) = w.
  Proof.
    induction w; simpl; intros; eauto.
    f_equal; eauto.
  Qed.

  Lemma CollapseFormatWord
    : forall {sz sz'} (w : word sz) (w' : word sz') k ce,
      refine (((format_word w)
                ThenC (format_word w')
                ThenC k) ce)
             (((format_word (combine w' w))
                 ThenC k) ce).
  Proof.
    intros; unfold compose, format_word, Bind2.
    autorewrite with monad laws.
    simpl; rewrite addE_addE_plus.
    rewrite Plus.plus_comm; f_equiv; intro.
    rewrite mappend_assoc.
    destruct a; simpl.
    f_equiv; f_equiv; f_equiv.
    revert sz' w'; induction w; simpl; intros.
    - rewrite mempty_left.
      generalize mempty; clear; induction w'; intros.
      + reflexivity.
      + simpl; rewrite IHw'; reflexivity.
    - rewrite !enqueue_opt_format_word.
      replace (encode_word' (sz' + S n) (combine w' (WS b0 w)) mempty)
      with (encode_word' (S sz' + n) (combine (SW_word b0 w') w) mempty).
      + rewrite <- IHw.
        simpl; rewrite format_word_S.
        rewrite <- mappend_assoc, word_split_tl_SW_word, word_split_hd_SW_word.
        f_equal.
        clear; induction w'.
        * simpl; rewrite mempty_right; reflexivity.
        * simpl; rewrite !enqueue_opt_format_word.
          rewrite <- IHw'.
          rewrite mappend_assoc; reflexivity.
      + clear; revert n w; induction w'; intros.
        * simpl; eauto.
        * simpl; rewrite <- IHw'; reflexivity.
  Qed.

  Lemma format_SW_word {n}
    : forall b (w : word n) ce,
          refine (format_word (SW_word b w) ce)
                 (`(bs, ce') <- format_word w (addE ce 1);
                    ret (mappend (enqueue_opt b mempty) bs, ce')).
  Proof.
    induction n; simpl; intros.
    - shatter_word w; simpl.
      unfold format_word; simpl.
      autorewrite with monad laws.
      simpl; rewrite addE_addE_plus; rewrite mempty_right; reflexivity.
    - pose proof (shatter_word_S w); destruct_ex; subst.
      simpl.
      unfold format_word; simpl.
      autorewrite with monad laws; simpl.
      assert (computes_to (`(bs, ce') <- ret (encode_word' n x0 mempty, addE (addE ce 1) n);
                           ret (mappend (enqueue_opt b mempty) bs, ce'))
                          (mappend (enqueue_opt b mempty) (encode_word' n x0 mempty), addE (addE ce 1) n)) by repeat computes_to_econstructor.
      pose proof (IHn b x0 ce _ H).
      unfold format_word in H0.
      computes_to_inv; inversion H0; subst.
      rewrite H2.
      rewrite enqueue_mappend_opt.
      rewrite addE_addE_plus.
      reflexivity.
  Qed.

  Lemma If_Opt_Then_Else_DecodeBindOpt_swap {A C ResultT : Type}
    : forall (a_opt : option A)
             (b : B)
             (cd : CacheDecode)
             (dec_c : B -> CacheDecode -> option (C * B * CacheDecode))
             (k : A -> C -> B -> CacheDecode -> option (ResultT * B * CacheDecode)),
      (`(a, b', cd') <- Ifopt a_opt as a Then Some (a, b, cd) Else None;
         `(c, b', cd') <- dec_c b' cd';
         k a c b' cd') =
      (`(c, b', cd') <- dec_c b cd;
         `(a, b', cd') <- Ifopt a_opt as a Then Some (a, b', cd') Else None;
         k a c b' cd').
  Proof.
    destruct a_opt; simpl; intros; eauto.
    destruct (dec_c b cd) as [ [ [? ?] ? ] | ]; reflexivity.
  Qed.

  Lemma If_Then_Else_Bind {sz} {C ResultT : Type}
    : forall (w w' : word sz)
             (b : B)
             (cd : CacheDecode)
             (dec_c : B -> CacheDecode -> option (C * B * CacheDecode))
             (k : C -> B -> CacheDecode -> option (ResultT * B * CacheDecode)),
      (if weq w w' then
         `(c, b', cd') <- dec_c b cd;
           k c b' cd'
       else
         None) =
      (`(c, b', cd') <- dec_c b cd;
         if weq w w' then
           k c b' cd'
         else None).
  Proof.
    intros; find_if_inside; eauto.
    destruct (dec_c b cd) as [ [ [? ?] ? ] | ]; reflexivity.
  Qed.

End AlignWord.

Require Import Fiat.Narcissus.BinLib.AlignedByteString.

Section AlignDecodeWord.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Lemma aligned_format_char_eq
    : forall (w : word 8) cd,
      refine (format_word (monoidUnit := ByteString_QueueMonoidOpt) w cd)
             (ret (build_aligned_ByteString (Vector.cons _ w _ (Vector.nil _)), addE cd 8)).
  Proof.
    intros; shatter_word w; simpl.
    unfold format_word; simpl.
    compute.
    intros.
    computes_to_inv; subst.
    match goal with
      |- computes_to (ret ?c) ?v => replace c with v
    end.
    computes_to_econstructor.
    f_equal.
    eapply ByteString_f_equal; simpl.
    instantiate (1 := eq_refl _).
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    erewrite eq_rect_Vector_cons; repeat f_equal.
    instantiate (1 := eq_refl _); reflexivity.
    Grab Existential Variables.
    reflexivity.
  Qed.

  Lemma AlignedDecodeChar {C}
        {numBytes}
    : forall (v : Vector.t (word 8) (S numBytes))
             (t : (word 8 * ByteString * CacheDecode) -> C)
             (e : C)
             cd,
      Ifopt (decode_word
               (monoidUnit := ByteString_QueueMonoidOpt) (sz := 8) (build_aligned_ByteString v) cd)
      as w Then t w Else e
         =
         LetIn (Vector.nth v Fin.F1)
               (fun w => t (w, build_aligned_ByteString (snd (Vector_split 1 _ v)), addD cd 8)).
  Proof.
    unfold LetIn; intros.
    unfold decode_word, WordOpt.decode_word.
    rewrite aligned_decode_char_eq; simpl.
    f_equal.
    pattern numBytes, v; apply Vector.caseS; simpl; intros.
    reflexivity.
  Qed.

  Lemma AlignedFormatChar {numBytes}
    : forall (w : word 8) ce ce' (c : _ -> Comp _) (v : Vector.t _ numBytes),
      refine (c (addE ce 8)) (ret (build_aligned_ByteString v, ce'))
      -> refine (((format_word (monoidUnit := ByteString_QueueMonoidOpt) w)
                    ThenC c) ce)
                (ret (build_aligned_ByteString (Vector.cons _ w _ v), ce')).
  Proof.
    unfold compose; intros.
    unfold Bind2.
    setoid_rewrite aligned_format_char_eq; simplify with monad laws.
    simpl; rewrite H; simplify with monad laws.

    simpl.
    rewrite <- build_aligned_ByteString_append.
    reflexivity.
  Qed.

  Lemma AlignedDecode2Char {C}
        {numBytes}
    : forall (v : Vector.t (word 8) (S (S numBytes)))
             (t : (word 16 * ByteString * CacheDecode) -> C)
             (e : C)
             cd,
      (Ifopt (decode_word
                (monoidUnit := ByteString_QueueMonoidOpt) (sz := 16) (build_aligned_ByteString v) cd) as w
                                                                                                           Then t w
                                                                                                           Else e)
      = Let n := Core.append_word (Vector.nth v (Fin.FS Fin.F1)) (Vector.nth v Fin.F1) in
        t (n, build_aligned_ByteString (snd (Vector_split 2 _ v)), addD cd 16).
  Proof.
    unfold LetIn; intros.
    unfold decode_word, WordOpt.decode_word.
    match goal with
      |- context[Ifopt ?Z as _ Then _ Else _] => replace Z with
                                                 (let (v', v'') := Vector_split 2 numBytes v in Some (VectorByteToWord v', build_aligned_ByteString v'')) by (symmetry; apply (@aligned_decode_char_eq' _ 1 v))
    end.
    unfold Vector_split, If_Opt_Then_Else, If_Opt_Then_Else.
    f_equal.
    rewrite !Vector_nth_tl, !Vector_nth_hd.
    erewrite VectorByteToWord_cons.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    f_equal.
    erewrite VectorByteToWord_cons.
    rewrite <- !Eqdep_dec.eq_rect_eq_dec; eauto using Peano_dec.eq_nat_dec.
    Grab Existential Variables.
    omega.
    omega.
  Qed.

End AlignDecodeWord.

Ltac collapse_word addD_addD_plus :=
  match goal with
  | |- DecodeBindOpt2
         (decode_word (sz := ?sz) ?b ?cd)
         (fun w b' cd' =>
            DecodeBindOpt2 (decode_word (sz := ?sz') b' cd')
                           (fun w' b'' cd'' => @?k w w' b'' cd'')) = _ =>
    etransitivity;
    [let H := fresh in
     pose proof (@CollapseWord'' _ _ _ _ _ addD_addD_plus _ sz' sz b cd k);
     apply H | ]
  end.
