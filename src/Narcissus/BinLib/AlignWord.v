Require Import
        Coq.Logic.Eqdep_dec
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.Sequence
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.BinLib.AlignedEncodeMonad.

Require Import
        Coq.Vectors.Vector
        Coq.omega.Omega
        Bedrock.Word.

Section AlignWord.
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
    fix trans_S_comm 1. destruct n.
    - intro; reflexivity.
    - simpl; intro; destruct (trans_S_comm n m); reflexivity.
  Defined.

  Lemma trans_plus_comm : forall n m, n + m = m + n.
  Proof.
    fix rec_n 1.
    destruct n.
    - fix rec_m 1.
      destruct m.
      + reflexivity.
      + simpl.
        destruct (rec_m m); reflexivity.
    - simpl; intro; rewrite (rec_n n m).
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

  Lemma CollapseEnumWord {ResultT}
    : forall sz' sz n (b : B) (tb : Vector.t (word sz) (S n))
             (cd : CacheDecode)
             (k : _ -> _ -> _ -> _ -> option (ResultT * B * CacheDecode)),
      (`(w, b', cd') <- decode_enum (sz:=sz) tb b cd;
         `(w', b', cd') <- decode_word (sz:=sz') b' cd';
         k w w' b' cd') =
      (`(w , b', cd') <- decode_word (sz:=sz' + sz) b cd;
         Ifopt (word_indexed (split2 sz' sz w) tb) as idx Then
                                                          k idx
                                                          (split1 sz' sz w) b' cd'
                                                          Else None).
  Proof.
    intros.
    unfold decode_enum.
    rewrite <- CollapseWord'' with
        (b0 := b)
        (cd0 := cd)
        (k0 := fun w1 w2 b cd =>
                Ifopt (word_indexed w1 tb) as idx Then k idx w2 b cd Else None).
    unfold decode_word; repeat setoid_rewrite If_Opt_Then_Else_DecodeBindOpt; simpl.
    destruct (decode_word' sz b) as [ [? ?] | ] eqn: ?; simpl; eauto.
    destruct (word_indexed w tb) as [ ? | ] eqn: ?; simpl; eauto.
    destruct (decode_word' sz' b0) as [ [? ?] | ] eqn: ?; simpl; eauto.
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

  Lemma CollapseFormatWord'
    : forall {sz sz'} (w : word sz) (w' : word sz') k ce,
      refine (((format_word (combine w' w))
                 ThenC k) ce)
             (((format_word w)
                 ThenC (format_word w')
                 ThenC k) ce).
  Proof.
    intros; unfold compose, format_word, Bind2.
    autorewrite with monad laws.
    simpl; rewrite addE_addE_plus.
    f_equiv.
    clear; rewrite Plus.plus_comm; reflexivity.
    intro; rewrite mappend_assoc.
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
      + rewrite IHw.
        simpl; rewrite format_word_S.
        rewrite <- mappend_assoc, word_split_tl_SW_word, word_split_hd_SW_word.
        f_equal.
        clear; induction w'.
        * simpl; rewrite mempty_right; reflexivity.
        * simpl; rewrite !enqueue_opt_format_word.
          rewrite IHw'.
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

Require Import Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedDecodeMonad.

Section AlignEncodeWord.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Variable addD_addD_plus :
    forall cd n m, addD (addD cd n) m = addD cd (n + m).

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
    unfold ByteBuffer.t; erewrite eq_rect_Vector_cons; repeat f_equal.
    instantiate (1 := eq_refl _); reflexivity.
    Grab Existential Variables.
    reflexivity.
  Qed.

  Local Open Scope AlignedDecodeM_scope.

  Lemma AlignedDecodeChar {C}
        {numBytes}
    : forall (v : ByteBuffer.t (S numBytes))
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

  Lemma AlignedDecodeCharM
    : DecodeMEquivAlignedDecodeM
        (decode_word (monoidUnit := ByteString_QueueMonoidOpt) (sz := 8))
        (fun numBytes => GetCurrentByte).
  Proof.
    unfold DecodeMEquivAlignedDecodeM, BindAlignedDecodeM, DecodeBindOpt2, BindOpt; intros;
      unfold decode_word, WordOpt.decode_word.
    split; [ | split ]; intros.
    - pattern numBytes_hd, v; eapply Vector.caseS; simpl; intros.
      unfold GetCurrentByte, nth_opt; simpl.
      destruct (Vector_nth_opt t n); simpl; eauto.
    - destruct (decode_word' 8 b) as [ [? ?] | ] eqn: ?; simpl in H; try discriminate.
      eapply decode_word'_lt in Heqo; unfold le_B, bin_measure in Heqo; simpl in Heqo.
      unfold lt_B in Heqo; simpl in Heqo.
      injections; omega.
    - destruct v.
      + simpl; intuition; discriminate.
      + rewrite aligned_decode_char_eq; simpl; intuition.
        * discriminate.
        * unfold GetCurrentByte in H; simpl in H; discriminate.
        * unfold GetCurrentByte; injections; simpl.
          clear; induction n; simpl; eauto.
        * injections.
          replace (match numBytes (build_aligned_ByteString v) with
                   | 0 => S n
                   | S l => n - l
                   end) with 1 by
              (unfold numBytes; simpl;
               clear; induction n; omega).
          setoid_rewrite <- build_aligned_ByteString_append.
          eexists (Vector.cons _ c _ (@Vector.nil _)); reflexivity.
  Qed.

  Lemma SW_word_append :
    forall b sz (w : word sz) sz' (w' : word sz'),
      SW_word b (Core.append_word w w')
      = eq_rect _ word (Core.append_word w (SW_word b w')) _ (sym_eq (plus_n_Sm _ _)).
  Proof.
    induction w; simpl; intros.
    - apply Eqdep_dec.eq_rect_eq_dec; auto with arith.
    - erewrite <- !WS_eq_rect_eq.
      rewrite IHw; reflexivity.
  Qed.

  Lemma decode_word_plus':
    forall (n m : nat) (v : ByteString),
      decode_word' (n + m) v =
      (`(w, v') <- decode_word' n v;
         `(w', v'') <- decode_word' m v';
         Some (eq_rect _ _ (Core.append_word w' w) _ (plus_comm_transparent _ _), v'')).
  Proof.
    induction n.
    - simpl; intros.
      destruct (decode_word' m v) as [ [? ?] | ]; simpl; repeat f_equal.
      revert w; clear.
      induction w; simpl; eauto.
      rewrite IHw at 1.
      rewrite Core.succ_eq_rect; f_equal.
      apply Eqdep_dec.UIP_dec; auto with arith.
    - simpl; intros.
      simpl; rewrite !DecodeBindOpt_assoc;
        destruct (ByteString_dequeue v) as [ [? ?] | ]; try reflexivity.
      simpl; rewrite !DecodeBindOpt_assoc.
      rewrite IHn.
      simpl; rewrite !DecodeBindOpt_assoc.
      destruct (decode_word' n b0)  as [ [? ?] | ]; try reflexivity.
      simpl; rewrite !DecodeBindOpt_assoc.
      destruct (decode_word' m b1)  as [ [? ?] | ]; try reflexivity.
      simpl; f_equal; f_equal; clear.
      revert b n w; induction w0; simpl; intros.
      + apply SW_word_eq_rect_eq.
      + erewrite !SW_word_eq_rect_eq; simpl.
        erewrite <- !WS_eq_rect_eq.
        f_equal.
        rewrite SW_word_append.
        rewrite <- Equality.transport_pp.
        f_equal.
        Grab Existential Variables.
        omega.
        omega.
  Qed.

  Lemma AlignedDecodeBindCharM {C : Type}
        (t : word 8 -> DecodeM (C * ByteString) ByteString)
        (t' : word 8 -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_word (monoidUnit := ByteString_QueueMonoidOpt) (sz := 8) v cd;
                          t a b0 cd')
           (fun numBytes => b <- GetCurrentByte; t' b).
  Proof.
    intro; eapply Bind_DecodeMEquivAlignedDecodeM.
    apply AlignedDecodeCharM.
    intros; eapply H.
  Qed.


  Lemma AlignedDecodeNCharM
        (addD_O : forall cd, addD cd 0 = cd)
        {m}
    : DecodeMEquivAlignedDecodeM
        (decode_word (sz := m * 8))
        (fun numBytes => GetCurrentBytes m).
  Proof.
    induction m.
    - unfold decode_word; simpl;
        pose proof (Return_DecodeMEquivAlignedDecodeM WO).
      eapply DecodeMEquivAlignedDecodeM_trans; intros; try rewrite addD_O; try higher_order_reflexivity.
      eapply H.
    - Local Arguments decode_word' : simpl never.
      Local Arguments plus : simpl never.
      unfold decode_word; simpl.
      eapply DecodeMEquivAlignedDecodeM_trans;
        intros; try eapply AlignedDecodeMEquiv_refl.
      + eapply AlignedDecodeBindCharM; intros.
        eapply Bind_DecodeMEquivAlignedDecodeM.
        eassumption.
        intros.
        pose proof (@Return_DecodeMEquivAlignedDecodeM); eapply H.
      + intros; unfold mult; simpl; rewrite decode_word_plus'; simpl; fold mult;
        simpl.
        unfold decode_word.
        destruct (decode_word' 8 b) as [ [? ?] | ]; simpl; eauto.
        destruct (decode_word' (m * 8) b0) as [ [? ?] | ]; simpl; eauto.
        rewrite addD_addD_plus; eauto.
  Qed.

  Lemma AlignedDecodeBindCharM' {A C : Type}
        (t : word 8 -> DecodeM (C * ByteString) ByteString)
        (t' : word 8 -> forall {numBytes}, AlignedDecodeM C numBytes)
        decode_w
    : (forall v cd,
          decode_word (monoidUnit := ByteString_QueueMonoidOpt) (sz := 8) v cd
          = decode_w v cd)
      -> (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_w v cd;
                          t a b0 cd')
           (fun numBytes => b <- GetCurrentByte; t' b)%AlignedDecodeM.
  Proof.
    intros; eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply DecodeMEquivAlignedDecodeM_trans; eauto.
    apply AlignedDecodeCharM.
    simpl. intros; eapply AlignedDecodeMEquiv_refl.
  Qed.

  Lemma decode_unused_word_plus':
    forall (n m : nat) (v : ByteString),
      decode_unused_word' (n + m) v =
      (`(w, v') <- decode_unused_word' n v;
         `(w', v'') <- decode_unused_word' m v';
         Some ((), v'')).
  Proof.
    induction n.
    - unfold plus; simpl; intros.
      destruct (decode_unused_word' m v) as [ [? ?] | ]; simpl; repeat f_equal.
      destruct u; eauto.
    - simpl; intros.
      unfold decode_unused_word' in *; simpl.
      fold plus.
      destruct (ByteString_dequeue v) as [ [? ?] | ]; try reflexivity.
      simpl.
      pose proof (IHn m b0).
      destruct (WordOpt.monoid_dequeue_word (n + m) b0) as [ [? ?] | ];
        simpl in *; try congruence.
      simpl in *.
      destruct (WordOpt.monoid_dequeue_word n b0) as [ [? ?] | ];
        simpl in *; try congruence.
      destruct (WordOpt.monoid_dequeue_word n b0) as [ [? ?] | ];
        simpl in *; try congruence.
  Qed.

  Lemma aligned_decode_unused_char_eq
        {numBytes}
    : forall (v : Vector.t _ (S numBytes)),
      WordOpt.decode_unused_word' (monoidUnit := ByteString_QueueMonoidOpt) 8 (build_aligned_ByteString v)
      = Some ((), build_aligned_ByteString (Vector.tl v)).
  Proof.
    unfold decode_unused_word'; simpl; intros.
    etransitivity.
    apply f_equal with (f := fun z => If_Opt_Then_Else z _ _ ).
    eapply DecodeBindOpt_under_bind; intros; set_evars; rewrite !DecodeBindOpt_assoc.
    repeat (unfold H; apply DecodeBindOpt_under_bind; intros; set_evars; rewrite !DecodeBindOpt_assoc).
    unfold H5; higher_order_reflexivity.
    simpl.
    pattern numBytes, v; eapply Vector.caseS; intros; simpl; clear v numBytes.
    replace (build_aligned_ByteString t) with (ByteString_enqueue_ByteString ByteString_id (build_aligned_ByteString t)).
    unfold Core.char in h.
    shatter_word h.
    pose proof (@dequeue_mappend_opt _ _ _ ByteString_QueueMonoidOpt).
    rewrite build_aligned_ByteString_cons; simpl.
    simpl in H7.
    erewrite H7 with (t := x6)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 (WS x5 WO))))));
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x5)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 (WS x4 WO)))));
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x4)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 (WS x3 WO))));
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x3)
                     (b' := {| front := WS x (WS x0 (WS x1 (WS x2 WO)));
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x2)
                     (b' := {| front := WS x (WS x0 (WS x1 WO));
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x1)
                     (b' := {| front := WS x (WS x0 WO);
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x0)
                     (b' := {| front := WS x WO;
                               byteString := Vector.nil _ |}); simpl.
    erewrite H7 with (t := x)
                     (b' := {| front := WO;
                               byteString := Vector.nil _ |}); simpl.
    reflexivity.
    unfold dequeue_opt.
    simpl.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    compute; repeat f_equal; apply Core.le_uniqueness_proof.
    unfold build_aligned_ByteString.
    unfold ByteString_dequeue; simpl.
    repeat f_equal; apply Core.le_uniqueness_proof.
    apply (@mempty_left _ ByteStringQueueMonoid).
  Qed.

  Lemma aligned_decode_unused_char_eq'
        {numBytes}
    : forall (v : Vector.t _ (S numBytes)) env,
      WordOpt.decode_unused_word (sz := 8) (monoidUnit := ByteString_QueueMonoidOpt) (build_aligned_ByteString v) env
      = Some ((), build_aligned_ByteString (Vector.tl v), addD env 8).
  Proof.
    unfold decode_unused_word; simpl; intros.
    etransitivity.
    unfold Compose_Decode, DecodeBindOpt.
    unfold BindOpt.
    eapply AlignedDecodeChar.
    pattern numBytes, v.
    eapply Vector.caseS; simpl; intros.
    reflexivity.
  Qed.

  Lemma AlignedDecodeUnusedCharM
    : DecodeMEquivAlignedDecodeM
        (decode_unused_word (sz := 8))
        (fun numBytes => SkipCurrentByte).
  Proof.
    unfold DecodeMEquivAlignedDecodeM, BindAlignedDecodeM, DecodeBindOpt2, BindOpt, Compose_Decode; intros;
      unfold WordOpt.decode_word, Compose_Decode.
    split; [ | split ]; intros.
    - pattern numBytes_hd, v; eapply Vector.caseS; simpl; intros.
      unfold SkipCurrentByte, nth_opt; simpl.
      destruct (Vector_nth_opt t n); simpl; eauto.
    - unfold decode_unused_word, Compose_Decode, decode_word in H.
      destruct (decode_word' 8 b) as [ [? ?] | ] eqn: ?; simpl in H; try discriminate.
      injections.
      eapply decode_word'_lt in Heqo; unfold le_B, bin_measure in Heqo; simpl in Heqo.
      unfold lt_B in Heqo; simpl in Heqo.
      injections; omega.
    - destruct v.
      + simpl; intuition; discriminate.
      + rewrite aligned_decode_unused_char_eq'; simpl; intuition.
        * discriminate.
        * unfold GetCurrentByte in H; simpl in H; discriminate.
        * unfold SkipCurrentByte; injections; simpl.
          clear; induction n; simpl; eauto.
        * injections.
          replace (match numBytes (build_aligned_ByteString v) with
                   | 0 => S n
                   | S l => n - l
                   end) with 1 by
              (unfold numBytes; simpl;
               clear; induction n; omega).
          setoid_rewrite <- build_aligned_ByteString_append.
          eexists (Vector.cons _ h _ (@Vector.nil _)); reflexivity.
  Qed.

  Lemma AlignedDecodeNUnusedCharM
        (addD_O : forall cd, addD cd 0 = cd)
        {m}
    : DecodeMEquivAlignedDecodeM
        (decode_unused_word (sz := m * 8))
        (fun numBytes => SkipCurrentBytes m).
  Proof.
    induction m.
    - unfold decode_unused_word; simpl;
        pose proof (@Return_DecodeMEquivAlignedDecodeM).
      eapply DecodeMEquivAlignedDecodeM_trans; intros; try rewrite addD_O.
      eapply H.
      unfold Compose_Decode, DecodeBindOpt, BindOpt.
      simpl; rewrite addD_O; reflexivity.
      simpl; reflexivity.
    - Local Arguments decode_word' : simpl never.
      Local Arguments plus : simpl never.
      unfold decode_unused_word; simpl.
      eapply DecodeMEquivAlignedDecodeM_trans;
        intros; try eapply AlignedDecodeMEquiv_refl.
      (*intros; unfold mult; simpl; rewrite decode_unused_word_plus'; simpl; fold mult. *)
      Focus 2.
      (*2: {*)
      {
      instantiate (1 := fun b cd => `(w, v', cd') <- decode_unused_word (sz := 8) b cd;
                                    `(w', v'', cd') <- decode_unused_word (sz := m * 8) v' cd';
                                    Some ((), v'', cd')); simpl.
      unfold decode_unused_word, Compose_Decode, DecodeBindOpt, BindOpt.
      unfold decode_word, decode_word'; simpl in *.
      destruct (ByteString_dequeue b) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b1) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b3) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b5) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b7) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b9) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      rewrite !DecodeBindOpt_assoc.
      destruct (ByteString_dequeue b11) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b13) as [ [? ?] | ]; simpl in *; try discriminate; eauto.
      destruct (ByteString_dequeue b15) as [ [? ?] | ]; simpl in *; try discriminate; eauto;
      intros; rewrite !DecodeBindOpt_assoc.
      simpl;  match goal with
                |- context [DecodeBindOpt ?z] => destruct z as [ [? ?] | ] eqn: ? ;
                                                   simpl in *; try discriminate
              end.
      rewrite addD_addD_plus; reflexivity.
      eauto.
      simpl;  match goal with
                |- context [DecodeBindOpt ?z] => destruct z as [ [? ?] | ] eqn: ? ;
                                                   simpl in *; try discriminate
              end.
      rewrite addD_addD_plus; reflexivity.
      eauto.
      }
      all: idtac.
      repeat (intros; eapply Bind_DecodeMEquivAlignedDecodeM);
        eauto using @Return_DecodeMEquivAlignedDecodeM.
      eapply AlignedDecodeUnusedCharM.
  Qed.

  Lemma AlignedDecodeBindUnusedCharM {C : Type}
        (t : unit -> DecodeM (C * ByteString) ByteString)
        (t' : unit -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (DecodeMEquivAlignedDecodeM (t ()) (@t' ()))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_unused_word (sz := 8) (monoidUnit := ByteString_QueueMonoidOpt) v cd;
                          t a b0 cd')
           (fun numBytes => b <- SkipCurrentByte; @t' b numBytes)%AlignedDecodeM.
  Proof.
    intro; eapply Bind_DecodeMEquivAlignedDecodeM; eauto using AlignedDecodeUnusedCharM.
    intro; destruct a; eauto.
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
    : forall (v : ByteBuffer.t (S (S numBytes)))
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

  Lemma decode_word_aligned_ByteString_overflow
        {sz'}
    : forall (b : t (word 8) sz')
             {sz : nat}
             (cd : CacheDecode),
      lt sz' sz
      -> decode_word (sz := 8 * sz) (build_aligned_ByteString b) cd = None.
  Proof.
    induction b; intros.
    - unfold build_aligned_ByteString; simpl.
      inversion H; subst; reflexivity.
    - destruct sz; try omega.
      apply lt_S_n in H.
      pose proof (IHb _ cd H).
      unfold decode_word, WordOpt.decode_word.
      rewrite <- mult_n_Sm, plus_comm.
      rewrite decode_word_plus'.
      rewrite (@aligned_decode_char_eq' _ 0).
      simpl.
      unfold build_aligned_ByteString, decode_word in *.
      simpl in H0.
      first [destruct (decode_word' (sz + (sz + (sz + (sz + (sz + (sz + (sz + (sz + 0))))))))
                                    {|
                                      padding := 0;
                                      front := WO;
                                      paddingOK := build_aligned_ByteString_subproof (*n b *);
                                      numBytes := n;
                                      byteString := b |}) as [ [? ?] | ]
            | destruct (decode_word' (sz + (sz + (sz + (sz + (sz + (sz + (sz + (sz + 0))))))))
                                     {|
                                       padding := 0;
                                       front := WO;
                                       paddingOK := build_aligned_ByteString_subproof n b;
                                       numBytes := n;
                                       byteString := b |}) as [ [? ?] | ]]
      ; simpl in *; try congruence.
  Qed.

  Lemma AlignedDecodeBind2CharM {C : Type}
        (t : word 16 -> DecodeM (C * ByteString) ByteString)
        (t' : word 16 -> forall {numBytes}, AlignedDecodeM C numBytes)
    : (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, b0, cd') <- decode_word (monoidUnit := ByteString_QueueMonoidOpt) (sz := 16) v cd;
                          t a b0 cd')
           (fun numBytes => b <- GetCurrentByte; b' <- GetCurrentByte; w <- return (Core.append_word b' b); t' w).
  Proof.
    intros; eapply DecodeMEquivAlignedDecodeM_trans with
                (bit_decoder1 :=
                   (fun (v : ByteString) (cd : CacheDecode) => `(w1, bs, cd') <-  decode_word (sz := 8) v cd;
                                                               `(w2, bs, cd') <-  decode_word (sz := 8) bs cd';
                                                               t (Core.append_word w2 w1) bs cd')).
    eapply AlignedDecodeBindCharM; intros.
    eapply AlignedDecodeBindCharM; intros.
    eapply DecodeMEquivAlignedDecodeM_trans.
    eapply (H _).
    intros; reflexivity.
    intros; higher_order_reflexivity.
    intros.
    unfold decode_word.
    rewrite (decode_word_plus' 8 8).
    unfold DecodeBindOpt2, DecodeBindOpt, BindOpt, If_Opt_Then_Else.
    destruct (decode_word' 8 b) as [ [? ?] | ]; eauto.
    destruct (decode_word' 8 b0) as [ [? ?] | ]; eauto.
    rewrite <- eq_rect_eq_dec; eauto using eq_nat_dec.
    rewrite addD_addD_plus; reflexivity.
    intros; reflexivity.
  Qed.

  Lemma CorrectAlignedEncoderForFormatChar_f
        {S} (proj : S -> word 8)
    : CorrectAlignedEncoder
        (Projection_Format format_word proj)
        (fun sz v idx s => SetCurrentByte v idx (proj s)).
  Proof.
    intros.
    unfold CorrectAlignedEncoder. eexists (Compose_Encode  (fun c env => Some ((build_aligned_ByteString (cons (word 8) c 0 (nil (word 8))), addE env 8))) (fun s => Some (proj s))); split; [ | split].
    - unfold Compose_Encode, Projection_Format, Compose_Format; intros.
      split; intros.
      + setoid_rewrite aligned_format_char_eq.
        injections.
        intros ? ?; apply unfold_computes; eexists; intuition eauto.
      + simpl in H; discriminate.
    - unfold Compose_Encode; simpl; intros.
      injections; reflexivity.
    - unfold Compose_Encode, EncodeMEquivAlignedEncodeM; intros; injections; intuition; simpl.
      + injections; simpl; unfold SetCurrentByte.
        unfold plus; fold plus.
        destruct (NPeano.ltb idx (idx + Datatypes.S m)) eqn: ? ; try omega.
        * eexists (Vector.append v1 (Vector.cons _ (proj s) _ v2)); split.
          { repeat f_equal; try omega.
            clear; simpl in v.
            revert v v2; induction v1; intros.
            - replace v with (Vector.cons _ (Vector.hd v) _ (Vector.tl v)).
              + generalize (Vector.tl v); apply Vector.case0; reflexivity.
              + revert v; generalize 0; apply Vector.caseS; simpl;
                  intros; reflexivity.
            - simpl; rewrite IHv1; reflexivity.
          }
          { rewrite !ByteString_enqueue_ByteString_assoc.
            rewrite <- !build_aligned_ByteString_append.
            assert (idx + 1 + m = idx + Datatypes.S m) by omega.
            pose proof (Vector_append_assoc _ _ _ H v1 (Vector.cons (word 8) (proj s) 0 (Vector.nil (word 8))) v2).
            simpl in H1; unfold Core.char in *;             unfold plus in *; fold plus in *; rewrite H1.
            generalize (append (append v1 (Vector.cons (word 8) (proj s) 0 (Vector.nil (word 8)))) v2).
            rewrite H; reflexivity.
          }
        * destruct (le_lt_dec (idx + Datatypes.S m) idx); try omega.
          apply NPeano.ltb_lt in l; congruence.
      + injections; simpl; unfold SetCurrentByte.
        destruct (NPeano.ltb idx numBytes') eqn: ?; eauto.
        apply NPeano.ltb_lt in Heqb.
        unfold build_aligned_ByteString in H0.
        unfold length_ByteString in H0; simpl padding in H0; simpl numBytes in H0.
        omega.
      + injections; simpl in *; omega.
      + discriminate.
  Defined.

  Lemma CorrectAlignedEncoderForFormatChar
    : CorrectAlignedEncoder
        (format_word (monoidUnit := ByteString_QueueMonoidOpt))
        (@SetCurrentByte _ _).
  Proof.
    replace (@SetCurrentByte _ _)
      with (fun (sz : nat) v idx s => SetCurrentByte (n := sz) v idx (id s)).
    eapply refine_CorrectAlignedEncoder.
    2: eapply (CorrectAlignedEncoderForFormatChar_f id).
    split; intros.
    + unfold Projection_Format, Compose_Format.
      intros v Comp_v; rewrite unfold_computes in Comp_v; destruct_ex; intuition.
      subst; eauto.
    + intro; apply (H v).
      unfold Projection_Format, Compose_Format in *.
      rewrite unfold_computes; eexists.
      subst; eauto.
    + eapply functional_extensionality_dep; intros.
      repeat (eapply functional_extensionality; intros).
      reflexivity.
  Defined.

  Lemma CorrectAlignedEncoderForFormatUnusedWord
        {S}
    : CorrectAlignedEncoder
        (format_unused_word 8 (monoidUnit := ByteString_QueueMonoidOpt))
        (fun sz v idx (s : S) => SetCurrentByte v idx (wzero 8)).
  Proof.
    intros; eapply refine_CorrectAlignedEncoder;
      eauto using (CorrectAlignedEncoderForFormatChar_f (fun _ => wzero 8)).
    simpl; split; intros.
    + unfold format_unused_word, Projection_Format, Compose_Format; simpl.
      intros ? ?.
      rewrite unfold_computes in *.
      destruct_ex; split_and; subst.
      eexists; split; eauto.
      rewrite unfold_computes; eauto.
    + unfold format_unused_word, Projection_Format, Compose_Format; simpl.
      intros ?.
      eapply (H _).
      unfold format_unused_word, Projection_Format, Compose_Format; simpl.
      destruct_ex; split_and; subst.
      rewrite unfold_computes; eauto.
      eexists _; split; eauto.
      unfold format_word; eauto.
  Defined.

  Lemma CorrectAlignedEncoderForProjection_Format
        {S S'}
        (f : S -> S')
        (format : FormatM S' ByteString)
        (encoder : forall n, AlignedEncodeM n)
    :
      CorrectAlignedEncoder format encoder
      -> CorrectAlignedEncoder (Projection_Format format f)
                            (fun sz v idx (s : S) => encoder sz v idx (f s)).
  Proof.
    intros; eapply refine_CorrectAlignedEncoder.
    split; intros.
    - rewrite refine_Projection_Format at 1. higher_order_reflexivity.
    - intro.
      eapply H.
      apply refine_Projection_Format in H0. eauto.
    - destruct X; intuition.
      eexists (fun s env => x (f s) env); intuition eauto.
      eapply H; eauto.
      eapply H; eauto.
      unfold EncodeMEquivAlignedEncodeM in *; intros.
      specialize (H2 env (f s) idx); intuition eauto.
  Defined.

  Lemma CollapseCorrectAlignedEncoderFormatWord
        {S : Type}
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
    : forall {sz sz'} (f : S ->  word sz) (f' : S -> word sz') k encoder,
      CorrectAlignedEncoder
        (Projection_Format format_word (fun s => combine (f' s) (f s))
                           ++ k)
        encoder
      -> CorrectAlignedEncoder
           (Projection_Format format_word f
                              ++ Projection_Format format_word f'
                              ++ k)
           encoder.
  Proof.
    intros; eapply refine_CorrectAlignedEncoder; eauto.
    intros.
    rewrite !refine_sequence_Format.
    unfold compose, Bind2.
    rewrite !refine_Projection_Format.
    pose proof CollapseFormatWord.
    unfold compose, Bind2 in H.
    rewrite <- H; eauto.
    split.
    - f_equiv; intro.
      rewrite !refine_sequence_Format.
      simpl.
      unfold compose, Bind2.
      simplify with monad laws.
      rewrite !refine_Projection_Format.
      setoid_rewrite refineEquiv_bind_bind.
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_bind.
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_unit.
      reflexivity.
    - intros.
      intro.
      simpl.
      apply refine_sequence_Format in H1.
      unfold compose, Bind2 in H1.
      computes_to_inv.
      apply refine_Projection_Format in H1.
      apply refine_sequence_Format in H1'.
      unfold compose, Bind2 in H1'.
      unfold format_word in *.
      computes_to_inv; subst.
      apply refine_Projection_Format in H1'.
      computes_to_inv; subst.
      simpl in *.
      eapply H0.
      unfold sequence_Format, compose, Bind2.
      computes_to_econstructor.
      apply refine_Projection_Format.
      eauto.
      computes_to_econstructor; eauto.
      simpl.
      rewrite addE_addE_plus in H1''0;
      rewrite plus_comm; eauto.
  Defined.

  Lemma CollapseCorrectAlignedEncoderFormatWord'
        {S : Type}
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
    : forall {sz sz'} (f : S ->  word sz) (f' : S -> word sz') k encoder,
      CorrectAlignedEncoder
        (Projection_Format format_word f
                           ++ Projection_Format format_word f'
                           ++ k)
        encoder
      -> CorrectAlignedEncoder
           (Projection_Format format_word (fun s => combine (f' s) (f s))
                              ++ k)
           encoder.
  Proof.
    intros; eapply refine_CorrectAlignedEncoder; eauto.
    intros.
    rewrite !refine_sequence_Format.
    unfold compose, Bind2.
    rewrite !refine_Projection_Format.
    pose proof CollapseFormatWord'.
    unfold compose, Bind2 in H.
    rewrite H; eauto.
    split.
    - f_equiv; intro.
      rewrite !refine_sequence_Format.
      simpl.
      unfold compose, Bind2.
      simplify with monad laws.
      rewrite !refine_Projection_Format.
      setoid_rewrite refineEquiv_bind_bind.
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_bind.
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_unit.
      reflexivity.
    - intros.
      intro.
      simpl.
      apply refine_sequence_Format in H1.
      unfold compose, Bind2 in H1.
      computes_to_inv.
      apply refine_Projection_Format in H1.
      unfold format_word in *.
      computes_to_inv; subst.
      simpl in *.
      eapply H0.
      unfold sequence_Format, compose, Bind2.
      computes_to_econstructor.
      apply refine_Projection_Format.
      eauto.
      computes_to_econstructor; eauto.
      simpl.
      computes_to_econstructor; eauto.
      apply refine_Projection_Format.
      eauto.
      computes_to_econstructor; eauto.
      simpl.
      rewrite addE_addE_plus;
      rewrite plus_comm; eauto.
  Defined.

  Lemma refine_CollapseFormatWord
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
    : forall {sz sz'} (w : word sz) (w' : word sz') format_1 format_2 ce,
      refine (format_1 ce) (format_word w ce)
      -> (forall ce, refine (format_2 ce) (format_word w' ce))
      -> refine ((format_1
                    ThenC format_2) ce)
                ((format_word (combine w' w)) ce).
  Proof.
    intros.
    etransitivity.
    instantiate (1 := ((format_word (combine w' w)) ThenC (fun ce => ret (ByteString_id, ce))) ce).
    rewrite <- CollapseFormatWord; eauto.
    unfold compose, Bind2; intros.
    rewrite H; setoid_rewrite H0; setoid_rewrite refineEquiv_bind_bind;
      repeat setoid_rewrite refineEquiv_bind_unit.
    simpl.
    pose proof mempty_right; simpl in *; rewrite H1; reflexivity.
    unfold compose, Bind2; intros; eauto.
    repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    pose proof mempty_right; simpl in *; rewrite H1; reflexivity.
  Qed.

  Lemma refine_CollapseFormatWord'
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
        {S}
    : forall {sz sz'} (f : S -> word sz) (f' : S -> word sz')
             (format_1 format_2 : FormatM S _),
      (forall s env, refine (format_1 s env) (Projection_Format format_word f s env))
      -> (forall s env, refine (format_2 s env) (Projection_Format format_word f' s env))
      -> (forall s env, refine ((format_1 ++ format_2) s env)
                               (Projection_Format format_word (fun s => combine (f' s) (f s)) s env)).
  Proof.
    intros.
    unfold sequence_Format, compose, Projection_Format, Compose_Format, Bind2.
    rewrite H; setoid_rewrite H0.
    intros ? ?.
    rewrite unfold_computes in H1.
    destruct_ex; intuition; subst.
    pose proof (CollapseFormatWord (sz' := sz') (sz := sz) addE_addE_plus (f s) (f' s)
               (fun ce => ret (ByteString_id, ce)) env); eauto.
    unfold compose in H1.
    unfold Bind2 in H1.
    repeat setoid_rewrite refineEquiv_bind_unit in H1.
    simpl in H1.
    unfold format_word in H2.
    pose proof mempty_right.
    simpl in H3.
    rewrite !H3 in H1.
    eapply H1 in H2.
    computes_to_inv; subst.
    computes_to_econstructor.
    unfold Projection_Format, Compose_Format; apply unfold_computes; eexists; intuition eauto.
    unfold format_word; computes_to_econstructor.
    computes_to_econstructor.
    unfold Projection_Format, Compose_Format; apply unfold_computes; eexists; intuition eauto.
    unfold format_word; computes_to_econstructor.
    simpl.
    eauto.
  Qed.

  Lemma format_words' {n m}
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
    : forall (w : word (n + m)) ce,
      refine (format_word (monoidUnit := ByteString_QueueMonoidOpt) w ce)
             ((format_word (monoidUnit := ByteString_QueueMonoidOpt) (split1' _ _ w)
                           ThenC (format_word (monoidUnit := ByteString_QueueMonoidOpt) (split2' _ _ w)))
                ce).
  Proof.
    induction n.
    - unfold compose; simpl; intros.
      unfold format_word at 2; simpl.
      autorewrite with monad laws.
      simpl; rewrite addE_addE_plus.
      pose proof mempty_left as H'; simpl in H'; rewrite H'.
      reflexivity.
    - unfold plus; fold plus; simpl; intros.
      rewrite (word_split_SW w) at 1.
      rewrite format_SW_word.
      unfold compose, Bind2.
      rewrite (IHn (word_split_tl w) (addE ce 1)).
      unfold compose, Bind2.
      unfold format_word; autorewrite with monad laws.
      simpl.
      rewrite format_word_S.
      pose proof mappend_assoc as H'; simpl in H'.
      rewrite !H'.
      rewrite !addE_addE_plus; simpl.
      f_equiv.
      f_equiv.
      f_equiv.
      rewrite !word_split_hd_SW_word, !word_split_tl_SW_word.
      fold plus.
      clear;
        generalize (split1' n m (word_split_tl w))
                   (ByteString_enqueue (word_split_hd w) ByteString_id).
      induction w0; simpl in *.
      + intros; pose proof (mempty_right b) as H; simpl in H; rewrite H; eauto.
      + intros.
        rewrite <- (IHw0 (wtl w) b0).
        pose proof enqueue_mappend_opt as H'''; simpl in H'''.
        rewrite <- H'''; eauto.
      + eauto.
  Qed.

  Lemma format_words {n m}
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
    : forall (w : word (n + m)) ce,
      refine (format_word (monoidUnit := ByteString_QueueMonoidOpt) w ce)
             ((format_word (monoidUnit := ByteString_QueueMonoidOpt) (split2 m n (eq_rect _ _ w _ (trans_plus_comm _ _)))
                           ThenC (format_word (monoidUnit := ByteString_QueueMonoidOpt) (split1 m n (eq_rect _ _ w _ (trans_plus_comm _ _)))))
                ce).
  Proof.
    intros; rewrite format_words'.
    rewrite split1'_eq, split2'_eq; reflexivity.
    eauto.
  Qed.

  Lemma CorrectAlignedEncoderForFormatNChar'
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
        {sz}
    : forall encoder,
      (CorrectAlignedEncoder
            (format_word (monoidUnit := ByteString_QueueMonoidOpt))
            (fun sz => encoder sz))
      -> CorrectAlignedEncoder
           (format_word (monoidUnit := ByteString_QueueMonoidOpt))
           (fun sz' => AppendAlignedEncodeM (fun v idx w => @SetCurrentByte _ _ sz' v idx (split1' 8 sz w))
                                            (fun v idx w => encoder sz' v idx (split2' 8 sz w))).
  Proof.
    intros; pose proof (format_words addE_addE_plus (n := 8) (m := sz)) as H';
      eapply refine_CorrectAlignedEncoder.
    split.
    - unfold flip, pointwise_relation; eapply H'.
    - intros; intro.
      eapply H.
      unfold compose, format_word; computes_to_econstructor; eauto.
      unfold compose, format_word; computes_to_econstructor; eauto.
    - eapply refine_CorrectAlignedEncoder.
      split; intros.
      rewrite <- split2'_eq, <- split1'_eq.
      3: eapply CorrectAlignedEncoderForThenC.
      (*3: intros; eapply (@CorrectAlignedEncoderForFormatChar_f (word (8 + sz))
        (split1' 8 sz)).*)
      instantiate (1 := Projection_Format format_word (split2' 8 sz)).
      rewrite refine_sequence_Format.
      instantiate (1 := Projection_Format format_word (split1' 8 sz)).
      unfold compose, Bind2; rewrite refine_Projection_Format; f_equiv.
      intro; rewrite refine_Projection_Format; f_equiv.
      2: eapply CorrectAlignedEncoderForProjection_Format; eauto.
      + intro.
        eapply H.
        rewrite <- split2'_eq, <- split1'_eq in H0.
        unfold sequence_Format.
        unfold compose, Bind2 in *; computes_to_inv; computes_to_econstructor.
        apply refine_Projection_Format; eauto.
        computes_to_econstructor.
        apply refine_Projection_Format; eauto.
        subst; eauto.
      + intros.
        instantiate (1 := (@CorrectAlignedEncoderForFormatChar_f (word (8 + sz)) (split1' 8 sz))).
        destruct (projT1 (CorrectAlignedEncoderForFormatChar_f (split1' 8 sz)) s env) eqn: ?.
        * eexists _, _; split; eauto.
          apply refine_Projection_Format; eauto.
          unfold format_word; eauto.
        * generalize (proj2 (proj1 (projT2 (CorrectAlignedEncoderForFormatChar_f (split1' 8 sz))) s env));
            intro.
          eapply H1 in Heqo.
          eapply Heqo in H; intuition eauto.
  Defined.

  Fixpoint SetCurrentBytes' (* Sets the bytes at the current index and increments the current index. *)
           {n sz : nat}
    : @AlignedEncodeM _ (word (sz * 8)) n :=
    match sz return @AlignedEncodeM _ (word (sz * 8)) _ with
    | 0 => AlignedEncode_Nil n
    | S sz' => AppendAlignedEncodeM (fun v idx w => SetCurrentByte v idx (split1' 8 (sz' * 8) w))
                                    (fun v idx w => SetCurrentBytes' v idx (split2' 8 (sz' * 8) w))
    end.

  Fixpoint SetCurrentBytes (* This version produces better code. *)
           {n sz : nat} {struct sz}
    : @AlignedEncodeM _ (word (sz * 8)) n :=
    match sz as n0 return (AlignedEncodeM n) with
    | 0 => AlignedEncode_Nil n
    | S sz0 =>
      fun v idx w =>
        match sz0 return word (S sz0 * 8) -> _ with
        | 0 => fun (w' : word 8) => SetCurrentByte v idx w'
        | S sz1 => fun _  => (* ignored to get proper recursive call *)
                    AppendAlignedEncodeM
                      (fun (v : t Core.char n) (idx : nat) (w : word (S sz0 * 8)) =>
                         SetCurrentByte v idx (split1' 8 (sz0 * 8) w))
                      (fun (v : t Core.char n) (idx : nat) (w : word (S sz0 * 8)) =>
                         SetCurrentBytes v idx (split2' 8 (sz0 * 8) w))
                      v idx w
        end w
    end.

  Local Arguments split1' : simpl never.
  Local Arguments split2' : simpl never.

  Lemma split1'_8_0 :
    forall w, (split1' 8 0 w) = w.
  Proof. intros; compute in (type of w); shatter_word w; reflexivity. Qed.

  Lemma SetCurrentBytes_SetCurrentBytes' :
    forall n sz v idx w c,
      @SetCurrentBytes n sz v idx w c =
      @SetCurrentBytes' n sz v idx w c.
  Proof.
    induction sz; simpl; intros.
    - reflexivity.
    - destruct sz;
        unfold AppendAlignedEncodeM, SetCurrentByte;
        destruct (_ <? _) eqn:?; unfold If_Opt_Then_Else.
      + unfold SetCurrentBytes', AlignedEncode_Nil, ReturnAlignedEncodeM; simpl.
        destruct (S _ <? S _) eqn:?; rewrite ?Nat.ltb_lt, ?Nat.ltb_ge, ?split1'_8_0 in *;
          (reflexivity || omega).
      + reflexivity.
      + rewrite IHsz; reflexivity.
      + reflexivity.
  Qed.

  Corollary CorrectAlignedEncoderForFormatNChar
            (addE_addE_plus :
               forall ce n m, addE (addE ce n) m = addE ce (n + m))
            (addE_0 :
               forall ce, addE ce 0 = ce)
            {sz}
    : CorrectAlignedEncoder
        (format_word (monoidUnit := ByteString_QueueMonoidOpt))
        (fun n => @SetCurrentBytes n sz).
  Proof.
    eapply CorrectAlignedEncoder_morphism with (encode := (fun n => @SetCurrentBytes' n sz)).
    apply EquivFormat_reflexive.
    auto using SetCurrentBytes_SetCurrentBytes'.
    unfold CorrectAlignedEncoder.
    induction sz; simpl; intros.
    - eapply refine_CorrectAlignedEncoder; intros.
      shatter_word s; unfold format_word; simpl.
      split.
      unfold format_word; rewrite addE_0; higher_order_reflexivity.
      intros; intro.
      eapply H.
      eauto.
      + eapply CorrectAlignedEncoderForDoneC.
    - eapply (CorrectAlignedEncoderForFormatNChar'
                addE_addE_plus
                (fun sz' => @SetCurrentBytes' sz' sz));
        eauto.
  Defined.

  Lemma CorrectAlignedEncoderForFormatMChar_f n
        {S}
        (addE_addE_plus :
           forall ce n m, addE (addE ce n) m = addE ce (n + m))
        (addE_0 :
           forall ce, addE ce 0 = ce)
        (proj : S -> word (n * 8))
    : CorrectAlignedEncoder
        (Projection_Format format_word proj)
        (fun sz v idx s => SetCurrentBytes v idx (proj s)).
  Proof.
    eapply CorrectAlignedEncoderForProjection_Format with
        (format := format_word)
        (encoder := fun sz => @SetCurrentBytes sz n)
        (f := proj).
    eapply CorrectAlignedEncoderForFormatNChar; eauto.
  Defined.

End AlignEncodeWord.

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
