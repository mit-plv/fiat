Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts.

Unset Implicit Arguments.
Section Word.
  Context {sz : nat}.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Fixpoint format_word' (s : nat) (w : word s) (b' : B) : B :=
    match w with
    | WO => b'
    | WS b s' w' => enqueue_opt b (format_word' s' w' b')
    end.

  Eval compute in (wordToNat (WS true (WS false (WS false (WS false (WO)))))).

  Definition encode_word (w : word sz) (ce : CacheEncode) : B * CacheEncode := (format_word' sz w mempty, addE ce sz).

  Definition format_word (w : word sz) (ce : CacheEncode) : Comp (B * CacheEncode) :=
    ret (format_word' sz w mempty, addE ce sz).

  Fixpoint SW_word {sz} (b : bool) (w : word sz) : word (S sz) :=
    match w with
    | WO => WS b WO
    | WS b' s' w'' => WS b' (SW_word b w'')
    end.

  Fixpoint word_split_hd {sz} (w : word (S sz))
    : bool :=
    match sz return word (S sz) -> bool with
    | 0 => @whd _
    | S n' => fun w => word_split_hd (wtl w)
    end w.

  Fixpoint word_split_tl {sz} (w : word (S sz))
    : word sz :=
    match sz return word (S sz) -> word sz with
    | 0 => fun _ => WO
    | S n' => fun w => WS (whd w) (word_split_tl (wtl w))
    end w.

  Lemma word_split_SW {n}
    : forall (w : word (S n)),
      w = SW_word (word_split_hd w) (word_split_tl w).
  Proof.
    induction n; simpl; intros.
    - shatter_word w; reflexivity.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      rewrite (IHn x0) at 1; reflexivity.
  Qed.

  Fixpoint decode_word' (s : nat) (b : B) {struct s} : option (word s * B) :=
    match s with
    | O => Some (WO, b)
    | S s' =>
      `(c, b') <- dequeue_opt b;
      `(w', b') <- decode_word' s' b';
      Some (SW_word c w', b')
    end.

  Definition decode_word (b : B) (cd : CacheDecode) : option (word sz * B * CacheDecode) :=
    Ifopt decode_word' sz b as decoded Then Some (decoded, addD cd sz) Else None.

  Lemma enqueue_opt_format_word :
    forall n w b b',
      enqueue_opt b (format_word' n w b') =
      mappend (format_word' n w b') (enqueue_opt b mempty).
  Proof.
    induction w; simpl; intros; eauto.
    - rewrite <- enqueue_mappend_opt, mempty_right; auto.
    - rewrite !IHw.
      rewrite <- mappend_assoc.
      rewrite <- !enqueue_mappend_opt, !mempty_right.
      rewrite IHw; reflexivity.
  Qed.

  Lemma dequeue_format_word'_enqueue_opt' :
    forall n w w' b b' ext,
      dequeue_opt w' = Some (b, b')
      -> dequeue_opt (mappend (format_word' n w w') ext) =
           Some (b, (mappend (format_word' n w b') ext)).
  Proof.
    induction w; simpl; intros.
    - erewrite dequeue_mappend_opt; eauto using dequeue_head_opt.
    - eapply dequeue_mappend_opt.
      rewrite enqueue_opt_format_word.
      erewrite IHw; eauto.
      rewrite <- enqueue_opt_format_word; reflexivity.
  Qed.

  Corollary dequeue_format_word'_enqueue_opt :
    forall n w b ext,
      dequeue_opt (mappend (format_word' n w (enqueue_opt b mempty)) ext) =
      Some (b, (mappend (format_word' n w mempty) ext)).
  Proof.
    intros; eapply dequeue_format_word'_enqueue_opt'.
    eapply dequeue_head_opt.
  Qed.

  Lemma dequeue_opt_Some' :
    forall n w ext,
      dequeue_opt (mappend (format_word' (S n) w mempty) ext)
      = Some (word_split_hd w, (mappend (format_word' n (word_split_tl w) mempty) ext)).
  Proof.
    induction n; simpl; intros.
    - shatter_word w; simpl in *.
      erewrite dequeue_mappend_opt; eauto using dequeue_head_opt.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      simpl in *.
      rewrite enqueue_opt_format_word.
      rewrite <- mappend_assoc.
      rewrite IHn.
      rewrite enqueue_opt_format_word.
      rewrite <- mappend_assoc; auto.
  Qed.

  Lemma decode_format_word'
    : forall {n} w ext,
      decode_word' n (mappend (format_word' n w mempty) ext)
      = Some (w, ext).
  Proof.
    induction n; simpl; intros; try shatter_word w; simpl in *.
    - rewrite mempty_left; reflexivity.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      rewrite enqueue_opt_format_word.
      rewrite <- !mappend_assoc.
      destruct n.
      + shatter_word x0; simpl.
        rewrite mempty_left.
        erewrite dequeue_mappend_opt;
          eauto using dequeue_head_opt.
        simpl.
        rewrite mempty_left; auto.
      + rewrite dequeue_opt_Some'.
        unfold DecodeBindOpt, BindOpt at 1; unfold If_Opt_Then_Else.
        assert (decode_word' (S n)
                   (mappend (format_word' n (word_split_tl x0) mempty)
                              (mappend (enqueue_opt x mempty) ext))
                = Some (WS x (word_split_tl x0), ext)).
        { simpl.
          pose proof (IHn (WS x (word_split_tl x0)) ext).
          simpl in H.
          rewrite enqueue_opt_format_word in H.
          rewrite <- mappend_assoc in H.
          rewrite H.
          eauto. }
        unfold BindOpt. rewrite H; simpl; rewrite <- (word_split_SW x0); auto.
  Qed.

  Lemma decode_format_word'_Some
    : forall sz bin data ext,
      decode_word' sz bin = Some (data, ext)
      -> bin = mappend (format_word' sz data mempty) ext.
  Proof.
    induction sz0; simpl; intros.
    - shatter_word data; simpl; injections.
      rewrite mempty_left; auto.
    - destruct (dequeue_opt bin) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate.
      destruct (decode_word' sz0 b0) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      apply IHsz0 in Heqo0; subst.
      eapply dequeue_opt_inj; eauto.
      simpl.
      rewrite <- dequeue_format_word'_enqueue_opt.
      clear; revert ext; induction w; simpl; auto; intros.
      rewrite !enqueue_opt_format_word, <- !mappend_assoc.
      rewrite IHw; reflexivity.
  Qed.

  Theorem Word_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder cache monoid (fun _ => True)
                              (fun _ _ => True)
                              format_word decode_word P.
  Proof.
    unfold CorrectDecoder, format_word, decode_word; split.
    - intros env env' xenv w w' ext env_OK Eeq _ _ Penc.
      computes_to_inv; injections.
      generalize dependent sz.
      intros; rewrite decode_format_word'; simpl.
      eexists; split; eauto using add_correct.
    - intros.
      destruct (decode_word' sz bin)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      apply decode_format_word'_Some in Heqo; subst.
      split; eauto using add_correct.
      eexists; eexists; repeat split.
      eauto using add_correct.
  Qed.

  Lemma decode_word'_le
    : forall (a : word sz) (b' b1 : B),
      decode_word' _ b1 = Some (a, b') -> le_B b' b1.
  Proof.
    intros; apply decode_format_word'_Some in H; subst.
    unfold le_B.
    rewrite mappend_measure; omega.
  Qed.

  Lemma decode_word_le
    : forall (b1 : B) (cd : CacheDecode) (a : word sz)
             (b' : B) (cd' : CacheDecode),
      decode_word b1 cd = Some (a, b', cd') -> le_B b' b1.
  Proof.
    unfold decode_word.
    intros; destruct (decode_word' sz b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    injections.
    eapply decode_word'_le; eauto.
  Qed.

  Lemma decode_word'_lt
    : forall (a : word (S sz)) (b' b1 : B),
      decode_word' _ b1 = Some (a, b') -> lt_B b' b1.
  Proof.
    simpl; intros; injections; unfold lt_B.
    destruct (dequeue_opt b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    apply measure_dequeue_Some in Heqo; subst.
    destruct (decode_word' sz b0) as [ [? ?] | ] eqn: ? ;
        subst; simpl in *; try discriminate.
    eapply decode_word'_le in Heqo0; injections.
    rewrite Heqo.
    unfold le_B in *.
    pose proof (B_measure_gt_0 b).
    omega.
  Qed.

  Lemma decode_word_lt
    : forall (b' : B) (cd : CacheDecode) (a : word (S sz))
             (b1 : B) (cd' : CacheDecode),
      Ifopt decode_word' _ b' as decoded Then Some (decoded, addD cd (S sz)) Else None = Some (a, b1, cd') -> lt_B b1 b'.
  Proof.
    intros; destruct (decode_word' (S sz) b') as [ [? ?] | ] eqn: ? ;
    try eapply decode_word'_lt in Heqo;
      simpl in *; try (subst; discriminate).
    injections.
    unfold lt_B in *.
    omega.
  Qed.

  Definition format_unused_word' (sz : nat) b
             (_ : unit) (ctx : CacheEncode) :=
    (w <- { w : word sz | True};
       ret (format_word' sz w b, addE ctx sz))%comp.

  Definition format_unused_word
             (sz : nat) :=
    format_unused_word' sz mempty tt.

  Fixpoint monoid_get_word {B}
           {monoid : Monoid B}
           {monoid_opt : QueueMonoidOpt monoid bool}
           (sz : nat)
           (b : B)
    : option (word sz) :=
    match sz with
    | 0 => Some WO
    | S sz' =>
      match dequeue_opt b with
      | Some (c, b') =>
        match monoid_get_word sz' b' with
        | Some w => Some (SW_word c w)
        | _ => None
        end
      | _ => None
      end
    end.

  Definition monoid_dequeue_word
         (sz : nat)
         (b : B)
  : option (word sz * B) := decode_word' sz b.

  Lemma monoid_dequeue_word_eq_decode_word' :
    forall (sz : nat)
           (b : B),
      monoid_dequeue_word sz b = decode_word' sz b.
  Proof.
    reflexivity.
  Qed.

  Lemma monoid_dequeue_format_word'
        (sz' : nat)
    : forall (w : word sz') (ext : B),
      monoid_dequeue_word sz' (mappend (format_word' _ w mempty ) ext) = Some (w, ext).
  Proof.
    intros; unfold monoid_dequeue_word.
    apply decode_format_word'.
  Qed.

  Definition decode_unused_word' (s : nat) (b : B) : option (unit * B) :=
    Ifopt monoid_dequeue_word s b as b' Then Some (tt, snd b') Else None.

  Definition decode_unused_word (sz' : nat)
             (b : B) (cd : CacheDecode) : option (unit * B * CacheDecode) :=
    Ifopt decode_unused_word' sz' b as decoded Then Some (decoded, addD cd sz') Else None.

  Theorem unused_word_decode_correct sz'
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder cache monoid (fun _ => True)
                              (fun _ _ => True)
                              (format_unused_word' sz' mempty) (decode_unused_word sz') P.
  Proof.
    unfold CorrectDecoder, format_unused_word', decode_unused_word; split.
    - intros env env' xenv w w' ext env_OK Eeq _ _ Penc.
      computes_to_inv; injections.
      unfold decode_unused_word'.
      rewrite monoid_dequeue_format_word'; simpl.
      destruct w.
      eexists; split; eauto using add_correct.
    - intros.
      destruct (decode_unused_word' sz' bin)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      unfold decode_unused_word', monoid_dequeue_word in Heqo.
      simpl in Heqo.
      split; auto.
      destruct (decode_word' sz' bin)  as [ [? ?] | ] eqn: ? ; simpl in *;
        try discriminate.
      injections.
      apply decode_format_word'_Some in Heqo0.
      eexists; eexists; repeat split.
      repeat computes_to_econstructor; eauto.
      apply Heqo0.
      apply add_correct; eauto.
  Qed.

End Word.

Arguments format_unused_word {_ _ _ _ _} sz ctx _.

Lemma monoid_get_format_word' {B}
      {monoid : Monoid B}
      {monoid_opt : QueueMonoidOpt monoid bool}
      (sz : nat)
  : forall (w : word sz) (ext : B),
    monoid_get_word sz (mappend (format_word' _ w mempty) ext) = Some w.
Proof.
  induction sz; simpl; intros; try shatter_word w; simpl in *.
    - reflexivity.
    - destruct (shatter_word_S w) as (?, (?, ?)); subst; simpl.
      rewrite enqueue_opt_format_word.
      rewrite <- !mappend_assoc.
      destruct sz.
      + shatter_word x0; simpl.
        rewrite mempty_left.
        erewrite dequeue_mappend_opt;
          eauto using dequeue_head_opt.
      + rewrite dequeue_opt_Some'.
          pose proof (IHsz (WS x (word_split_tl x0)) ext).
          simpl in *.
          rewrite enqueue_opt_format_word in H.
          rewrite <- mappend_assoc in H.
          destruct (dequeue_opt
          (mappend (format_word' sz (word_split_tl x0) mempty)
                     (mappend (enqueue_opt x mempty) ext))) as [ [? ?] | ];
            simpl in *; try discriminate.
          destruct (monoid_get_word sz b0); try discriminate.
          injections.
          rewrite H0.
          simpl.
          rewrite <- (word_split_SW x0); auto.
  Qed.
