Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import
        Coq.ZArith.ZArith
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.BaseFormats.

Section Word.
  Context {sz : nat}.

  Context {T : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.
  Context {monoidfix : QueueMonoidOptFix monoidUnit}.

  Fixpoint encode_word' (s : nat) (w : word s) (b' : T) : T :=
    match w with
    | WO => b'
    | WS b s' w' => enqueue_opt b (encode_word' s' w' b')
    end.

  Definition encode_word (w : word sz) (ce : CacheFormat) : T * CacheFormat := (encode_word' sz w mempty, addE ce sz).

  Definition serialize := encode_word.

  Definition format_word (w : word sz) (ce : CacheFormat) : Comp (T * CacheFormat) :=
    ret (encode_word' sz w mempty, addE ce sz).

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

  Fixpoint decode_word' (s : nat) (b : T) {struct s} : option (word s * T) :=
    match s with
    | O => Some (WO, b)
    | S s' =>
      `(c, b') <- dequeue_opt b;
      `(w', b') <- decode_word' s' b';
      Some (SW_word c w', b')
    end.

  Definition decode_word (b : T) (cd : CacheDecode) : option (word sz * T * CacheDecode) :=
    Ifopt decode_word' sz b as decoded Then Some (decoded, addD cd sz) Else None.

  Lemma enqueue_opt_format_word :
    forall n w b b',
      enqueue_opt b (encode_word' n w b') =
      mappend (encode_word' n w b') (enqueue_opt b mempty).
  Proof.
    induction w; simpl; intros; eauto.
    - rewrite <- enqueue_mappend_opt, mempty_right; auto.
    - rewrite !IHw.
      rewrite <- mappend_assoc.
      rewrite <- !enqueue_mappend_opt, !mempty_right.
      rewrite IHw; reflexivity.
  Qed.

  Lemma dequeue_encode_word'_enqueue_opt' :
    forall n w w' b b' ext,
      dequeue_opt w' = Some (b, b')
      -> dequeue_opt (mappend (encode_word' n w w') ext) =
           Some (b, (mappend (encode_word' n w b') ext)).
  Proof.
    induction w; simpl; intros.
    - erewrite dequeue_mappend_opt; eauto using dequeue_head_opt.
    - eapply dequeue_mappend_opt.
      rewrite enqueue_opt_format_word.
      erewrite IHw; eauto.
      rewrite <- enqueue_opt_format_word; reflexivity.
  Qed.

  Corollary dequeue_encode_word'_enqueue_opt :
    forall n w b ext,
      dequeue_opt (mappend (encode_word' n w (enqueue_opt b mempty)) ext) =
      Some (b, (mappend (encode_word' n w mempty) ext)).
  Proof.
    intros; eapply dequeue_encode_word'_enqueue_opt'.
    eapply dequeue_head_opt.
  Qed.

  Lemma dequeue_opt_Some' :
    forall n w ext,
      dequeue_opt (mappend (encode_word' (S n) w mempty) ext)
      = Some (word_split_hd w, (mappend (encode_word' n (word_split_tl w) mempty) ext)).
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

  Lemma decode_encode_word'
    : forall {n} w ext,
      decode_word' n (mappend (encode_word' n w mempty) ext)
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
                   (mappend (encode_word' n (word_split_tl x0) mempty)
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

  Lemma decode_encode_word'_Some
    : forall sz bin data ext,
      decode_word' sz bin = Some (data, ext)
      -> bin = mappend (encode_word' sz data mempty) ext.
  Proof.
    induction sz0; simpl; intros.
    - shatter_word data; simpl; injections.
      rewrite mempty_left; auto.
    - destruct (dequeue_opt bin) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate.
      destruct (decode_word' sz0 t) as [ [? ?] | ] eqn: ? ;
        simpl in *; try discriminate.
      injections.
      apply IHsz0 in Heqo0; subst.
      eapply dequeue_opt_inj; eauto.
      simpl.
      rewrite <- dequeue_encode_word'_enqueue_opt.
      clear; revert ext; induction w; simpl; auto; intros.
      rewrite !enqueue_opt_format_word, <- !mappend_assoc.
      rewrite IHw; reflexivity.
  Qed.

  Theorem Word_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder monoid (fun _ => True)
                     (fun _ => True)
                     eq
                     format_word decode_word P format_word.
  Proof.
    unfold CorrectDecoder, format_word, decode_word; split.
    - intros env env' xenv w w' ext env_OK Eeq _ ?.
      computes_to_inv; injections.
      generalize dependent sz.
      intros; rewrite decode_encode_word'; simpl.
      eexists _, _; split; intuition eauto using add_correct.
    - intros.
      destruct (decode_word' sz t)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      apply decode_encode_word'_Some in Heqo; subst.
      split; eauto using add_correct.
      eexists _, _; repeat split.
      eauto using add_correct.
  Qed.

  Corollary encode_Word_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder monoid
                     (fun _ => True)
                     (fun _ => True)
                     eq
                     (fun w ctx => ret (serialize w ctx)) decode_word P
                     (fun w ctx => ret (serialize w ctx)).
  Proof.
    unfold CorrectDecoder; split; intros.
    - eapply Word_decode_correct; eauto.
    - eapply Word_decode_correct in H1; eauto.
  Qed.

  Lemma decode_word'_le
    : forall (a : word sz) (b' b1 : T),
      decode_word' _ b1 = Some (a, b') -> le_B b' b1.
  Proof.
    intros; apply decode_encode_word'_Some in H; subst.
    unfold le_B.
    rewrite mappend_measure; lia.
  Qed.

  Lemma decode_word_le
    : forall (b1 : T) (cd : CacheDecode) (a : word sz)
             (b' : T) (cd' : CacheDecode),
      decode_word b1 cd = Some (a, b', cd') -> le_B b' b1.
  Proof.
    unfold decode_word.
    intros; destruct (decode_word' sz b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    injections.
    eapply decode_word'_le; eauto.
  Qed.

  Lemma decode_word'_lt
    : forall (a : word (S sz)) (b' b1 : T),
      decode_word' _ b1 = Some (a, b') -> lt_B b' b1.
  Proof.
    simpl; intros; injections; unfold lt_B.
    destruct (dequeue_opt b1) as [ [? ?] | ] eqn: ? ;
      subst; simpl in *; try discriminate.
    apply measure_dequeue_Some in Heqo; subst.
    destruct (decode_word' sz t) as [ [? ?] | ] eqn: ? ;
        subst; simpl in *; try discriminate.
    eapply decode_word'_le in Heqo0; injections.
    rewrite Heqo.
    unfold le_B in *.
    pose proof (B_measure_gt_0 b).
    lia.
  Qed.

  Lemma decode_word_lt
    : forall (b' : T) (cd : CacheDecode) (a : word (S sz))
             (b1 : T) (cd' : CacheDecode),
      Ifopt decode_word' _ b' as decoded Then Some (decoded, addD cd (S sz)) Else None = Some (a, b1, cd') -> lt_B b1 b'.
  Proof.
    intros; destruct (decode_word' (S sz) b') as [ [? ?] | ] eqn: ? ;
    try eapply decode_word'_lt in Heqo;
      simpl in *; try (subst; discriminate).
    injections.
    unfold lt_B in *.
    lia.
  Qed.

  Lemma format_word_measure
    : forall (a : word sz) ce b ce',
      format_word a ce ∋ (b, ce') ->
      bin_measure b = sz * B_measure_fix.
  Proof.
    unfold format_word.
    intros.
    computes_to_inv. injections.
    induction a; simpl.
    apply measure_mempty.

    rewrite measure_enqueue.
    rewrite IHa.
    rewrite B_measure_fix_consistent.
    lia.
  Qed.

  (* A similar lemma for [None] is only provable if we have [dequeue_opt b =
  None -> b = mempty]. *)
  Lemma decode_word_measure_some
    : forall (a : word sz) b cd b' cd',
      decode_word b cd = Some (a, b', cd') ->
      bin_measure b = sz * B_measure_fix + bin_measure b'.
  Proof.
    unfold decode_word.
    intros * H. destruct (decode_word' sz b) as [ [] | ] eqn:?;
      simpl in *; try discriminate; injections.
    revert dependent b.
    induction sz; intros; simpl in *; injections; eauto.
    destruct dequeue_opt as [[??]|] eqn:H; try discriminate; simpl in *.
    destruct decode_word' as [[??]|] eqn:H'; try discriminate; simpl in *.
    eapply measure_dequeue_Some in H.
    rewrite B_measure_fix_consistent in H.
    injections. apply IHn in H'. lia.
  Qed.

  Lemma word_B_measure_gt_0
    : (0 < sz -> 0 < sz * B_measure_fix)%nat.
  Proof.
    assert (0 < B_measure_fix)%nat by eauto using (B_measure_fix_gt_0 true).
    lia.
  Qed.

  Definition format_unused_word {S}
    : FormatM S T :=
    Compose_Format format_word (fun _ => {w : word sz | True})%comp.

  Fixpoint monoid_get_word {T}
           {monoid : Monoid T}
           {monoid_opt : QueueMonoidOpt monoid bool}
           (sz : nat)
           (b : T)
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
         (b : T)
  : option (word sz * T) := decode_word' sz b.

  Lemma monoid_dequeue_word_eq_decode_word' :
    forall (sz : nat)
           (b : T),
      monoid_dequeue_word sz b = decode_word' sz b.
  Proof.
    reflexivity.
  Qed.

  Lemma monoid_dequeue_encode_word'
        (sz' : nat)
    : forall (w : word sz') (ext : T),
      monoid_dequeue_word sz' (mappend (encode_word' _ w mempty ) ext) = Some (w, ext).
  Proof.
    intros; unfold monoid_dequeue_word.
    apply decode_encode_word'.
  Qed.

  Definition decode_unused_word' (s : nat) (b : T) : option (unit * T) :=
    Ifopt monoid_dequeue_word s b as b' Then Some (tt, snd b') Else None.

  Definition decode_unused_word
    : DecodeM (unit * T) T :=
    Compose_Decode decode_word (fun wt => (tt, snd wt)).

End Word.

Lemma EquivFormat_LaxTerminal {S T}
        {monoid' : Monoid T}
        {cache' : Cache}
  : forall format : FormatM S T,
    EquivFormat (Projection_Format format fst ++ LaxTerminal_Format) (DoneLax format) .
Proof.
  unfold EquivFormat, DoneLax, Projection_Format, Compose_Format, LaxTerminal_Format,
  sequence_Format, ComposeOpt.compose, Bind2;
    split; unfold refine; intros.
  - rewrite unfold_computes in H; destruct_ex; split_and; subst.
    destruct v; destruct s; simpl in *; subst.
    repeat computes_to_econstructor; eauto.
    rewrite unfold_computes; eexists; split; eauto.
    rewrite unfold_computes; eauto.
    simpl; computes_to_econstructor.
  - computes_to_inv; subst.
    rewrite unfold_computes in H; rewrite unfold_computes.
    destruct_ex; destruct v0; eexists; simpl in *; intuition eauto.
    subst; eauto.
Qed.

Theorem unused_word_decode_correct
        {sz : nat}
        {S T}
        {monoid : Monoid T}
        {cache : Cache}
        {cacheAddNat : CacheAdd cache nat}
        {monoidUnit : QueueMonoidOpt monoid bool}
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  :
    CorrectDecoder (S := S) monoid (fun _ => True)
                   (fun _ => True)
                   (fun s v => True)
                   (format_unused_word (sz := sz))
                   (decode_unused_word (sz := sz)) P
                   (format_unused_word (sz := sz)).
Proof.
  eapply format_decode_correct_alt.
  7: {
    eapply injection_decode_correct with (inj := fun _ => ()).
    eapply Compose_decode_correct with
        (view := (fun _ : S => {_ : word sz | True}%comp)).
    eapply encode_Word_decode_correct.
    eapply P_OK.
    simpl; intros; eauto.
    instantiate (1 := fun _ _ => True); eauto.
    instantiate (1 := fun _ => True); eauto.
    intros.
    simpl in H.
    instantiate (1 := fun _ env t => _ env t).
    instantiate (1 := format_unused_word u).
    apply unfold_computes.
    unfold format_unused_word, Compose_Format; eexists v; eauto.
    unfold format_word, serialize, encode_word in *; intuition eauto.
    apply unfold_computes; eauto.
  }
  - instantiate (1 := fun _ => True);
      unfold flip, pointwise_relation; intuition.
  - unfold flip, pointwise_relation; intuition.
  - unfold flip, pointwise_relation; intuition.
  - unfold flip, pointwise_relation, EquivFormat; intuition.
  - unfold flip, pointwise_relation; intuition.
  - unfold flip, pointwise_relation, EquivFormat; intuition.
Qed.

Arguments format_unused_word sz {_ _ _ _ _ _}.

Lemma monoid_get_encode_word' {T}
      {monoid : Monoid T}
      {monoid_opt : QueueMonoidOpt monoid bool}
      (sz : nat)
  : forall (w : word sz) (ext : T),
    monoid_get_word sz (mappend (encode_word' _ w mempty) ext) = Some w.
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
          (mappend (encode_word' sz (word_split_tl x0) mempty)
                     (mappend (enqueue_opt x mempty) ext))) as [ [? ?] | ];
            simpl in *; try discriminate.
          destruct (monoid_get_word sz t); try discriminate.
          injections.
          rewrite H0.
          simpl.
          rewrite <- (word_split_SW x0); auto.
  Qed.
