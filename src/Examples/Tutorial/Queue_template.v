Require Import Tutorial.


Section data.
  Variable data : Set.
  (* Here we parameterize over an arbitrary type of data stored within stacks. *)
  Variable dummy : data.
  (* Sometimes it's useful to have a default value of the data type. *)

  (** Type signature of an implementation of functional queues *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "empty" : rep,
      Method "enqueue" : rep * data -> rep,
      Method "dequeue" : rep -> rep * (option data)
    }.
  (* Notice that "effectful" methods just return new private-state values,
   * in addition to being passed original state values as parameters. *)

  (** The specification of functional correctness *)
  Definition spec : ADT sig :=
    Def ADT
    {
      rep := list data, (* This first part is the abstract representation type. *)
      Def Constructor "empty" : rep :=
        ret nil,,
      Def Method1 "enqueue" (self : rep) (d : data) : rep :=
        ret (self ++ d :: nil),
      Def Method0 "dequeue"(self : rep) : rep * (option data) :=
        match self with
        | nil => ret (self, None)
        | d :: self' => ret (self', Some d)
        end
    }.

  (* We define an abstraction relation, connecting abstract and concrete states.
   * Classic trick: simulate a queue with two stacks,
   * one of which needs to be reversed to reproduce the abstract queue. *)
  Definition absRel (abs : list data) (conc : list data * list data) :=
    abs = fst conc ++ rev (snd conc).

  (* The appropriate initial states are related. *)
  Lemma absRel_initial : absRel nil (nil, nil).
  Proof.
    reflexivity.
  Qed.

  (* The simple implementation of "push" preserves the relation. *)
  Lemma absRel_push : forall d abs conc, absRel abs conc
    -> absRel (abs ++ d :: nil) (fst conc, d :: snd conc).
  Proof.
    unfold absRel; simpl; intros; subst.
    rewrite app_assoc; reflexivity.
  Qed.

  (* When the concrete state is empty, so must be the abstract state. *)
  Lemma absRel_must_be_nil : forall abs conc,
    absRel abs conc
    -> fst conc = nil
    -> snd conc = nil
    -> abs = nil.
  Proof.
    unfold absRel; destruct conc; simpl; intros; subst; reflexivity.
  Qed.

  (* The abstract queue may be expanded into its first element and tail,
   * if it's related to a concrete state with nonempty first list.
   * In general, such a property depends on a list being nonempty. *)
  Lemma eta_abs_fst : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold absRel; destruct abs; simpl; intuition.
    destruct (fst conc); simpl in *; intuition congruence.
  Qed.

  (* The abstract queue may be expanded into its first element and tail,
   * if it's related to a concrete state with nonempty second list. *)
  Lemma eta_abs_snd : forall abs conc,
    absRel abs conc
    -> snd conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold absRel; destruct abs; simpl; intros.
    destruct (snd conc); simpl in *; intuition.
    apply (f_equal (@length _)) in H.
    repeat rewrite app_length in H; simpl in H.
    arithmetic.
    auto.
  Qed.

  (* The case for preserving the relation on "pop",
   * when we need to reverse the second list. *)
  Lemma absRel_reversed_rep : forall abs conc r,
    absRel abs conc
    -> fst conc = nil
    -> snd conc <> nil
    -> r = rev (snd conc)
    -> absRel (tl abs) (tl r, nil).
  Proof.
    unfold absRel; intuition simpl in *; subst.
    autorewrite with core; auto.
  Qed.

  (* The case for returning the right data value on "pop",
   * when we need to reverse the second list. *)
  Lemma absRel_reversed_data : forall abs conc r,
    absRel abs conc
    -> fst conc = nil
    -> snd conc <> nil
    -> r = rev (snd conc)
    -> hd dummy abs = hd dummy r.
  Proof.
    unfold absRel; intuition simpl in *; subst; auto.
  Qed.

  (* The case for preserving the relation on "pop",
   * in the fast path where the first list is not empty. *)
  Lemma absRel_fast_rep : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> absRel (tl abs) (tl (fst conc), snd conc).
  Proof.
    unfold absRel; intuition simpl in *; subst.
    destruct (fst conc); simpl in *; tauto.
  Qed.

  (* The case for returning the right data value on "pop",
   * in the fast path where the first list is not empty. *)
  Lemma absRel_fast_data : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> hd dummy abs = hd dummy (fst conc).
  Proof.
    unfold absRel; intuition simpl in *; subst; auto.
    destruct (fst conc); simpl in *; tauto.
  Qed.

  (* Now we start deriving an implementation, in a correct-by-construction way. *)
  Theorem implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using absRel.

    monad_simpl.
    pick_by absRel_initial.
    done.

    monad_simpl.
    pick_by absRel_push.
    done.

    refine_testnil (fst r_n).

    refine_testnil (snd r_n).

    assert (r_o = nil) by (eapply absRel_must_be_nil; eauto).
    subst.
    monad_simpl.
    pick_by absRel_initial.
    monad_simpl.
    done.

    refine_let (rev (snd r_n)).

    erewrite eta_abs_snd with (abs := r_o) by eauto.
    monad_simpl.
    pick_by absRel_reversed_rep.
    monad_simpl.
    erewrite absRel_reversed_data by eauto.
    done.

    done.

    erewrite eta_abs_fst with (abs := r_o) by eauto.
    monad_simpl.
    pick_by absRel_fast_rep.
    monad_simpl.
    erewrite absRel_fast_data with (abs := r_o) by eauto.
    done.

    rewrite refine_let_ret.
    rewrite refine_testnil_ret.
    rewrite refine_testnil_ret.
    done.

    finalize.
  Defined.

  (* We can now extract a standlone Gallina term for this ADT. *)
  Definition impl := Eval simpl in projT1 implementation.
  Print impl.

  (* We can go further, building tactics to automate most of our strategy. *)

  Hint Resolve absRel_initial absRel_push absRel_must_be_nil absRel_reversed_rep absRel_fast_rep.

  Ltac queue' :=
    repeat match goal with
           | _ => progress monad_simpl
           | _ => pick
           | [ H : absRel ?abs _ |- _ ] =>
             match abs with
             | nil => fail 1
             | _ => assert (abs = nil) by eauto; subst
             end
           | [ _ : absRel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] =>
             (erewrite eta_abs_fst with (abs := abs_) by eauto)
             || (erewrite eta_abs_snd with (abs := abs_) by eauto)
           | [ |- context[hd dummy _] ] =>
             (erewrite absRel_reversed_data by eauto)
             || (erewrite absRel_fast_data by eauto)
           end.

  Ltac queue := queue'; done.

  Theorem even_more_automated_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using absRel; try queue.

    refine_testnil (fst r_n); [
      refine_testnil (snd r_n); [ queue |
        refine_let (rev (snd r_n)); queue | queue ] | queue | ].

    cleanup; done.

    finalize.
  Defined.



























  (* OK, we just spent all that effort on automating the derivation.
   * Ideally the same automation will keep working with different implementations.
   * Let's try another (dumb, slow) one. *)
  Definition dumbAbsRel (abs conc : list data) := conc = rev abs.

  Fixpoint getLast (ls : list data) : (list data * data) :=
    match ls with
    | nil => (nil, dummy)
    | d :: nil => (nil, d)
    | d :: ls' =>
      let p := getLast ls' in
      (d :: fst p, snd p)
    end.

  Lemma dumbAbsRel_initial : dumbAbsRel nil nil.
  Proof.
    reflexivity.
  Qed.

  Lemma dumbAbsRel_push : forall abs conc d,
    dumbAbsRel abs conc
    -> dumbAbsRel (abs ++ d :: nil) (d :: conc).
  Proof.
    unfold dumbAbsRel; simpl; intros.
    rewrite rev_unit.
    congruence.
  Qed.

  Lemma dumbAbsRel_must_be_nil : forall abs conc,
    dumbAbsRel abs conc
    -> conc = nil
    -> abs = nil.
  Proof.
    unfold dumbAbsRel; simpl; intros.
    subst.
    destruct abs; simpl in *; intuition.
    exfalso; eauto.
  Qed.

  Lemma dumbAbsRel_eta : forall abs conc,
    dumbAbsRel abs conc
    -> conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold dumbAbsRel; simpl; intros.
    subst.
    destruct abs; intuition.
  Qed.

  Lemma getLast_append_list : forall ls d,
    fst (getLast (ls ++ d :: nil)) = ls.
  Proof.
    induction ls; simpl; intuition.
    destruct (ls ++ d :: nil) eqn:Heq.
    exfalso; eauto.
    rewrite <- Heq.
    rewrite IHls.
    auto.
  Qed.

  Lemma dumbAbsRel_pop_rep : forall abs conc r,
    dumbAbsRel abs conc
    -> conc <> nil
    -> r = getLast conc
    -> dumbAbsRel (tl abs) (fst r).
  Proof.
    unfold dumbAbsRel; intros; subst.
    destruct abs; simpl in *; intuition.
    apply getLast_append_list.
  Qed.

  Lemma getLast_append_data : forall ls d,
    snd (getLast (ls ++ d :: nil)) = d.
  Proof.
    induction ls; auto.

    intros.
    simpl app.
    unfold getLast.
    fold getLast.
    destruct (ls ++ d :: nil) eqn:Heq.
    exfalso; eauto.
    rewrite <- Heq.
    rewrite IHls.
    auto.
  Qed.

  Lemma dumbAbsRel_pop_data : forall abs conc r,
    dumbAbsRel abs conc
    -> conc <> nil
    -> r = getLast conc
    -> hd dummy abs = snd r.
  Proof.
    unfold dumbAbsRel; intros; subst.
    destruct abs; simpl in *; intuition.
    rewrite getLast_append_data; auto.
  Qed.

  Hint Resolve dumbAbsRel_initial dumbAbsRel_push dumbAbsRel_must_be_nil dumbAbsRel_pop_rep.

  (* Here's our first derivation, showing a bit more manual perspective. *)
  Theorem dumb_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using dumbAbsRel; try queue.

    refine_testnil r_n.

    assert (r_o = nil) by eauto.
    subst.
    queue.

    refine_let (getLast r_n).
    erewrite dumbAbsRel_eta with (abs := r_o) by eauto.
    erewrite dumbAbsRel_pop_data by eauto.
    queue.

    cleanup.
    done.

    finalize.
  Defined.

  (* We use a double colon to override the prior definition. *)
  Ltac queue' ::=
    repeat match goal with
           | _ => progress monad_simpl
           | _ => pick
           | [ H : dumbAbsRel ?abs _ |- _ ] =>
             match abs with
             | nil => fail 1
             | _ => assert (abs = nil) by eauto; subst
             end
           | [ _ : dumbAbsRel ?abs_ ?conc |- context[match ?abs_ with nil => _ | _ :: _ => _ end] ] =>
             erewrite dumbAbsRel_eta with (abs := abs_) by eauto
           | [ |- context[hd dummy _] ] =>
             erewrite dumbAbsRel_pop_data by eauto
           end.

  (* Now let's automate it more. *)
  Theorem more_automated_dumb_implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using dumbAbsRel; try queue.

    refine_testnil r_n; [ queue |
      refine_let (getLast r_n); queue | ].

    queue'.
    cleanup.
    done.

    finalize.
  Defined.
End data.
