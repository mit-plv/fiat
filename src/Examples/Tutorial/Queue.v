Require Import Tutorial.


Section data.
  Variable data : Set.
  (* Here we prioritize over an arbitrary type of data stored within stacks. *)
  Variable dummy : data.
  (* Sometimes it's useful to have a default value of the data type. *)

  (** Type signature of an implementation of functional queues *)
  Definition sig : ADTSig :=
    ADTsignature {
      Constructor "empty" : rep,
      Method "enqueue" : rep * data -> rep,
      Method "dequeue" : rep -> rep * (option data)
    }.

  (** The specification of functional correctness *)
  Definition spec : ADT sig :=
    ADTRep (list data)
           (* This first part is the abstract representation type. *)
    {
      Def Constructor "empty" : rep :=
        ret nil,
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

  Lemma absRel_initial : absRel nil (nil, nil).
  Proof.
    reflexivity.
  Qed.

  Lemma absRel_push : forall d abs conc, absRel abs conc
    -> absRel (abs ++ d :: nil) (fst conc, d :: snd conc).
  Proof.
    unfold absRel; simpl; intros; subst.
    rewrite app_assoc; reflexivity.
  Qed.

  Lemma tl_cons : forall A (x : A) ls1 ls2,
    x :: ls1 = ls2
    -> ls1 = tl ls2.
  Proof.
    destruct ls2; simpl; congruence.
  Qed.

  Hint Resolve absRel_initial absRel_push tl_cons.

  Lemma absRel_must_be_nil : forall abs conc,
    absRel abs conc
    -> fst conc = nil
    -> snd conc = nil
    -> abs = nil.
  Proof.
    unfold absRel; destruct conc; simpl; intros; subst; reflexivity.
  Qed.

  Hint Resolve absRel_must_be_nil.

  Lemma eta_abs_fst : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold absRel; destruct abs; simpl; intuition.
    destruct (fst conc); simpl in *; intuition congruence.
  Qed.

  Lemma eta_abs_snd : forall abs conc,
    absRel abs conc
    -> snd conc <> nil
    -> abs = hd dummy abs :: tl abs.
  Proof.
    unfold absRel; destruct abs; simpl; intros.
    destruct (snd conc); simpl in *; intuition.
    apply (f_equal (@length _)) in H.
    repeat rewrite app_length in H; simpl in H.
    omega.
    auto.
  Qed.

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

  Lemma absRel_reversed_data : forall abs conc r,
    absRel abs conc
    -> fst conc = nil
    -> snd conc <> nil
    -> r = rev (snd conc)
    -> hd dummy abs = hd dummy r.
  Proof.
    unfold absRel; intuition simpl in *; subst; auto.
  Qed.

  Lemma absRel_fast_rep : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> absRel (tl abs) (tl (fst conc), snd conc).
  Proof.
    unfold absRel; intuition simpl in *; subst.
    destruct (fst conc); simpl in *; tauto.
  Qed.

  Lemma absRel_fast_data : forall abs conc,
    absRel abs conc
    -> fst conc <> nil
    -> hd dummy abs = hd dummy (fst conc).
  Proof.
    unfold absRel; intuition simpl in *; subst; auto.
    destruct (fst conc); simpl in *; tauto.
  Qed.

  Hint Resolve absRel_reversed_rep absRel_fast_rep.

  (* Now we start deriving an implementation, in a correct-by-construction way. *)
  Theorem implementation : FullySharpened spec.
  Proof.
    start sharpening ADT.
    hone representation using absRel.

    simplify with monad laws.
    pick.
    finish honing.

    simplify with monad laws.
    pick.
    finish honing.

    refine_testnil (fst r_n).

    refine_testnil (snd r_n).

    assert (r_o = nil) by eauto; subst.
    monad_simpl.
    pick.
    monad_simpl.
    finish honing.

    apply refine_let with (v := rev (snd r_n)); intros.

    erewrite (eta_abs_snd (abs := r_o)) by eauto.
    monad_simpl.
    pick.
    monad_simpl.
    erewrite absRel_reversed_data by eauto.
    finish honing.

    cbv beta.
    finish honing.

    erewrite (eta_abs_fst (abs := r_o)) by eauto.
    monad_simpl.
    pick.
    monad_simpl.
    erewrite absRel_fast_data with (abs := r_o) by eauto.
    finish honing.

    cleanup.
    finish honing.

    finalize.
  Defined.

  Definition impl := Eval simpl in projT1 implementation.
  Print impl.
End data.
