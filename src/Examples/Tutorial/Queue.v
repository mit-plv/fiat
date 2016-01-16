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

  Hint Resolve tl_cons refine_pick_val.
  Hint Rewrite <- app_nil_end.

  Definition getNext (conc : list data * list data) : data * (list data * list data) :=
    match fst conc with
    | nil =>
      let ls' := rev (snd conc) in (hd dummy ls', (tl ls', nil))
    | x :: ls' =>
      (x, (ls', snd conc))
    end.

  Lemma absRel_pop_rep : forall abs conc newState,
    absRel abs conc
    -> ~(fst conc = nil /\ snd conc = nil)
    -> newState = getNext conc
    -> absRel (tl abs) (snd newState).
  Proof.
    unfold absRel; intuition; subst; simpl in *.
    destruct a, b; simpl in *; intuition (congruence || autorewrite with core; eauto).
  Qed.

  Lemma absRel_pop_result : forall abs conc newState,
    absRel abs conc
    -> ~(fst conc = nil /\ snd conc = nil)
    -> newState = getNext conc
    -> hd dummy abs = fst newState.
  Proof.
    unfold absRel; intuition; subst; simpl in *.
    destruct a, b; simpl in *; intuition (congruence || autorewrite with core; eauto).
  Qed.

  Lemma absRel_nonempty : forall x ls conc,
    absRel (x :: ls) conc
    -> ~(fst conc = nil /\ snd conc = nil).
  Proof.
    unfold absRel; intros.
    destruct (fst conc), (snd conc); simpl in *; intuition congruence.
  Qed.

  Hint Resolve absRel_initial absRel_push absRel_pop_rep absRel_nonempty.
  Hint Rewrite absRel_pop_result using tauto.

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

    Definition testnil A B (ls : list A) (cnil ccons : B) : B :=
      match ls with
      | nil => cnil
      | _ :: _ => ccons
      end.

    Lemma refine_testnil : forall A (ls : list A) B (c1 cnil ccons : Comp B),
      (ls = nil -> refine c1 cnil)
      -> (ls <> nil -> refine c1 ccons)
      -> refine c1 (testnil ls cnil ccons).
    Proof.
      destruct ls; intuition congruence.
    Qed.

    Add Parametric Morphism A B
    : (@testnil A (Comp B))
        with signature
        @eq (list A)
          ==> @refine B
          ==> @refine B
          ==> @refine B
          as refine_testnil_morphism.
    Proof.
      destruct y; auto.
    Qed.

    Lemma refine_testnil_ret : forall A B (ls : list A) (cnil ccons : B),
      refine (testnil ls (ret cnil) (ret ccons)) (ret (testnil ls cnil ccons)).
    Proof.
      destruct ls; reflexivity.
    Qed.

    etransitivity.
    apply refine_testnil with (ls := fst r_n); intro.
    etransitivity.
    apply refine_testnil with (ls := snd r_n); intro.
    
    Lemma absRel_must_be_nil : forall abs conc,
      absRel abs conc
      -> fst conc = nil
      -> snd conc = nil
      -> abs = nil.
    Proof.
      unfold absRel; destruct conc; simpl; intros; subst; reflexivity.
    Qed.

    Hint Resolve absRel_must_be_nil.

    assert (r_o = nil) by eauto; subst.
    simplify with monad laws; simpl.
    pick.
    simplify with monad laws; simpl.
    finish honing.

    Lemma refine_let : forall A B (v : A) c1 (c2 : A -> Comp B),
      (forall x, x = v -> refine c1 (c2 x))
      -> refine c1 (let x := v in c2 x).
    Proof.
      auto.
    Qed.

    apply refine_let with (v := rev (snd r_n)); intros.

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

    erewrite (eta_abs_snd (abs := r_o)) by eauto.
    simplify with monad laws; simpl.

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

    Hint Resolve absRel_reversed_rep.

    pick.
    simplify with monad laws.
    erewrite absRel_reversed_data by eauto.
    finish honing.

    cbv beta.
    finish honing.

    Lemma eta_abs_fst : forall abs conc,
      absRel abs conc
      -> fst conc <> nil
      -> abs = hd dummy abs :: tl abs.
    Proof.
      unfold absRel; destruct abs; simpl; intuition.
      destruct (fst conc); simpl in *; intuition congruence.
    Qed.

    erewrite (eta_abs_fst (abs := r_o)) by eauto.
    simplify with monad laws; simpl.
    
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

    Hint Resolve absRel_fast_rep.

    Lemma reversing_matches_abs : forall abs conc,
      absRel abs conc
      -> fst conc = nil
      -> rev (snd conc) = abs.
    Proof.
      unfold absRel; intros.
      rewrite H0 in *; auto.
    Qed.

    pick.
    simplify with monad laws.
    erewrite absRel_fast_data with (abs := r_o) by eauto.
    finish honing.

    repeat rewrite refine_testnil_ret.
    finish honing.

    finish_SharpeningADT_WithoutDelegation.
  Defined.

  Definition impl := Eval simpl in projT1 implementation.
  Print impl.
End data.
