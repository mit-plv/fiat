(* UpperBound of a list.*)
Require Import Coq.Lists.List Coq.Bool.Bool Fiat.Common Fiat.Computation.Core Fiat.Computation.Refinements.General.

Open Scope list_scope.

Section Upperbound.
  Variable A : Type.
  Variable B : Type.
  Variable f f' : A -> B.
  Variable R : B -> B -> Prop.
  Variable R_dec : forall a b, {R a b} + {~ R a b}.

  (* every element in xs is `rel` to x *)
  Definition upperbound  (x : A) (xs : list A) :=
    forall x', List.In x' xs -> R (f x) (f' x').

  (* if you decide to pick some x', it must be the upperbound of the list *)
  Definition pick_upperbound (xs : list A) : Comp (option A) :=
    {x | (forall x', x = Some x' -> List.In x' xs /\ upperbound x' xs)}%comp.

  (* an inefficient way to implement pick_upperbound *)
  Fixpoint check_upperbound_ineff (v : A) (xs : list A) : bool :=
    match xs with
      | [ ] => true
      | x :: xs' => andb (if R_dec (f v) (f' x) then true else false)
                         (check_upperbound_ineff v xs')
    end.

  Fixpoint choose_upperbound_ineff' (xs : list A) (ys : list A) : option A :=
    match ys with
      | [ ] => None
      | y :: ys' => match choose_upperbound_ineff' xs ys' with
                      | None => if check_upperbound_ineff y xs
                                then Some y
                                else None
                      | Some v => Some v
                    end
    end.

  Definition choose_upperbound_ineff (xs : list A) : option A :=
    choose_upperbound_ineff' xs xs.

  Lemma choose_upperbound_ineff'_close :
    forall xs ys x, choose_upperbound_ineff' xs ys = Some x -> List.In x ys.
  Proof.
    induction ys; intuition; try discriminate; simpl in *;
    remember (choose_upperbound_ineff' xs ys) as c; destruct c;
    [ right | destruct (check_upperbound_ineff a xs); inversion H ]; intuition.
  Qed.

  Corollary choose_upperbound_ineff_close :
    forall xs x, choose_upperbound_ineff xs = Some x -> List.In x xs.
  Proof.
    unfold choose_upperbound_ineff; intuition;
    eapply choose_upperbound_ineff'_close; eauto.
  Qed.

  Lemma check_upperbound_ineff_sound :
    forall v xs, check_upperbound_ineff v xs = true -> upperbound v xs.
  Proof.
    unfold upperbound; induction xs; simpl in *; intuition;
    apply andb_true_iff in H; intuition; subst;
    find_if_inside; intuition.
  Qed.

  Lemma choose_upperbound_ineff'_is_upperbound :
    forall xs ys x, choose_upperbound_ineff' xs ys = Some x -> upperbound x xs.
  Proof.
    induction ys; intuition; try discriminate; simpl in *;
    remember (choose_upperbound_ineff' xs ys) as c; destruct c; [
      apply IHys |
      remember (check_upperbound_ineff a xs) as c'; destruct c'; inversion H;
      apply check_upperbound_ineff_sound; symmetry; subst ]; trivial.
  Qed.

  Corollary choose_upperbound_ineff_is_upperbound :
    forall xs x, choose_upperbound_ineff xs = Some x -> upperbound x xs.
  Proof.
    unfold choose_upperbound_ineff; intuition;
    eapply choose_upperbound_ineff'_is_upperbound; eauto.
  Qed.

  Theorem refine_pick_upperbound_ineff :
    forall (xs : list A),
      refine (pick_upperbound xs)
             (ret (choose_upperbound_ineff xs)).
  Proof.
    unfold pick_upperbound, choose_upperbound_ineff; intuition;
    refine pick val _; try reflexivity; intuition;
    [ apply choose_upperbound_ineff_close | apply choose_upperbound_ineff_is_upperbound ]; trivial.
  Qed.

  Lemma rel_dec_comm :
    forall a b, {R b a} + {~ R b a}.
  Proof. intuition. Qed.
End Upperbound.

(* notation for upperbound *)
Notation "{{ x 'in' xs | P 'forall' y }}" := (pick_upperbound (fun x y => P) xs) (at level 70) : comp_scope.
(*Notation "{{ x 'in' xs | P 'forall' y }} : A" := (@pick_upperbound A (fun x y => P) xs) (at level 70) : comp_scope. *)

(* Old definition of upperbound
Section UpperBound.

  Context {A : Type}.
  Variable R : A -> A -> Prop.
  Context {Pre_R : PreOrder R}.

  Definition upperbound (As : list A) (r : A) :=
    forall r', In r' As -> R r' r.

  Variable (R_dec : forall a a', {R a a'} + {R a' a}).
  Context {MinA : A}.
  Variable R_MinA : forall a : A, R MinA a.

  Definition find_max
             (As : list A) : A :=
    fold_right (fun a acc => if R_dec a acc then acc else a) MinA As.

  Lemma fold_right_max_is_max
  : forall As a,
      In a As -> R a (find_max As).
  Proof.
    induction As; intros; inversion H; subst; simpl;
    find_if_inside; intros; eauto.
    - reflexivity.
    - etransitivity; eauto.
  Qed.

  Definition find_upperbound
             (As : list A) : list A :=
    let max := find_max As in
    filter (fun a => if R_dec max a then true else false) As.

  Lemma fold_right_higher_is_higher
  : forall As a,
      (forall a', In a' As -> R a' a) ->
      R (find_max As) a.
  Proof.
    induction As; simpl; intros; [ apply R_MinA | ].
    find_if_inside;
    etransitivity; eauto; reflexivity.
  Qed.

  Lemma find_upperbound_highest_length
  : forall As a,
      In a (find_upperbound As) -> forall a', In a' As -> R a' a.
  Proof.
    unfold find_upperbound; intros.
    apply filter_In in H; intuition.
    destruct (R_dec (find_max As) a).
    etransitivity.
    eapply fold_right_max_is_max; eauto.
    eassumption.
    discriminate.
  Qed.

End UpperBound. *)
