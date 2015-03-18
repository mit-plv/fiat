(* UpperBound of a list.*)
Require Import Coq.Lists.List ADTSynthesis.Common.
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

End UpperBound.
