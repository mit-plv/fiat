Set Implicit Arguments.

Require Import Coq.Lists.List.

Section TopSection.

  Require Import Bedrock.Platform.Cito.GeneralTactics2.

  Lemma NoDup_cons_cons : forall A (x y : A) ls, List.NoDup (x :: y :: ls) -> x <> y.
    intros.
    inversion H.
    not_not.
    subst.
    intuition.
  Qed.

  Lemma NoDup_cons_elim : forall A ls (e : A), List.NoDup (e :: ls) -> forall e', List.In e' ls -> e' <> e.
    induction ls; simpl; intuition.
    subst.
    eapply NoDup_cons_cons in H.
    intuition.
    subst.
    inversion H; subst.
    intuition.
  Qed.

  Require Import Coq.Classes.Morphisms.

  Lemma Forall2_map : forall A B (f1 f2 : A -> B) R ls, pointwise_relation _ R f1 f2 -> Forall2 R (List.map f1 ls) (List.map f2 ls).
    unfold pointwise_relation.
    induction ls; simpl; intuition.
  Qed.

  Fixpoint fold_right_2 A (f : A -> A -> A) def ls :=
    match ls with
      | nil => def
      | x :: nil => x
      | x :: xs => f x (fold_right_2 f def xs)
    end.

End TopSection.
