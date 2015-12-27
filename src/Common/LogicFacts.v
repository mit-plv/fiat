Require Coq.Lists.List.
Require Import Coq.Program.Basics.

Section LogicFacts.
  Lemma or_false :
    forall (P: Prop), P \/ False <-> P.
  Proof.
    tauto.
  Qed.

  Lemma false_or :
    forall (P Q: Prop),
      (False <-> P \/ Q) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma false_or' :
    forall (P Q: Prop),
      (P \/ Q <-> False) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false :
    forall P,
      (False <-> P) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false' :
    forall P,
      (P <-> False) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma and_True :
    forall P,
      (P /\ True) <-> P.
  Proof.
    tauto.
  Qed.

  Lemma not_exists_forall :
    forall {A} (P: A -> Prop),
      (~ (exists a, P a)) <-> (forall a, ~ P a).
  Proof.
    firstorder.
  Qed.

  Lemma not_and_implication :
    forall (P Q: Prop),
      ( ~ (P /\ Q) ) <-> (P -> ~ Q).
  Proof.
    firstorder.
  Qed.

  Lemma eq_sym_iff :
    forall {A} x y, @eq A x y <-> @eq A y x.
  Proof.
    split; intros; symmetry; assumption.
  Qed.

  Lemma fold_right_and_True {ls : list Prop}
  : List.fold_right and True ls <-> (forall P, List.In P ls -> P).
  Proof.
    split; induction ls; simpl in *; repeat (intros [] || intro);
    repeat split; try assumption;
    try apply IHls; intros; eauto;
    match goal with
      | [ H : _ |- _ ]
        => apply H; solve [ left; reflexivity | right; assumption ]
    end.
  Qed.

  Lemma fold_right_and_True_map {A} {P : A -> Prop} {ls : list A}
  : List.fold_right and True (List.map P ls) <-> (forall x, List.In x ls -> P x).
  Proof.
    rewrite fold_right_and_True; split; intros H x Hx.
    { apply H, List.in_map, Hx. }
    { apply List.in_map_iff in Hx.
      destruct Hx as [? [? ?]]; subst; eauto. }
  Qed.

  Lemma forall_iff {A B C}
  : (forall x : A, (B x <-> C x)) -> ((forall x, B x) <-> (forall x, C x)).
  Proof.
    intro H; split; intros H' x; apply H, H'.
  Qed.

  Lemma forall_impl {A B C}
  : (forall x : A, (impl (B x) (C x))) -> (impl (forall x, B x) (forall x, C x)).
  Proof.
    intro H; intros H' x; apply H, H'.
  Qed.

  Lemma and_distr_or_r A B C
  : (A /\ (B \/ C)) <-> ((A /\ B) \/ (A /\ C)).
  Proof. tauto. Qed.
  Lemma and_distr_or_l A B C
  : ((B \/ C) /\ A) <-> ((B /\ A) \/ (C /\ A)).
  Proof. tauto. Qed.
  Lemma ex_distr_or A B C
  : (exists x : A, B x \/ C x) <-> ((exists x : A, B x) \/ (exists x : A, C x)).
  Proof.
    repeat (intros [] || split || intro);
    first [ do 2 first [ left | esplit ]; eassumption
          | do 2 first [ right | esplit ]; eassumption ].
  Defined.
End LogicFacts.
