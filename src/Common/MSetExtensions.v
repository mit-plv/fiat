Require Export Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetProperties
        Coq.MSets.MSetFacts.
Require Import Fiat.Common.Instances.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.

Module MSetExtensionsOn (E: DecidableType) (Import M: WSetsOn E).
  Module Export BasicFacts := WFactsOn E M.
  Module Export BasicProperties := WPropertiesOn E M.

  Definition of_list (ls : list E.t) : t
    := List.fold_right
         add
         empty
         ls.

  Global Instance Equal_Equivalence : Equivalence Equal := _.

  Global Instance equal_Equivalence : Equivalence equal.
  Proof.
    setoid_rewrite <- equal_iff; exact _.
  Qed.

  Tactic Notation "setoid_rewrite_in_all" open_constr(lem) :=
    idtac;
    match goal with
    | _ => rewrite !lem
    | [ H : _ |- _ ] => rewrite !lem in H
    | _ => setoid_rewrite lem
    | [ H : _ |- _ ] => setoid_rewrite lem in H
    end.

  Tactic Notation "setoid_rewrite_in_all" "<-" open_constr(lem) :=
    idtac;
    match goal with
    | _ => rewrite <- !lem
    | [ H : _ |- _ ] => rewrite <- !lem in H
    | _ => setoid_rewrite <- lem
    | [ H : _ |- _ ] => setoid_rewrite <- lem in H
    end.

  Ltac eq_bools_to_is_trues :=
    idtac;
    let x := match goal with |- ?x = ?y :> bool => x end in
    let y := match goal with |- x = ?y :> bool => y end in
    let Hx := fresh in
    let Hy := fresh in
    destruct x eqn:Hx;
    [ symmetry
    | destruct y eqn:Hy;
      [ rewrite <- Hx; clear Hx
      | reflexivity ] ];
    fold_is_true.

  Ltac eq_bools_to_is_trues_in H :=
    idtac;
    let x := match type of H with ?x = ?y :> bool => x end in
    let y := match type of H with x = ?y :> bool => y end in
    let Hx := fresh in
    let Hy := fresh in
    destruct x eqn:Hx;
    [ symmetry
    | destruct y eqn:Hy;
      [ rewrite <- Hx; clear Hx
      | reflexivity ] ];
    fold_is_true.
  Ltac eq_bools_to_is_trues_in_all :=
    idtac;
    match goal with
    | [ H : _ = _ :> bool |- _ ]
      => eq_bools_to_is_trues_in H
    end.

  Ltac to_caps_step :=
    first [ setoid_rewrite_in_all subset_spec
          | setoid_rewrite_in_all equal_spec
          | setoid_rewrite_in_all <- not_true_iff_false
          | setoid_rewrite_in_all negb_true_iff
          | progress fold_is_true
          | progress eq_bools_to_is_trues
          | progress eq_bools_to_is_trues_in_all ].
  Ltac to_caps := repeat to_caps_step.

  Create HintDb sets discriminated.
  Global Hint Immediate union_subset_1 union_subset_2 inter_subset_1 inter_subset_2 equal_refl : sets.

  Ltac simplify_sets_step :=
    idtac;
    match goal with
    | [ H : ?x [<=] ?y, H' : ?y [<=] ?x |- _ ]
      => pose proof (subset_antisym H H');
         clear H H'
    | [ H : context[subset ?x ?y] |- _ ]
      => match type of H with
         | context[subset y x] => fail 1
         | _ => idtac
         end;
         progress replace (equal y x) with (equal x y)
           in H by auto with sets
    | _ => setoid_subst_rel Equal
    end.

  Ltac simplify_sets := repeat simplify_sets_step.

  Ltac push_In_step :=
    first [ progress unfold Equal in *
          | setoid_rewrite_in_all union_spec
          | setoid_rewrite_in_all inter_spec ].

  Ltac push_In := repeat push_In_step.

  Lemma equal_refl_b x : equal x x.
  Proof. to_caps; auto with sets. Qed.

  Lemma equal_sym_b x y : equal x y = equal y x.
  Proof. to_caps; simplify_sets; reflexivity. Qed.

  Hint Immediate equal_sym_b : sets.

  Lemma union_subset_1b
    : forall s s', subset s (union s s').
  Proof. to_caps; auto with sets. Qed.

  Lemma union_subset_2b
    : forall s s', subset s' (union s s').
  Proof. to_caps; auto with sets. Qed.

  Lemma inter_subset_1b
    : forall s s', subset (inter s s') s.
  Proof. to_caps; auto with sets. Qed.

  Lemma inter_subset_2b
    : forall s s', subset (inter s s') s'.
  Proof. to_caps; auto with sets. Qed.

  Hint Rewrite union_subset_1b union_subset_2b inter_subset_1b inter_subset_2b equal_refl_b : sets.

  Lemma union_idempotent x : Equal (union x x) x.
  Proof. push_In; tauto. Qed.

  Lemma inter_idempotent x : Equal (inter x x) x.
  Proof. push_In; tauto. Qed.

  Hint Immediate union_idempotent inter_idempotent : sets.

  Lemma union_idempotent_b x : equal (union x x) x.
  Proof. to_caps; auto with sets. Qed.

  Lemma inter_idempotent_b x : equal (inter x x) x.
  Proof. to_caps; auto with sets. Qed.

  Hint Rewrite union_idempotent_b inter_idempotent_b : sets.

  Global Instance Subset_Proper_Equal_iff
    : Proper (Equal ==> Equal ==> iff) Subset.
  Proof. repeat intro; unfold Subset; simplify_sets; reflexivity. Qed.
  Global Instance Subset_Proper_Equal : Proper (Equal ==> Equal ==> impl) Subset | 1.
  Proof. repeat intro; simplify_sets; eauto with nocore. Qed.
  Global Instance Subset_Proper_Equal_flip : Proper (Equal ==> Equal ==> flip impl) Subset | 1.
  Proof. repeat intro; simplify_sets; eauto with nocore. Qed.

  Global Instance subset_Proper_equal
    : Proper (equal ==> equal ==> Logic.eq) subset.
  Proof. repeat intro; to_caps; simplify_sets; assumption. Qed.

  Lemma equal_or_subset_and_not_equal_subset_b {x y}
    : (equal x y || (subset x y && negb (equal x y))) = subset x y.
  Proof.
    destruct (equal x y) eqn:?; simpl; bool_congr; to_caps; simplify_sets;
      try reflexivity;
      try assumption.
  Qed.

  Lemma equal_or_subset_and_not_equal_subset {x y}
    : (Equal x y \/ (Subset x y /\ ~Equal x y)) <-> Subset x y.
  Proof.
    destruct (equal x y) eqn:?; simpl; bool_congr; to_caps; simplify_sets;
      intuition.
  Qed.

  Hint Rewrite @equal_or_subset_and_not_equal_subset @equal_or_subset_and_not_equal_subset_b : sets.

  Ltac handle_known_comparisons_step :=
    idtac;
    lazymatch goal with
    | [ |- context[subset (inter ?x ?y) ?x] ]
      => replace (subset (inter x y) x) with true by (symmetry; apply inter_subset_1b)
    | [ |- context[subset (inter ?x ?y) ?y] ]
      => replace (subset (inter x y) y) with true by (symmetry; apply inter_subset_2b)
    | [ |- context[subset ?x (union ?x ?y)] ]
      => replace (subset x (union x y)) with true by (symmetry; apply union_subset_1b)
    | [ |- context[subset ?y (union ?x ?y)] ]
      => replace (subset y (union x y)) with true by (symmetry; apply union_subset_2b)
    | [ |- context[equal (?f ?x ?y) ?x] ]
      => replace (equal (f x y) x) with (equal x (f x y)) by apply equal_sym_b
    | [ |- context[equal (?f ?x ?y) ?y] ]
      => replace (equal (f x y) y) with (equal y (f x y)) by apply equal_sym_b
    end.

  Ltac handle_known_comparisons := repeat handle_known_comparisons_step.
End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.
