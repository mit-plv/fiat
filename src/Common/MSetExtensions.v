Require Export Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetProperties
        Coq.MSets.MSetFacts.
Require Import Fiat.Common.Instances.
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

  Ltac to_caps_step :=
    first [ setoid_rewrite_in_all subset_spec
          | setoid_rewrite_in_all equal_spec ].
  Ltac to_caps := repeat to_caps_step.

  Create HintDb sets discriminated.
  Global Hint Immediate union_subset_1 union_subset_2 equal_refl : sets.

  Lemma equal_refl_b x : equal x x.
  Proof. to_caps; auto with sets. Qed.

  Lemma union_subset_1b
    : forall s s', subset s (union s s').
  Proof. to_caps; auto with sets. Qed.

  Lemma union_subset_2b
    : forall s s', subset s' (union s s').
  Proof. to_caps; auto with sets. Qed.

  Hint Rewrite union_subset_1b union_subset_2b equal_refl_b : sets.

  Lemma union_idempotent x : Equal (union x x) x.
  Proof.
    unfold Equal.
    setoid_rewrite union_spec.
    tauto.
  Qed.

  Hint Immediate union_idempotent : sets.

  Lemma union_idempotent_b x : equal (union x x) x.
  Proof. to_caps; auto with sets. Qed.

  Hint Rewrite union_idempotent_b : sets.

  Global Instance Subset_Proper_Equal_iff
    : Proper (Equal ==> Equal ==> iff) Subset | 1.
  Proof.
    intros ?? H ?? H'.
    unfold Subset, Equal in *.
    setoid_rewrite H.
    setoid_rewrite H'.
    reflexivity.
  Qed.
  Global Instance Subset_Proper_Equal : Proper (Equal ==> Equal ==> impl) Subset.
  Proof.
    intros ?? H ?? H'; rewrite H, H'; reflexivity.
  Qed.
  Global Instance Subset_Proper_Equal_flip : Proper (Equal ==> Equal ==> flip impl) Subset.
  Proof.
    intros ?? H ?? H'; rewrite H, H'; reflexivity.
  Qed.

  Global Instance subset_Proper_equal
    : Proper (equal ==> equal ==> Logic.eq) subset.
  Proof.
    intros a b H a' b' H'.
    destruct (subset b b') eqn:H'';
      [ | destruct (subset a a') eqn:H''';
          [ rewrite <- H''; clear H''; symmetry | reflexivity ] ];
      to_caps;
      setoid_subst_rel Equal; assumption.
  Qed.

End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.
