Require Import Coq.Program.Program.
Require Import Fiat.Common.
(** * Various useful lemmas about logic *)

(** We prove things here mainly for the purpose of [setoid_rewrite]ing with instances of [impl] and [iff]. *)

Local Arguments impl / .
Local Arguments flip / .
Local Arguments pointwise_relation / .

Local Hint Extern 1 => progress simpl in *.
Local Hint Extern 1 => progress subst; eauto. (* WTF? *)
Local Hint Extern 1 => progress destruct_head_hnf sig.

Section forall_eq.
  (** We prove some lemmas about [forall] and [eq], for the benefit of setoid rewriting. *)
  Definition iff_remove_forall_eql A x (P : _ -> Prop)
  : iff (forall y : A, y = x -> P y) (P x).
  Proof. firstorder. Defined.

  Definition iff_remove_forall_eqr A x (P : _ -> Prop)
  : iff (forall y : A, x = y -> P y) (P x).
  Proof. firstorder. Defined.

  (** These versions are around twice as fast as the [iff] versions... not sure why. *)
  Definition remove_forall_eql A x (P : _ -> Prop)
  : flip impl (forall y : A, y = x -> P y) (P x)
    := proj2 (@iff_remove_forall_eql A x P).

  Definition remove_forall_eql' A x (P : _ -> Prop)
  : impl (forall y : A, y = x -> P y) (P x)
    := proj1 (@iff_remove_forall_eql A x P).

  Definition remove_forall_eqr A x (P : _ -> Prop)
  : flip impl (forall y : A, x = y -> P y) (P x)
    := proj2 (@iff_remove_forall_eqr A x P).

  Definition remove_forall_eqr' A x (P : _ -> Prop)
  : impl (forall y : A, x = y -> P y) (P x)
    := proj1 (@iff_remove_forall_eqr A x P).

  Section and.
    (** Variants for equalities with /\  *)
    Definition iff_remove_forall_eql_and A x (P : _ -> Prop) (Q : A -> Prop)
    : iff (forall y : A, (y = x /\ Q y) -> P y) (Q x -> P x).
    Proof. firstorder. Qed.

    Definition iff_remove_forall_eqr_and A x (P : _ -> Prop) (Q : A -> Prop)
    : iff (forall y : A, (x = y /\ Q y) -> P y) (Q x -> P x).
    Proof. firstorder. Qed.

    Definition iff_remove_forall_and_eql A x (P : _ -> Prop) (Q : A -> Prop)
    : iff (forall y : A, (Q y /\ y = x) -> P y) (Q x -> P x).
    Proof. firstorder. Qed.

    Definition iff_remove_forall_and_eqr A x (P : _ -> Prop) (Q : A -> Prop)
    : iff (forall y : A, (Q y /\ x = y) -> P y) (Q x -> P x).
    Proof. firstorder. Qed.

    Definition remove_forall_eql_and A x (P : _ -> Prop) (Q : A -> Prop)
    : flip impl (forall y : A, (y = x /\ Q y) -> P y) (Q x -> P x)
      := proj2 (@iff_remove_forall_eql_and A x P Q).

    Definition remove_forall_eql_and' A x (P : _ -> Prop) (Q : A -> Prop)
    : impl (forall y : A, (y = x /\ Q y) -> P y) (Q x -> P x)
      := proj1 (@iff_remove_forall_eql_and A x P Q).

    Definition remove_forall_eqr_and A x (P : _ -> Prop) (Q : A -> Prop)
    : flip impl (forall y : A, (x = y /\ Q y) -> P y) (Q x -> P x)
      := proj2 (@iff_remove_forall_eqr_and A x P Q).

    Definition remove_forall_eqr_and' A x (P : _ -> Prop) (Q : A -> Prop)
    : impl (forall y : A, (x = y /\ Q y) -> P y) (Q x -> P x)
      := proj1 (@iff_remove_forall_eqr_and A x P Q).

    Definition remove_forall_and_eql A x (P : _ -> Prop) (Q : A -> Prop)
    : flip impl (forall y : A, (Q y /\ y = x) -> P y) (Q x -> P x)
      := proj2 (@iff_remove_forall_and_eql A x P Q).

    Definition remove_forall_and_eql' A x (P : _ -> Prop) (Q : A -> Prop)
    : impl (forall y : A, (Q y /\ y = x) -> P y) (Q x -> P x)
      := proj1 (@iff_remove_forall_and_eql A x P Q).

    Definition remove_forall_and_eqr A x (P : _ -> Prop) (Q : A -> Prop)
    : flip impl (forall y : A, (Q y /\ x = y) -> P y) (Q x -> P x)
      := proj2 (@iff_remove_forall_and_eqr A x P Q).

    Definition remove_forall_and_eqr' A x (P : _ -> Prop) (Q : A -> Prop)
    : impl (forall y : A, (Q y /\ x = y) -> P y) (Q x -> P x)
      := proj1 (@iff_remove_forall_and_eqr A x P Q).
  End and.
End forall_eq.

Section exists_and_eq.
  (** And now with [exists] *)
  Definition iff_remove_exists_and_eql A x (P : _ -> Prop)
  : iff (exists y : A, P y /\ y = x) (P x).
  Proof. firstorder. Qed.

  Definition iff_remove_exists_and_eqr A x (P : _ -> Prop)
  : iff (exists y : A, P y /\ x = y) (P x).
  Proof. firstorder. Defined.

  Definition iff_remove_exists_eql_and A x (P : _ -> Prop)
  : iff (exists y : A, y = x /\ P y) (P x).
  Proof. firstorder. Qed.

  Definition iff_remove_exists_eqr_and A x (P : _ -> Prop)
  : iff (exists y : A, x = y /\ P y) (P x).
  Proof. firstorder. Defined.

  (** These versions are around twice as fast as the [iff] versions... not sure why. *)
  Definition remove_exists_and_eql A x (P : _ -> Prop)
  : flip impl (exists y : A, P y /\ y = x) (P x)
    := proj2 (@iff_remove_exists_and_eql A x P).

  Definition remove_exists_and_eql' A x (P : _ -> Prop)
  : impl (exists y : A, P y /\ y = x) (P x)
    := proj1 (@iff_remove_exists_and_eql A x P).

  Definition remove_exists_and_eqr A x (P : _ -> Prop)
  : flip impl (exists y : A, P y /\ x = y) (P x)
    := proj2 (@iff_remove_exists_and_eqr A x P).

  Definition remove_exists_and_eqr' A x (P : _ -> Prop)
  : impl (exists y : A, P y /\ x = y) (P x)
    := proj1 (@iff_remove_exists_and_eqr A x P).

  Definition remove_exists_eql_and A x (P : _ -> Prop)
  : flip impl (exists y : A, y = x /\ P y) (P x)
    := proj2 (@iff_remove_exists_eql_and A x P).

  Definition remove_exists_eql_and' A x (P : _ -> Prop)
  : impl (exists y : A, y = x /\ P y) (P x)
    := proj1 (@iff_remove_exists_eql_and A x P).

  Definition remove_exists_eqr_and A x (P : _ -> Prop)
  : flip impl (exists y : A, x = y /\ P y) (P x)
    := proj2 (@iff_remove_exists_eqr_and A x P).

  Definition remove_exists_eqr_and' A x (P : _ -> Prop)
  : impl (exists y : A, x = y /\ P y) (P x)
    := proj1 (@iff_remove_exists_eqr_and A x P).
End exists_and_eq.

Lemma forall_sig_prop A P (Q : _ -> Prop)
: (forall x : @sig A P, Q x) <-> (forall x y, Q (exist P x y)).
Proof. firstorder. Defined.

Lemma forall_commute A P Q (R : forall x : A, P x -> Q x -> Prop)
: (forall x y z, R x y z) <-> (forall x z y, R x y z).
Proof. firstorder. Defined.

Lemma flip_a_impl_b_impl_a (A : Prop) B : flip impl (B -> A) A.
Proof. firstorder. Defined.

Lemma exists_sig A P Q
: (exists x : @sig A P, Q x) <-> (exists x y, Q (exist P x y)).
Proof. firstorder eauto. Defined.

Lemma exists_and_comm A B Q
: (exists x : A, B /\ Q x) <-> (B /\ exists x : A, Q x).
Proof. firstorder. Defined.

Lemma exists_and_assoc A B Q
: (exists x : A, (Q x /\ B)) <-> ((exists x : A, Q x) /\ B).
Proof. firstorder. Defined.

Lemma impl_exists A P Q (H : exists x : A, impl Q (P x))
: impl Q (exists x : A, P x).
Proof. firstorder. Defined.

Hint Resolve impl_exists : typeclass_instances.
