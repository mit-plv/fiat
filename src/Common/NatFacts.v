Require Import Coq.omega.Omega.

Section NatFacts.
  Lemma le_r_le_max :
    forall x y z,
      x <= z -> x <= max y z.
  Proof.
    intros x y z;
    destruct (Max.max_spec y z) as [ (comp, eq) | (comp, eq) ];
    rewrite eq;
    omega.
  Qed.

  Lemma le_l_le_max :
    forall x y z,
      x <= y -> x <= max y z.
  Proof.
    intros x y z.
    rewrite Max.max_comm.
    apply le_r_le_max.
  Qed.

  Lemma le_neq_impl :
    forall m n, m < n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma gt_neq_impl :
    forall m n, m > n -> m <> n.
  Proof.
    intros; omega.
  Qed.

  Lemma lt_refl_False :
    forall x,
      lt x x -> False.
  Proof.
    intros; omega.
  Qed.

  Lemma beq_nat_eq_nat_dec :
    forall x y,
      beq_nat x y = if eq_nat_dec x y then true else false.
  Proof.
    intros; destruct (eq_nat_dec _ _); [ apply beq_nat_true_iff | apply beq_nat_false_iff ]; assumption.
  Qed.
End NatFacts.

Fixpoint minusr (n m : nat) {struct m} : nat
  := match m with
       | 0 => n
       | S l => minusr (pred n) l
     end.

Lemma minusr_minus n m
: minusr n m = minus n m.
Proof.
  revert m; induction n; simpl;
  induction m; simpl; auto.
Qed.

Delimit Scope natr_scope with natr.
Infix "-" := minusr : natr_scope.

Module minusr_notation.
  Infix "-" := minusr : nat_scope.
End minusr_notation.
