Require Import Coq.omega.Omega.

Hint Rewrite <- nat_compare_lt : hints.
Hint Rewrite <- nat_compare_gt : hints.
Hint Rewrite nat_compare_eq_iff : hints.
Hint Rewrite <- nat_compare_eq_iff : hints.

Ltac autorewrite_nat_compare :=
  autorewrite with hints.

Lemma nat_compare_eq_refl : forall x, nat_compare x x = Eq.
  intros; apply nat_compare_eq_iff; trivial.
Qed.

Lemma nat_compare_consistent :
  forall n0 n1,
    { nat_compare n0 n1 = Lt /\ nat_compare n1 n0 = Gt }
    + { nat_compare n0 n1 = Eq /\ nat_compare n1 n0 = Eq }
    + { nat_compare n0 n1 = Gt /\ nat_compare n1 n0 = Lt }.
Proof.
  intros n0 n1;
  destruct (lt_eq_lt_dec n0 n1) as [ [_lt | _eq] | _lt ];
  [ constructor 1; constructor 1  | constructor 1; constructor 2 | constructor 2 ];
  split;
  autorewrite_nat_compare;
  intuition.
Qed.
