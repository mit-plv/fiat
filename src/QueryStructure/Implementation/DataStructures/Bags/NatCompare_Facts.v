Require Import Coq.ZArith.ZArith.
Require Export Fiat.Common.Coq__8_4__8_5__Compat.

#[global]
Hint Rewrite <- nat_compare_lt : hints.
#[global]
Hint Rewrite <- nat_compare_gt : hints.
#[global]
Hint Rewrite Nat.compare_eq_iff : hints.
#[global]
Hint Rewrite <- Nat.compare_eq_iff : hints.

Ltac autorewrite_nat_compare :=
  autorewrite with hints.

Lemma nat_compare_eq_refl : forall x, Nat.compare x x = Eq.
  intros; apply Nat.compare_eq_iff; trivial.
Qed.

Lemma nat_compare_consistent :
  forall n0 n1,
    { Nat.compare n0 n1 = Lt /\ Nat.compare n1 n0 = Gt }
    + { Nat.compare n0 n1 = Eq /\ Nat.compare n1 n0 = Eq }
    + { Nat.compare n0 n1 = Gt /\ Nat.compare n1 n0 = Lt }.
Proof.
  intros n0 n1;
  destruct (lt_eq_lt_dec n0 n1) as [ [_lt | _eq] | _lt ];
  [ constructor 1; constructor 1  | constructor 1; constructor 2 | constructor 2 ];
  split;
  autorewrite_nat_compare;
  intuition.
Qed.
