Set Implicit Arguments.

Require Import Coq.Arith.Arith.
Require Import Coq.omega.Omega.

Lemma plus_eq_right_0 : forall a b, a + b = b -> a = 0.
  induction a; simpl; intuition.
Qed.
