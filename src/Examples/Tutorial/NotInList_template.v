Require Import Tutorial.


(* A specification of what it means to choose a number that is not in a particular list *)
Definition notInList (ls : list nat) :=
  {n : nat | ~In n ls}%comp.

(* A simple traversal will find the maximum list element, which is a good upper bound. *)
Definition listMax := fold_right max 0.

(* ...and we can prove it! *)
Theorem listMax_upperBound : forall init ls,
  forall n, In n ls -> fold_right max init ls >= n.
Proof.
  induction ls; simpl; intuition.
  arithmetic.
  apply IHls in H0.
  arithmetic.
Qed.

(* Let's derive an efficient implementation. *)
Theorem implementation : { f : list nat -> Comp nat | forall ls, refine (notInList ls) (f ls) }.
Proof.
  begin.
Admitted.

(* We can extract the program that we found as a standlone, executable Gallina term. *)
Definition impl := Eval simpl in projT1 implementation.
Print impl.

Eval compute in impl (1 :: 7 :: 8 :: 2 :: 13 :: 6 :: nil).
