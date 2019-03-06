Require Import Tutorial.


(* A specification of what it means to choose a number that is not in a particular list *)
Definition notInList (ls : list nat) :=
  {n : nat | ~In n ls}%comp.

Theorem notInList_decompose : forall ls,
  refine (notInList ls) (upper <- {upper | forall n, In n ls -> upper >= n};
                         {beyond | beyond > upper}).
Proof.
  refines.
  firstorder.
Qed.

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

Theorem listMax_refines : forall ls,
  refine {upper | forall n, In n ls -> upper >= n} (ret (listMax ls)).
Proof.
  refines.
  apply listMax_upperBound.
Qed.

Theorem increment_refines : forall n,
  refine {higher | higher > n} (ret (n + 1)).
Proof.
  refines.
  arithmetic.
Qed.

(* Let's derive an efficient implementation. *)
Theorem implementation : { f : list nat -> Comp nat | forall ls, refine (notInList ls) (f ls) }.
Proof.
  begin.
  rewrite notInList_decompose.
  rewrite listMax_refines.
  setoid_rewrite increment_refines.
  monad_simpl.
  finish honing.
Defined.

(* We can extract the program that we found as a standlone, executable Gallina term. *)
Definition impl := Eval simpl in proj1_sig implementation.
Print impl.

Eval compute in impl (1 :: 7 :: 8 :: 2 :: 13 :: 6 :: nil).
