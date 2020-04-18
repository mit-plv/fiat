Require Import Coq.omega.Omega.

Require Import Bedrock.Examples.PreAutoSep.


(** Let's put the lemma prover through its paces. *)

Hint Extern 1 => elimtype False; omega : contradiction.

Theorem t0 : forall a b, a =*> b ===> a =*> b.
  sepLemma.
Qed.

Theorem t1 : forall a b c d, a =*> b * c =*> d ===> c =*> d * a =*> b.
  sepLemma.
Qed.

Theorem t2 : forall P : nat -> Prop, (Ex x, [| P x |]) ===> Ex x, [| P x |].
  sepLemma; eauto.
Qed.

Theorem t3 : forall ls : list nat, [| (length ls > 0)%nat |] ===> Ex x, Ex ls', [| ls = x :: ls' |].
  destruct ls; sepLemma.
Qed.

Theorem t4 : forall A (R : A -> A -> Prop),
  (Ex x, Ex y, Ex z, [| R x y /\ R y z |]) ===> (Ex y, ((Ex x, [| R x y |]) * (Ex z, [| R y z |]))).
  sepLemma.
  apply H.
  eassumption.
Qed.

(** Unification **)
Theorem t5 : forall p1 P2 V, exists p2, exists v,
  (p1 =*> P2 * P2 =*> V) ===> (p1 =*> p2 * p2 =*> v).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t6 : forall p1 P2 V, exists p2, exists v,
  (P2 =*> V * p1 =*> P2) ===> (p1 =*> p2 * p2 =*> v).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t7 : forall p1 P2 V, exists p2, exists v,
  (p1 =*> P2 * P2 =*> V) ===> (p2 =*> v * p1 =*> p2).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t8 : forall p1 P2 V, exists p2, exists v,
  (P2 =*> V * p1 =*> P2) ===> (p2 =*> v * p1 =*> p2).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t_err : forall a b c d, a =*> c * b =*> d ===> a =*> b * c =*> d.
  intros.
  progress sep_canceller ltac:ILTacCommon.isConst auto_ext ltac:(hints_ext_simplifier auto_ext).
  (progress sep_canceller ltac:ILTacCommon.isConst auto_ext ltac:(hints_ext_simplifier auto_ext); fail 3) || idtac.
Abort.
