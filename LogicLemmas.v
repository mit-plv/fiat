Require Import Program.
Require Import Common.
(** * Various useful lemmas about logic *)

(** We prove things here mainly for the purpose of [setoid_rewrite]ing with instances of [impl] and [iff]. *)

Local Arguments impl / .
Local Arguments flip / .
Local Arguments pointwise_relation / .

Local Hint Extern 1 => progress simpl in *.
Local Hint Extern 0 => progress subst.
Local Hint Extern 1 => progress destruct_head_hnf sig.

(** We prove some lemmas about [forall], for the benefit of setoid rewriting. *)
Definition remove_forall_eq A x B (P : A -> B -> Prop)
: pointwise_relation _ iff (fun z => forall y : A, y = x -> P y z) (P x).
Proof. firstorder. Defined.

Definition remove_forall_eq' A x B (P : A -> B -> Prop)
: pointwise_relation _ iff (fun z => forall y : A, x = y -> P y z) (P x).
Proof. firstorder. Defined.


(** These versions are around twice as fast as the [iff] versions... not sure why. *)
Definition remove_forall_eq0 A x B (P : A -> B -> Prop)
: pointwise_relation _ (flip impl) (fun z => forall y : A, y = x -> P y z) (P x).
Proof. firstorder. Defined.

Definition remove_forall_eq1 A x B (P : A -> B -> Prop)
: pointwise_relation _ impl (fun z => forall y : A, y = x -> P y z) (P x).
Proof. firstorder. Defined.

Definition remove_forall_eq0' A x B (P : A -> B -> Prop)
: pointwise_relation _ (flip impl) (fun z => forall y : A, x = y -> P y z) (P x).
Proof. firstorder. Defined.

Definition remove_forall_eq1' A x B (P : A -> B -> Prop)
: pointwise_relation _ impl (fun z => forall y : A, x = y -> P y z) (P x).
Proof. firstorder. Defined.

(** And now with [exists] *)
Definition remove_exists_and_eq A B x (P : A -> B -> Prop)
: pointwise_relation _ iff (fun z => exists y : A, P y z /\ y = x z) (fun z => P (x z) z).
Proof. firstorder. Defined.

Definition remove_exists_and_eq' A B x (P : A -> B -> Prop)
: pointwise_relation _ iff (fun z => exists y : A, P y z /\ x z = y) (fun z => P (x z) z).
Proof. firstorder. Defined.


(** These versions are around twice as fast as the [iff] versions... not sure why. *)
Definition remove_exists_and_eq0 A B x (P : A -> B -> Prop)
: pointwise_relation _ (flip impl) (fun z => exists y : A, P y z /\ y = x z) (fun z => P (x z) z).
Proof. firstorder. Defined.

Definition remove_exists_and_eq1 A B x (P : A -> B -> Prop)
: pointwise_relation _ impl (fun z => exists y : A, P y z /\ y = x z) (fun z => P (x z) z).
Proof. firstorder. Defined.

Definition remove_exists_and_eq0' A B x (P : A -> B -> Prop)
: pointwise_relation _ (flip impl) (fun z => exists y : A, P y z /\ x z = y) (fun z => P (x z) z).
Proof. firstorder. Defined.

Definition remove_exists_and_eq1' A B x (P : A -> B -> Prop)
: pointwise_relation _ impl (fun z => exists y : A, P y z /\ x z = y) (fun z => P (x z) z).
Proof. firstorder. Defined.

Lemma forall_sig_prop A P (Q : _ -> Prop) : (forall x : @sig A P, Q x) <-> (forall x y, Q (exist P x y)).
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
