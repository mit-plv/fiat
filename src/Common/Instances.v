Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.RelationClasses Coq.Program.Basics.

Global Instance arrow2_1_Proper {A B RA RB X Y}
       {H0 : Proper (RA ==> RB ==> flip impl) (fun (a : A) (b : B) => X a b)}
       {H1 : Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => Y a b)}
: Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => X a b -> Y a b) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow2_2_Proper {A B RA RB X} {Y : A -> B -> Type} {Z : A -> B -> Prop}
       {H0 : Proper (RA ==> RB ==> flip impl) (fun (a : A) (b : B) => X a b)}
       {H1 : Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => Y a b -> Z a b)}
: Proper (RA ==> RB ==> impl) (fun (a : A) (b : B) => X a b -> Y a b -> Z a b) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_1_Proper {A B C RA RB RC X Y}
       {H0 : Proper (RA ==> RB ==> RC ==> flip impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> impl) Y}
: Proper (RA ==> RB ==> RC ==> impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_2_Proper {A B C RA RB RC X} {Y : A -> B -> C -> Type} {Z : A -> B -> C -> Prop}
       {H0 : Proper (RA ==> RB ==> RC ==> flip impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> impl) (fun (a : A) (b : B) (c : C) => Y a b c -> Z a b c)}
: Proper (RA ==> RB ==> RC ==> impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c -> Z a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_1_Proper_flip {A B C RA RB RC X Y}
       {H0 : Proper (RA ==> RB ==> RC ==> impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> flip impl) Y}
: Proper (RA ==> RB ==> RC ==> flip impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance arrow3_2_Proper_flip {A B C RA RB RC X} {Y : A -> B -> C -> Type} {Z : A -> B -> C -> Prop}
       {H0 : Proper (RA ==> RB ==> RC ==> impl) X}
       {H1 : Proper (RA ==> RB ==> RC ==> flip impl) (fun (a : A) (b : B) (c : C) => Y a b c -> Z a b c)}
: Proper (RA ==> RB ==> RC ==> flip impl) (fun (a : A) (b : B) (c : C) => X a b c -> Y a b c -> Z a b c) | 100.
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance flip_impl_reflexive {A} {f}
: Reflexive (fun x y : A => flip impl (f x) (f y)) | 1.
Proof.
  repeat intro; assumption.
Defined.
Global Instance split_cons_drop_1_Proper {T} {R : relation T}
       {A RA RLA RLA' B C RB RC} {f}
       {H0 : Proper (RA ==> RLA ==> RLA') (@Datatypes.cons _)}
       {H1 : Proper (RB ==> RLA' ==> R) f}
: Proper (RA ==> RLA ==> RB ==> RC ==> R)
         (fun (a : A) (la : list A) (b : B) (_ : C) => f b (@Datatypes.cons _ a la)).
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Qed.
Global Instance drop_4_Proper {T} {R : relation T}
       {A B C D RA RB RC RD f}
       {H0 : @Reflexive D RD}
       {H1 : Proper (RA ==> RB ==> RC ==> R) f}
: Proper (RA ==> RB ==> RC ==> RD ==> R) (fun (a : A) (b : B) (c : C) (_ : D) => f a b c).
Proof.
  unfold Proper, impl, flip, respectful in *; eauto with nocore.
Defined.
Global Instance drop_0_Proper {A B RA RB} {f : B}
       {H : Proper RB f}
: Proper (RA ==> RB) (fun _ : A => f).
Proof.
  lazy in H |- *; eauto with nocore.
Defined.
Global Instance idmap_Proper {A} {R : relation A}
: Proper (R ==> R) (fun x : A => x).
Proof.
  lazy; trivial.
Defined.
Global Instance forall_fun3_Proper {A X Y Z RX RY RZ} {B : _ -> _ -> _ -> _ -> Prop}
       {H : forall a, Proper (RX ==> RY ==> RZ ==> flip impl) (B a)}
: Proper (RX ==> RY ==> RZ ==> flip impl) (fun (x : X) (y : Y) (z : Z) => forall a : A, B a x y z) | 1000.
Proof.
  lazy in H |- *; eauto with nocore.
Defined.

Local Ltac equiv_t :=
  unfold pointwise_relation;
  let H := fresh in
  intros ?? H; split; intro; try split; repeat intro;
  try apply H;
  try reflexivity;
  try (symmetry; apply H; assumption);
  try (etransitivity; apply H; eassumption);
  try (apply antisymmetry; apply H; assumption);
  try (eapply asymmetry; apply H; eassumption).

Global Instance Reflexive_Proper {T}
  : Proper (pointwise_relation T (pointwise_relation T iff) ==> iff) Reflexive.
Proof. equiv_t. Qed.

Global Instance Symmetric_Proper {T}
  : Proper (pointwise_relation T (pointwise_relation T iff) ==> iff) Symmetric.
Proof. equiv_t. Qed.

Global Instance Transitive_Proper {T}
  : Proper (pointwise_relation T (pointwise_relation T iff) ==> iff) Transitive.
Proof. equiv_t. Qed.

Global Instance Equivalence_Proper {T}
  : Proper (pointwise_relation T (pointwise_relation T iff) ==> iff) Equivalence.
Proof. equiv_t. Qed.

Global Instance Antisymmetric_Proper {A eqA eqvA}
  : Proper (pointwise_relation _ (pointwise_relation _ iff) ==> iff) (@Antisymmetric A eqA eqvA).
Proof. equiv_t. Qed.

Global Instance Asymmetric_Proper {T}
  : Proper (pointwise_relation T (pointwise_relation _ iff) ==> iff) Asymmetric.
Proof. equiv_t. Qed.

Global Instance is_true_Proper_eq: Proper (Logic.eq ==> Logic.eq) is_true := _.
Global Instance negb_Proper_eq: Proper (Logic.eq ==> Logic.eq) negb := _.
Global Instance and_Proper_eq: Proper (Logic.eq ==> Logic.eq ==> Logic.eq) and := _.

Global Instance eq_flip_impl_flip_impl_impl_Prper
  : Proper (Logic.eq ==> Basics.flip Basics.impl ==> Basics.flip Basics.impl) Basics.impl.
Proof. compute; intros; subst; tauto. Qed.

Global Instance and_flip_impl_iff_Proper
  : Proper (flip impl ==> iff ==> flip impl) and | 5.
Proof. compute; tauto. Qed.
Global Instance and_iff_eq_iff_Proper : Proper (iff ==> Logic.eq ==> iff) and | 4.
Proof. compute; intros; subst; tauto. Qed.
Global Instance and_iff_iff_iff_Proper : Proper (iff ==> iff ==> iff) and | 1
  := _.
Global Instance impl_iff_iff_flip_impl_Proper : Proper (iff ==> iff ==> flip impl) impl | 2.
Proof. compute; tauto. Qed.
Global Instance impl_iff_iff_iff_Proper : Proper (iff ==> iff ==> iff) impl | 1.
Proof. compute; tauto. Qed.

Global Instance impl_eq_eq_eq_Proper : Proper (eq ==> eq ==> eq) impl | 0 := _.
Global Instance all_pointwise_eq_iff_Proper A : Proper (pointwise_relation A eq ==> iff) (all (A:=A)) | 2.
Proof.
  compute; intros ?? H'.
  split; intros H'' x';
    first [ rewrite H' | rewrite <- H' ]; auto.
Qed.

Global Existing Instance eq_Reflexive.

Lemma Equivalence_flip {A R} (H : @Equivalence A R) : Equivalence (flip R).
Proof. split; exact _. Qed.

Hint Extern 0 (Equivalence (flip _)) => apply Equivalence_flip : typeclass_instances.
