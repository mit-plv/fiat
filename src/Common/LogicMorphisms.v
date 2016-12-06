Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Program.Basics.

Local Coercion is_true : bool >-> Sortclass.

Add Parametric Morphism {A: Type} :
  (fun (P: A -> Prop) => exists x, P x)
    with signature (pointwise_relation A iff ==> iff)
      as exists_eq_iff_morphism.
Proof.
  intros * equiv;
  split; intro H; destruct H as [x0 H']; exists x0;
  apply equiv in H'; assumption.
Qed.

Lemma impl_iff_Proper
: Proper (iff ==> iff ==> iff) impl.
Proof. lazy; tauto. Qed.
Lemma impl_impl_Proper
: Proper (Basics.flip impl ==> impl ==> impl) impl.
Proof. lazy; tauto. Qed.
Lemma ex_iff_Proper {A}
: Proper (pointwise_relation _ iff ==> iff) (@ex A).
Proof.
  lazy.
  intros ?? H;
    repeat (intros [] || intro || esplit);
    apply H; eassumption.
Defined.
Lemma ex_impl_Proper {A}
: Proper (pointwise_relation _ impl ==> impl) (@ex A).
Proof.
  lazy.
  intros ?? H;
    repeat (intros [] || intro || esplit);
    apply H; eassumption.
Defined.
Lemma and_iff_Proper
: Proper (iff ==> iff ==> iff) and.
Proof. lazy; tauto. Qed.
Lemma and_impl_Proper
: Proper (impl ==> impl ==> impl) and.
Proof. lazy; tauto. Qed.
Global Instance and_flip_impl_Proper
: Proper (flip impl ==> flip impl ==> flip impl) and.
Proof. lazy; tauto. Qed.
Global Instance pair_Proper {A B}
  : Proper (eq ==> eq ==> eq) (@pair A B).
Proof.
  lazy; intros; congruence.
Qed.
Global Instance andb_implb_Proper
  : Proper (flip implb ==> flip implb ==> flip implb) andb.
Proof.
  unfold flip, implb, andb.
  intros [] [] ? [] [] ?; trivial.
Qed.

Global Instance or_iff_iff_impl_Proper : Proper (iff ==> iff ==> impl) or | 2.
Proof. lazy; tauto. Qed.
Global Instance and_iff_iff_impl_Proper : Proper (iff ==> iff ==> impl) and | 2.
Proof. lazy; tauto. Qed.

Class pull_forall_able (iffR : Prop -> Prop -> Prop)
  := pull_forall_iffR : forall A P Q, (forall x : A, iffR (P x) (Q x)) -> iffR (forall x, P x) (forall x, Q x).
Global Instance pull_forall_able_iff : pull_forall_able iff.
Proof. compute; firstorder. Qed.
Global Instance pull_forall_able_impl : pull_forall_able impl.
Proof. compute; firstorder. Qed.
Global Instance pull_forall_able_flip_impl : pull_forall_able (flip impl).
Proof. compute; firstorder. Qed.

Global Instance iff_Proper_iff_iff_flip_impl : Proper (iff ==> iff ==> flip impl) iff | 2.
Proof. compute; firstorder. Qed.
Global Instance iff_Proper_iff_iff_impl : Proper (iff ==> iff ==> impl) iff | 2.
Proof. compute; firstorder. Qed.
Global Instance iff_Proper_iff_iff_iff : Proper (iff ==> iff ==> iff) iff | 2 := _.

Global Instance impl_Proper_iff_iff_flip_impl : Proper (iff ==> iff ==> flip impl) impl | 2.
Proof. compute; firstorder. Qed.
Global Instance impl_Proper_iff_iff_impl : Proper (iff ==> iff ==> impl) impl | 2.
Proof. compute; firstorder. Qed.
Global Instance impl_Proper_iff_iff_iff : Proper (iff ==> iff ==> iff) impl | 2 := _.

Global Instance flip_impl_Proper_iff_iff_flip_impl : Proper (iff ==> iff ==> flip impl) (flip impl) | 2.
Proof. compute; firstorder. Qed.
Global Instance flip_impl_Proper_iff_iff_impl : Proper (iff ==> iff ==> impl) (flip impl) | 2.
Proof. compute; firstorder. Qed.
Global Instance flip_impl_Proper_iff_iff_iff : Proper (iff ==> iff ==> iff) (flip impl) | 2 := _.
