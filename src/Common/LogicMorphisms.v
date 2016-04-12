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
