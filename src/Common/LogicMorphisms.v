Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.

Add Parametric Morphism {A: Type} :
  (fun (P: A -> Prop) => exists x, P x)
    with signature (pointwise_relation A iff ==> iff)
      as exists_eq_iff_morphism.
Proof.
  intros * equiv;
  split; intro H; destruct H as [x0 H']; exists x0;
  apply equiv in H'; assumption.
Qed.
