Require Import Coq.Sets.Ensembles.

Lemma weaken :
  forall {A: Type} ensemble condition,
  forall (x: A),
    Ensembles.In _ (fun x => Ensembles.In _ ensemble x /\ condition x) x
    -> Ensembles.In _ ensemble x.
Proof.
  unfold Ensembles.In; intros; intuition.
Qed.
