Require Import Ensembles List.

Definition EnsembleListEquivalence {A: Type} (ensemble: A -> Prop) (seq: list A) :=
  NoDup seq /\
  forall x, Ensembles.In _ ensemble x <-> List.In x seq.

Lemma ensemble_list_equivalence_set_eq_morphism {A : Type} {ens1 ens2 : A -> Prop} :
  (forall x, Ensembles.In _ ens1 x <-> Ensembles.In _ ens2 x) ->
  forall (seq : list A),
    (EnsembleListEquivalence ens1 seq <-> EnsembleListEquivalence ens2 seq).
Proof.
  intros * equiv *;
  unfold EnsembleListEquivalence, In in *;
  setoid_rewrite equiv; reflexivity.
Qed.

Lemma EnsembleListEquivalence_lift_property {TItem: Type} {P: TItem -> Prop} :
  forall (sequence: list TItem) (ensemble: TItem -> Prop),
    EnsembleListEquivalence ensemble sequence ->
    ((forall item,
        List.In item sequence -> P item) <->
     (forall item,
        Ensembles.In _ ensemble item -> P item)).
Proof.
  intros * equiv;
  destruct equiv as [NoDup_l equiv];
  setoid_rewrite equiv;
  reflexivity.
Qed.
