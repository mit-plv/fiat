Require Export IndexedEnsembles.
Require Import Ensembles List AdditionalPermutationLemmas.

Lemma EnsembleListEquivalence_slice :
  forall {A} a b c (ens: Ensemble A),
    EnsembleListEquivalence ens (a ++ b ++ c) ->
    EnsembleListEquivalence (fun x => ens x /\ ~ List.In x b) (a ++ c).
Proof.
  unfold EnsembleListEquivalence, Ensembles.In; simpl;
  repeat setoid_rewrite in_app_iff; intros *.
  split.
  - intros. intuition.
    eauto using NoDup_slice.
  - intros; intuition.
    + rewrite H1 in H2; intuition.
    + rewrite H1; intuition.
    + eapply NoDup_app_inv'; eauto.
    + rewrite H1; intuition.
    + eapply NoDup_app_inv'; eauto.
Qed.


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
