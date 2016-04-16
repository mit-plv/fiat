Require Import List.
Require Import CertifiedExtraction.Utils.
Require Import
        CertifiedExtraction.Extraction.QueryStructures.TupleToListW
        CertifiedExtraction.Extraction.QueryStructures.EnsemblesOfTuplesAndListW.
Require Import Fiat.ADT.Core.
Require Bedrock.Platform.Facade.examples.QsADTs.
Require Bedrock.Platform.Facade.examples.TuplesF.

Lemma EmptySet_False :
  forall {A} (x: A), Ensembles.Empty_set _ x <-> False.
Proof.
  firstorder.
Qed.

Ltac EnsembleIndexedListEquivalence_nil_t :=
  repeat match goal with
         | _ => cleanup
         | _ => solve [constructor]
         | _ => progress destruct_conjs
         | _ => progress unfold IndexedEnsembles.EnsembleIndexedListEquivalence,
                IndexedEnsembles.UnIndexedEnsembleListEquivalence,
                TuplesF.EnsembleIndexedListEquivalence,
                TuplesF.UnIndexedEnsembleListEquivalence,
                IndexedEnsemble_TupleToListW,
                Ensembles.Same_set, Ensembles.Included, Ensembles.In in *
         | [  |- exists (_: list ?t), _ ] => exists (@nil t)
         | [ H: map _ _ = nil |- _ ] => apply map_eq_nil in H
         | [ H: context[In _ nil] |- _ ] =>
           setoid_rewrite (fun A a => (fun A => proj1 (neg_false A)) _ (@in_nil A a)) in H
         | [  |- context[Ensembles.Empty_set _ _] ] => setoid_rewrite EmptySet_False
         | [ H: context[Ensembles.Empty_set _ _] |- _ ] => setoid_rewrite EmptySet_False in H
         | _ => firstorder
         end.

Lemma IndexedEnsembles_UnIndexedEnsembleListEquivalence_nil :
  forall A ens, IndexedEnsembles.UnIndexedEnsembleListEquivalence ens (@nil A) <->
           Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

Lemma IndexedEnsembles_EnsembleIndexedListEquivalence_nil :
  forall A ens, IndexedEnsembles.EnsembleIndexedListEquivalence ens (@nil A) <->
           Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

Lemma TuplesF_UnIndexedEnsembleListEquivalence_nil :
  forall A ens, TuplesF.UnIndexedEnsembleListEquivalence ens (@nil A) <->
           Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.

Lemma TuplesF_EnsembleIndexedListEquivalence_nil :
  forall A ens,
    TuplesF.EnsembleIndexedListEquivalence ens (@nil A) <->
    Ensembles.Same_set _ ens (Ensembles.Empty_set _).
Proof.
  EnsembleIndexedListEquivalence_nil_t.
Qed.
