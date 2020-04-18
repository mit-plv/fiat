Require Import CertifiedExtraction.Utils.
Require Bedrock.Platform.Facade.examples.TuplesF.
Require Import List.

Require Import CertifiedExtraction.Extraction.QueryStructures.Basics.

Definition AllOfLength_set {A} N ens :=
  forall x, Ensembles.In _ ens x -> @List.length A (TuplesF.indexedElement x) = N.

Definition AllOfLength_list {A} N seq :=
  forall x, List.In x seq -> @List.length A x = N.

Lemma UnIndexedEnsembleListEquivalence_AllOfLength:
  forall (N : nat) A ens seq,
    @TuplesF.UnIndexedEnsembleListEquivalence (list A) ens seq ->
    AllOfLength_set N ens ->
    AllOfLength_list N seq.
Proof.
  repeat match goal with
         | _ => cleanup
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: exists _, _ |- _ ] => destruct H
         | [ H: In _ (map _ _) |- _ ] => rewrite in_map_iff in H
         | _ => progress unfold TuplesF.UnIndexedEnsembleListEquivalence,
                AllOfLength_set, AllOfLength_list in *
         end; firstorder.
Qed.

Lemma EnsembleIndexedListEquivalence_AllOfLength:
  forall (N : nat) A ens seq,
    @TuplesF.EnsembleIndexedListEquivalence (list A) ens seq ->
    AllOfLength_set N ens ->
    AllOfLength_list N seq.
Proof.
  unfold TuplesF.EnsembleIndexedListEquivalence; cleanup.
  intuition eauto using UnIndexedEnsembleListEquivalence_AllOfLength.
Qed.

Lemma keepEq_length {A B}:
  forall (N : nat) ens key k default (EQ: A -> B -> Prop),
    AllOfLength_set N ens ->
    AllOfLength_set N (TuplesF.keepEq EQ default ens key k).
Proof.
  unfold AllOfLength_set, TuplesF.keepEq, Ensembles.In; cleanup; intuition.
Qed.
