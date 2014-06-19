Require Import BagsInterface AdditionalLemmas.
Require Import AdditionalMorphisms.

Lemma binsert_enumerate_weak {TContainer TItem TSearchTerm} {bag: Bag TContainer TItem TSearchTerm}:
  forall item inserted container,
    List.In item (benumerate (binsert container inserted)) <->
    List.In item (benumerate container) \/ item = inserted.
Proof.
  intros.
  rewrite <- refold_in.
  apply in_permutation_morphism; eauto using binsert_enumerate. 
Qed.

Lemma benumerate_empty_eq_nil {TContainer TItem TSearchTerm} (bag: Bag TContainer TItem TSearchTerm):
  (benumerate bempty) = nil. 
Proof.
  pose proof (benumerate_empty) as not_in;
  unfold BagEnumerateEmpty in not_in.
  destruct (benumerate bempty) as [ | item ? ]; 
    simpl in *;
    [ | exfalso; apply (not_in item) ];
    eauto.
Qed.

Lemma binsert_enumerate_length :
  forall {TItem TContainer TSearchTerm} {bag_proof: Bag TContainer TItem TSearchTerm},
  forall (bag: TContainer) (item: TItem),
    List.length (benumerate (binsert bag item)) = S (List.length (benumerate bag)).
Proof.      
  intros; rewrite binsert_enumerate; simpl; trivial.
Qed.
