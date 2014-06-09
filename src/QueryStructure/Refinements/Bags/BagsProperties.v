Require Import BagsInterface AdditionalLemmas.

Lemma binsert_enumerate_SetEq {TContainer TItem TSearchTerm} (bag: Bag TContainer TItem TSearchTerm):
  forall inserted container,
    SetEq 
      (benumerate (binsert container inserted))
      (inserted :: (benumerate container)).
Proof.
  unfold SetEq; intros; simpl.
  setoid_rewrite or_comm; setoid_rewrite eq_sym_iff. 
  apply binsert_enumerate. 
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
