Require Import BagsInterface AdditionalLemmas.
Require Import AdditionalMorphisms.

Section BagsProperties.

  Context {TContainer   : Type}
          {TItem        : Type}
          {TSearchTerm  : Type}
          {TUpdateTerm  : Type}
          {bag          : Bag TContainer TItem TSearchTerm TUpdateTerm}.

  Lemma binsert_enumerate_weak
  : forall item inserted container,
      List.In item (benumerate (binsert container inserted)) <->
      List.In item (benumerate container) \/ item = inserted.
  Proof.
    intros.
    rewrite <- refold_in.
    apply in_permutation_morphism; eauto using binsert_enumerate.
  Qed.

  Lemma benumerate_empty_eq_nil
  : benumerate bempty = nil.
  Proof.
    pose proof (benumerate_empty) as not_in;
    unfold BagEnumerateEmpty in not_in.
    destruct (benumerate bempty) as [ | item ? ];
      simpl in *;
      [ | exfalso; apply (not_in item) ];
      eauto.
  Qed.

  Lemma binsert_enumerate_length
  : forall (bag: TContainer) (item: TItem),
      List.length (benumerate (binsert bag item)) = S (List.length (benumerate bag)).
  Proof.
    intros; rewrite binsert_enumerate; simpl; trivial.
  Qed.

  Definition _bcount container item :=
    List.length (List.filter (fun x => if bfind_matcher item x then true else false) (benumerate container)).

  Definition _BagInsertCount :=
    forall (search_term : TSearchTerm) (item : TItem) (container : TContainer),
      _bcount (binsert container item) search_term =
      _bcount container search_term + if bfind_matcher search_term item then 1 else 0.

  Definition _BagCountEmpty :=
    forall item, _bcount bempty item = 0.

  Lemma _bcount_empty :
      _BagCountEmpty.
  Proof.
    unfold _BagCountEmpty, _bcount; intros.
    rewrite benumerate_empty_eq_nil; simpl; trivial.
  Qed.

  Lemma _binsert_count : _BagInsertCount.
  Proof.
    unfold _BagInsertCount, _bcount; intros;
    rewrite binsert_enumerate; simpl; destruct (bfind_matcher search_term item); simpl; omega.
  Qed.

End BagsProperties.
