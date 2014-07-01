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

Definition HasDecidableEquality (T: Type) :=
  forall (x y: T), {x = y} + {x <> y}.

Definition _BagInsertCount
           {TContainer TItem}
           (benumerate : TContainer -> list TItem)
           (binsert    : TContainer -> TItem -> TContainer)
           (bcount     : HasDecidableEquality TItem -> TContainer -> TItem -> nat) :=
  forall (beq : HasDecidableEquality TItem),
  forall item inserted container,
    bcount beq (binsert container inserted) item =
    bcount beq container item + if beq item inserted then 1 else 0.

Definition _BagCountEmpty
           {TContainer TItem: Type}
           (benumerate : TContainer -> list TItem)
           (bempty     : TContainer)
           (bcount     : HasDecidableEquality TItem -> TContainer -> TItem -> nat) :=
  forall (beq : HasDecidableEquality TItem),
  forall item, bcount beq bempty item = 0. 

Definition _bcount {TContainer TItem TSearchTerm} (bag: Bag TContainer TItem TSearchTerm) 
           (dec: HasDecidableEquality TItem) container item :=
  List.length (List.filter (fun x => if dec item x then true else false) (benumerate container)). 

Lemma _bcount_empty {TContainer TItem TSearchTerm} :
  forall (bag: Bag TContainer TItem TSearchTerm),
    @_BagCountEmpty TContainer TItem benumerate bempty (_bcount bag).
Proof.
  unfold _BagCountEmpty, _bcount; intros;
  rewrite benumerate_empty_eq_nil; simpl; trivial.
Qed.

Lemma _binsert_count {TContainer TItem TSearchTerm} :
  forall (bag: Bag TContainer TItem TSearchTerm),
    @_BagInsertCount TContainer TItem benumerate binsert (_bcount bag).
Proof.
  unfold _BagInsertCount, _bcount; intros;
  rewrite binsert_enumerate; simpl; destruct (beq item inserted); simpl; omega.
Qed.
