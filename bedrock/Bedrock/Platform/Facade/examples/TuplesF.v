(** Multisets of tuples *)
Require Import Coq.Sets.Ensembles.
Require Import Bedrock.Bedrock.
Require Import Coq.Relations.Relations.

(* This section copied from Fiat for convenience, to avoid circular dependencies across libraries! *)
Section IndexedEnsembles.
  Context {ElementType : Type}.

  Record IndexedElement :=
    { elementIndex : nat;
      indexedElement : ElementType }.

  Definition IndexedEnsemble := Ensemble IndexedElement.

  Definition IndexedEnsemble_In
             (ensemble : IndexedEnsemble)
             (item : ElementType) :=
    exists idx, Ensembles.In _ ensemble {| elementIndex := idx; indexedElement := item |}.

  Definition IndexedEnsembleSubtract
             (element : ElementType)
             (ens : IndexedEnsemble)
  : IndexedEnsemble :=
    fun element' => indexedElement element' <> element /\ ens element'.

  (* 'Deleting' a set of tuples [R] from a relation [F] is the same
   as taking the intersection of [F] and the complement of [R]. *)
  Definition EnsembleDelete
             (F : IndexedEnsemble)
             (R : Ensemble ElementType)
    := Intersection _ F (Complement _ (fun iel => R (indexedElement iel))).

  Definition IndexedEnsembleUpdate
             (ens : IndexedEnsemble)
             (cond : Ensemble ElementType)
             (updateR : relation ElementType)
  : IndexedEnsemble
    := fun e => (exists f: IndexedElement, ((ens f) /\ cond (indexedElement f) /\ updateR (indexedElement f) (indexedElement e))
                                           /\ elementIndex e = elementIndex f) \/
                ((ens e) /\ Complement _ (fun f => cond (indexedElement f)) e).

  Definition UnIndexedEnsembleListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType)  :=
    exists l', (map indexedElement l') = l /\
               (forall x, Ensembles.In _ ensemble x <-> List.In x l') /\
               NoDup (map elementIndex l').

  Definition UnConstrFreshIdx
             (ensemble : IndexedEnsemble)
             (bound : nat) :=
  forall element,
    ensemble element
    -> lt (elementIndex element) bound.

  Definition EnsembleIndexedListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType) :=
    (exists bound, UnConstrFreshIdx ensemble bound)
    /\ UnIndexedEnsembleListEquivalence ensemble l.
End IndexedEnsembles.

Definition GenericTuple A := list A.
Definition GenericTuples A := @IndexedEnsemble (GenericTuple A).

Definition EnsembleInsert {A : Type}
           (a : A)
           (R : Ensemble A)
           (a' : A) :=
  a' = a \/ R a'.

Lemma in_ensemble_insert_iff :
  forall {A} table tup inserted,
    Ensembles.In A (EnsembleInsert inserted table) tup <->
    tup = inserted \/ Ensembles.In A table tup.
Proof.
  firstorder.
Qed.

Definition Equiv {A} (ts1 ts2 : @IndexedEnsemble A) := forall t, ts1 t <-> ts2 t.

Theorem Equiv_refl : forall A ts1 ts2, ts1 = ts2 -> @Equiv A ts1 ts2.
Proof.
  unfold Equiv; firstorder congruence.
Qed.

Hint Resolve Equiv_refl.

Definition insert {A} (ts : GenericTuples A) (t : GenericTuple A) (ts' : GenericTuples A) : Prop :=
  exists idx,
    UnConstrFreshIdx ts idx
    /\ Equiv ts' (EnsembleInsert {| elementIndex := idx;
                                    indexedElement:= t |} ts).

Fixpoint allTuplesLen {A} (len : nat) (ts : list (GenericTuple A)) :=
  match ts with
  | nil => True
  | t :: ts' => length t = len /\ allTuplesLen len ts'
  end.

Definition Empty {A} : GenericTuples A := fun _ => False.
Definition bounded {A} (ts : GenericTuples A) := exists idx, UnConstrFreshIdx ts idx.
Definition minFreshIndex {A} (ts : GenericTuples A) (idx : nat) :=
  UnConstrFreshIdx ts idx
  /\ forall idx', (idx' < idx)%nat -> ~UnConstrFreshIdx ts idx'. 
Definition insertAt {A} (ts : GenericTuples A) (idx : nat) (t : GenericTuple A) : GenericTuples A :=
  EnsembleInsert {| elementIndex := idx;
                    indexedElement:= t |} ts.
Definition functional {A} (ts : GenericTuples A) :=
  forall t1 t2, Ensembles.In _ ts t1 -> Ensembles.In _ ts t2
                -> elementIndex t1 = elementIndex t2 -> t1 = t2.

Definition keepEq {A B} (EQ: A -> B -> Prop) (default : A) (ts : GenericTuples A) (key: W) (k : B) : GenericTuples A :=
  fun tup => Ensembles.In _ ts tup /\
          EQ match List.nth_error (indexedElement tup) (wordToNat key) with
             | Some k0 => k0
             | None => default
             end k.

Definition tupl := GenericTuple W.
Definition tuples := GenericTuples W.
