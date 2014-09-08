Require Import List String Ensembles Arith
        Computation.Core
        ADT.ADTSig ADT.Core
        Common.ilist ADTNotation.StringBound
        ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.QueryStructureSchema QueryStructure.QueryStructure.

(* Definitions for updating query structures. *)

(* 'Inserting' a Tuple [tup] into a relation [R] represented
    as an ensemble produces a new ensemble that holds for any
    Tuple [tup'] equal to [tup] or which is already in [R]. *)
Definition EnsembleInsert {A : Type}
           (a : A)
           (R : Ensemble A)
           (a' : A) :=
  a' = a \/ R a'.

Lemma in_ensemble_insert_iff :
  forall {A} table tup inserted,
    In A (EnsembleInsert inserted table) tup <->
    tup = inserted \/ In A table tup.
Proof.
  firstorder.
Qed.

Definition QSInsertSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (tup : @IndexedTuple (schemaHeading (QSGetNRelSchema _ Ridx)))
           (qs' : QueryStructure qsSchemaHint')
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall Ridx',
     Ridx <> Ridx' ->
     GetRelation qsHint Ridx' = GetRelation qs' Ridx') /\
  (* If [tup] is consistent with the schema constraints, *)
  (SatisfiesSchemaConstraints Ridx tup tup)
  -> (forall tup', GetRelation qsHint Ridx tup' ->
                SatisfiesSchemaConstraints Ridx tup tup')
  -> (forall tup', GetRelation qsHint Ridx tup' ->
    SatisfiesSchemaConstraints Ridx tup' tup)
  (* and [tup] is consistent with the other tables per the cross-relation
     constraints, *)
  -> (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' tup
                                                      ((GetRelation qsHint Ridx')))
  (* and each tuple in the other tables is consistent with the
     table produced by inserting [tup] into the relation indexed by [Ridx], *)
  -> (forall Ridx',
        Ridx' <> Ridx ->
        forall tup',
        (GetRelation qsHint Ridx') tup'
        -> SatisfiesCrossRelationConstraints
             Ridx' Ridx tup'
             (EnsembleInsert tup ((GetRelation qsHint Ridx))))
  (* [tup] is included in the relation indexed by [Ridx] after insert.
   The behavior of insertion is unspecified otherwise. *)
  -> (forall t, GetRelation qs' Ridx t <->
                (EnsembleInsert tup (GetRelation qsHint Ridx) t)).

Definition freshIdx (qs : QueryStructureHint) Ridx (n : nat) :=
  forall tup,
    GetRelation qsHint Ridx tup ->
    tupleIndex tup <> n.

Definition SuccessfulInsertSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (qs' : QueryStructure qsSchemaHint')
           (tup : @IndexedTuple (schemaHeading (QSGetNRelSchema _ Ridx)))
           (result : bool) : Prop :=
  decides result (forall t,
               GetRelation qs' Ridx t <->
               (EnsembleInsert tup
                               (GetRelation qsHint Ridx) t)).

Definition QSInsert (qs : QueryStructureHint) Ridx tup :=
  (idx <- Pick (freshIdx _ Ridx);
   qs' <- Pick (QSInsertSpec _ Ridx {| tupleIndex := idx;
                                      indexedTuple := tup |});
   b <- Pick (SuccessfulInsertSpec _ Ridx qs'
                                   {| tupleIndex := idx;
                                      indexedTuple := tup |});
   ret (qs', b))%comp.

Opaque QSInsert.

Notation "'Insert' b 'into' Ridx " :=
  (QSInsert _ {|bindex := Ridx%comp |} b)
    (at level 80) : QuerySpec_scope.
