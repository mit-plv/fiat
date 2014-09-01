Require Import List String Ensembles Arith
        Computation.Core
        ADT.ADTSig ADT.Core
        ADTNotation.ilist ADTNotation.StringBound
        ADTNotation.BuildADT ADTNotation.BuildADTSig
        QueryStructure.QueryStructureSchema QueryStructure.QueryStructure
        InsertQSSpecs ListQueryStructureRefinements.

(* Definitions for updating query structures. *)

(* 'Deleting' a set of tuples [F] from a relation [R] is the same
   as taking the intersection of [R] and the complement of [F]. *)
Definition EnsembleDelete
           {A : Type}
           (F : Ensemble A)
           (R : Ensemble A)
: Ensemble A := Intersection _ R (Complement _ F).

(* This delete is fairly constrained:
   If the delete is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)
Definition QSDeleteSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (DeletedTuples : Ensemble (@IndexedTuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (qs' : QueryStructure qsSchemaHint')
: Prop :=
  (* Either we get a database with an updated ensemble whose
     tuples satisfy the schema constraints. *)
  ((forall tup tup',
        EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples tup
        -> EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples tup'
        -> SatisfiesSchemaConstraints Ridx tup tup')
   (* And is compatible with the cross-schema constraints. *)
  /\ (forall Ridx',
        Ridx' <> Ridx ->
        forall tup',
          (GetRelation qsHint Ridx') tup'
          -> SatisfiesCrossRelationConstraints
               Ridx' Ridx tup'
               (EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples))
  (* And is equivalent to removing the specified tuples
     from the original ensemble *)
  /\ (forall tup, GetRelation qs' Ridx tup <->
                  (EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples tup))
  (* And all other tables are unchanged*)
  /\ (forall Ridx',
     Ridx <> Ridx' ->
     GetRelation qsHint Ridx' = GetRelation qs' Ridx'))
  \/
  (* Otherwise, one of the schema constraints was violated. *)
  ((~(forall tup tup',
        EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples tup
        -> EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples tup'
        -> SatisfiesSchemaConstraints Ridx tup tup')
    (* Or one of the cross-schema constraints was violated. *)
  \/ ~(forall Ridx',
        Ridx' <> Ridx ->
        forall tup',
          (GetRelation qsHint Ridx') tup'
          -> SatisfiesCrossRelationConstraints
               Ridx' Ridx tup'
               (EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples))
   ) /\
   (* And the updated table is equivalent to the original *)
   (forall tup, GetRelation qs' Ridx tup <->
                (GetRelation qsHint Ridx tup))).

(* We augment [QSDeleteSpec] so that delete also returns a list of the
   deleted Tuples. *)
Definition QSDelete (qs : QueryStructureHint) Ridx DeletedTuples :=
  (qs'       <- Pick (QSDeleteSpec _ Ridx DeletedTuples);
   deleted   <- Pick (EnsembleIndexedListEquivalence
                        (Intersection _
                                      (GetRelation qsHint Ridx)
                                      (GetRelation qs' Ridx)));
   ret (deleted, qs'))%comp.

Notation "'Delete' b 'from' Ridx 'where' Ens" :=
  (QSDelete _ {|bindex := Ridx%comp |} (fun b => Ens))
    (at level 80) : QuerySpec_scope.
