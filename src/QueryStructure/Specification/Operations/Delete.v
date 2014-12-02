Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
        ADTSynthesis.Computation.Core
        ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.ADTNotation.BuildADT ADTSynthesis.ADTNotation.BuildADTSig
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.QueryStructure.Specification.Operations.Insert.

(* Definitions for updating query structures. *)

(* Removing a set of tuples [DeletedTuples] from a Relation
 [GetRelation qshint Ridx] is permitted if the resulting
 Ensemble satisfies the Schema Constraints, *)
Definition DeletePreservesSchemaConstraints
           {heading}
           (Rel : @IndexedEnsemble (@Tuple heading))
           (DeletedTuples : @Ensemble Tuple)
           (Constr : Tuple -> Tuple -> Prop)
  :=
    forall tup tup',
      EnsembleDelete Rel DeletedTuples tup
      -> EnsembleDelete Rel DeletedTuples tup'
      -> Constr (indexedElement tup) (indexedElement tup').

(* AND if the resulting Ensemble satisfies the Cross Constraints. *)
Definition DeletePreservesCrossConstraints
           {heading heading'}
           (Rel : @IndexedEnsemble (@Tuple heading))
           (Rel' : @IndexedEnsemble (@Tuple heading'))
           (DeletedTuples : @Ensemble Tuple)
           (CrossConstr : Tuple -> @IndexedEnsemble Tuple -> Prop)
  :=
    forall tup',
      Rel' tup'
      -> CrossConstr (indexedTuple tup')
                     (EnsembleDelete Rel DeletedTuples).

(* This delete is fairly constrained:
   If the delete is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)

Definition QSDeleteSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (DeletedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (qs' : QueryStructure qsSchemaHint')
: Prop :=
  (* Either we get a database with an updated ensemble whose
     tuples satisfy the schema constraints. *)
  (DeletePreservesSchemaConstraints (GetRelation qsHint Ridx) DeletedTuples (SatisfiesSchemaConstraints Ridx)
   (* And is compatible with the cross-schema constraints. *)
   /\ (forall Ridx',
         Ridx' <> Ridx
         -> DeletePreservesCrossConstraints
              (GetRelation qsHint Ridx)
              (GetRelation qsHint Ridx')
              DeletedTuples
              (SatisfiesCrossRelationConstraints Ridx' Ridx)
   (* And is equivalent to removing the specified tuples
     from the original ensemble *)
   /\ (forall tup, GetRelation qs' Ridx tup <->
                   (EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples tup))
   (* And all other tables are unchanged*)
   /\ (forall Ridx',
         Ridx <> Ridx' ->
         GetRelation qsHint Ridx' = GetRelation qs' Ridx')))
  \/
  (* Otherwise, one of the schema constraints was violated. *)
  ((~ DeletePreservesSchemaConstraints
      (GetRelation qsHint Ridx) DeletedTuples
      (SatisfiesSchemaConstraints Ridx)
    (* Or one of the cross-schema constraints was violated. *)
    \/ ~ (forall Ridx',
         Ridx' <> Ridx
         -> DeletePreservesCrossConstraints
              (GetRelation qsHint Ridx)
              (GetRelation qsHint Ridx')
              DeletedTuples
              (SatisfiesCrossRelationConstraints Ridx' Ridx)))
    /\
   (* And all the tables are equivalent to the original *)
   (forall r tup, GetRelation qs' r tup <->
                (GetRelation qsHint r tup))) .

(* We augment [QSDeleteSpec] so that delete also returns a list of the
   deleted Tuples. *)
Definition QSDelete (qs : QueryStructureHint) Ridx
           (DeletedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))) :=
  (qs'       <- Pick (QSDeleteSpec _ Ridx DeletedTuples);
   deleted   <- Pick (UnIndexedEnsembleListEquivalence
                        (Intersection _
                                      (GetRelation qsHint Ridx)
                                      (Complement _ (GetRelation qs' Ridx))));
   ret (qs', deleted))%comp.

Opaque QSDelete.

Notation "'Delete' b 'from' Ridx 'where' Ens" :=
  (QSDelete _ {|bindex := Ridx%comp |} (fun b => Ens))
    (at level 80) : QuerySpec_scope.
