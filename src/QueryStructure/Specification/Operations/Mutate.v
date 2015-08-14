Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Sets.Ensembles
        Coq.Arith.Arith
        Fiat.Computation.Core
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.Common.ilist
        Fiat.Common.StringBound
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

(* Definitions for updating query structures. *)

(* Mutating a Relation [GetRelation qshint Ridx] is permitted if the resulting
 Ensemble satisfies the Tuple Constraints, *)
Definition MutationPreservesTupleConstraints
           {heading}
           (MutatedTuples : @IndexedEnsemble (@RawTuple heading))
           (Constr : RawTuple -> RawTuple -> Prop)
  :=
    forall tup tup',
      elementIndex tup <> elementIndex tup'
      -> MutatedTuples tup
      -> MutatedTuples tup'
      -> Constr (indexedElement tup) (indexedElement tup').

(* AND the tuples in the resulting Ensemble satisfy the attribute
 constraints *)
Definition MutationPreservesAttributeConstraints
           {heading}
           (MutatedTuples : @IndexedEnsemble (@RawTuple heading))
           (Constr : RawTuple -> Prop)
  :=
    forall tup,
      MutatedTuples tup
      -> Constr (indexedElement tup).

(* AND if the resulting Ensemble satisfies the Cross Constraints. *)

Definition MutationPreservesCrossConstraints
           {heading heading'}
           (Rel : @IndexedEnsemble (@RawTuple heading))
           (MutatedRawTuples : @IndexedEnsemble (@RawTuple heading'))
           (CrossConstr : RawTuple -> @IndexedEnsemble RawTuple -> Prop)
  :=
    forall tup',
      Rel tup'
      -> CrossConstr (indexedRawTuple tup')
                     (MutatedRawTuples).

(* This mutation is fairly constrained:
   If the mutation is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)

Definition QSMutateSpec
           (qs_schema : QueryStructureSchema)
           (qs : QueryStructure qs_schema)
           (Ridx : _)
           (MutatedTuples : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading _ Ridx)))
           (qs' : QueryStructure qs_schema)
: Prop :=
  (* Either we get a database with an updated ensemble whose
     tuples satisfy the attribute constraints. *)
  (MutationPreservesAttributeConstraints MutatedTuples (SatisfiesAttributeConstraints Ridx))
   (* AND is compatible with the attribute constraints. *)
  /\ (MutationPreservesTupleConstraints MutatedTuples (SatisfiesTupleConstraints Ridx))
   (* And is compatible with the cross-schema constraints. *)
  /\ (forall Ridx',
         Ridx' <> Ridx
         -> MutationPreservesCrossConstraints
              MutatedTuples
              (GetRelation qs' Ridx')
              (SatisfiesCrossRelationConstraints Ridx Ridx'))
  /\ (forall Ridx',
        Ridx' <> Ridx
        -> MutationPreservesCrossConstraints
             (GetRelation qs' Ridx')
             MutatedTuples
             (SatisfiesCrossRelationConstraints Ridx' Ridx))
  (* And is equivalent to removing the specified tuples
     from the original ensemble *)
  /\ (Same_set _ (GetRelation qs' Ridx) MutatedTuples)
  (* And all other tables are unchanged*)
  /\ (forall Ridx',
        Ridx <> Ridx' ->
        Same_set _ (GetRelation qs Ridx') (GetRelation qs' Ridx'))
  \/
  (* Otherwise, one of the attribute constraints was violated. *)
  ((~ MutationPreservesAttributeConstraints MutatedTuples (SatisfiesAttributeConstraints Ridx)
    (* OR one of the tuple constraints was violated. *)
    \/ (~ MutationPreservesTupleConstraints
          MutatedTuples
          (SatisfiesTupleConstraints Ridx))
    (* OR one of the cross-schema constraints was violated. *)
    \/ ~ (forall Ridx',
         Ridx' <> Ridx
         -> MutationPreservesCrossConstraints
              MutatedTuples
              (GetRelation qs Ridx')
              (SatisfiesCrossRelationConstraints Ridx Ridx'))
    \/ ~ (forall Ridx',
            Ridx' <> Ridx
            -> MutationPreservesCrossConstraints
                 (GetRelation qs Ridx')
                 MutatedTuples
                 (SatisfiesCrossRelationConstraints Ridx' Ridx)))
    /\
   (* And all the tables are equivalent to the original *)
   (forall r, Same_set _ (GetRelation qs' r) (GetRelation qs r))).

(* We augment [QSMutateSpec] so that delete also returns a list of the
   affected Tuples. *)
Definition QSMutate qs_schema (qs : QueryStructure qs_schema) Ridx MutatedTuples :=
  (qs'       <- Pick (QSMutateSpec qs Ridx MutatedTuples);
   mutated   <- Pick (UnIndexedEnsembleListEquivalence
                        (Intersection _
                                      (GetRelation qs Ridx)
                                      (Complement _ (GetRelation qs' Ridx))));
   ret (qs', mutated))%comp.

Opaque QSMutate.
