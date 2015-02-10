Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
        ADTSynthesis.Computation.Core
        ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.ADTNotation.BuildADT ADTSynthesis.ADTNotation.BuildADTSig
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure.

(* Definitions for updating query structures. *)

(* Mutating a Relation [GetRelation qshint Ridx] is permitted if the resulting
 Ensemble satisfies the Tuple Constraints, *)
Definition MutationPreservesTupleConstraints
           {heading}
           (MutatedTuples : @IndexedEnsemble (@Tuple heading))
           (Constr : Tuple -> Tuple -> Prop)
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
           (MutatedTuples : @IndexedEnsemble (@Tuple heading))
           (Constr : Tuple -> Prop)
  :=
    forall tup,
      MutatedTuples tup
      -> Constr (indexedElement tup).

(* AND if the resulting Ensemble satisfies the Cross Constraints. *)

Definition MutationPreservesCrossConstraints
           {heading heading'}
           (Rel : @IndexedEnsemble (@Tuple heading))
           (MutatedTuples : @IndexedEnsemble (@Tuple heading'))
           (CrossConstr : Tuple -> @IndexedEnsemble Tuple -> Prop)
  :=
    forall tup',
      Rel tup'
      -> CrossConstr (indexedTuple tup')
                     (MutatedTuples).

(* This mutation is fairly constrained:
   If the mutation is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)
Definition QSMutateSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (MutatedTuples : @IndexedEnsemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (qs' : QueryStructure qsSchemaHint')
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
        Same_set _ (GetRelation qsHint Ridx') (GetRelation qs' Ridx'))
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
              (GetRelation qsHint Ridx')
              (SatisfiesCrossRelationConstraints Ridx Ridx'))
    \/ ~ (forall Ridx',
            Ridx' <> Ridx
            -> MutationPreservesCrossConstraints
                 (GetRelation qsHint Ridx')
                 MutatedTuples
                 (SatisfiesCrossRelationConstraints Ridx' Ridx)))
    /\
   (* And all the tables are equivalent to the original *)
   (forall r, Same_set _ (GetRelation qs' r) (GetRelation qsHint r))).

(* We augment [QSMutateSpec] so that delete also returns a list of the
   affected Tuples. *)
Definition QSMutate (qs : QueryStructureHint) Ridx MutatedTuples :=
  (qs'       <- Pick (QSMutateSpec _ Ridx MutatedTuples);
   mutated   <- Pick (UnIndexedEnsembleListEquivalence
                        (Intersection _
                                      (GetRelation qsHint Ridx)
                                      (Complement _ (GetRelation qs' Ridx))));
   ret (qs', mutated))%comp.

Opaque QSMutate.
