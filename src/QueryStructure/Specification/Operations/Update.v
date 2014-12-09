Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
        ADTSynthesis.Computation.Core
        ADTSynthesis.ADT.ADTSig
        ADTSynthesis.ADT.Core
        ADTSynthesis.Common.ilist
        ADTSynthesis.Common.StringBound
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.ADTNotation.BuildADT
        ADTSynthesis.ADTNotation.BuildADTSig
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure.

(* Definitions for updating query structures. *)

(* Updating a set of tuples [UpdatedTuples] in a Relation
 [GetRelation qshint Ridx] is permitted if the resulting
 Ensemble satisfies the Schema Constraints, *)
Definition UpdatePreservesSchemaConstraints
           {heading}
           (Rel : @IndexedEnsemble (@Tuple heading))
           (UpdatedTuples : @Ensemble Tuple)
           (UpdateFunction : Tuple -> Tuple)
           (Constr : Tuple -> Tuple -> Prop)
  :=
    forall tup tup',
      IndexedEnsembleUpdate Rel UpdatedTuples UpdateFunction tup
      -> IndexedEnsembleUpdate Rel UpdatedTuples UpdateFunction tup'
      -> Constr (indexedElement tup) (indexedElement tup').

(* AND if the resulting Ensemble satisfies the Cross Constraints. *)
Definition UpdatePreservesCrossConstraints
           {heading heading'}
           (Rel : @IndexedEnsemble (@Tuple heading))
           (Rel' : @IndexedEnsemble (@Tuple heading'))
           (UpdateTuples : @Ensemble Tuple)
           (UpdateFunction : Tuple -> Tuple)
           (CrossConstr : Tuple -> @IndexedEnsemble Tuple -> Prop)
  :=
    forall tup',
      Rel' tup'
      -> CrossConstr (indexedTuple tup')
                     (IndexedEnsembleUpdate Rel UpdateTuples UpdateFunction).

(* This update is fairly constrained:
   If the update is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)
Definition QSUpdateSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (UpdatedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (UpdateFunction :  (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))) ->
                              (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (qs' : QueryStructure qsSchemaHint')
: Prop :=
  (* Either we get a database with an updated ensemble whose
     tuples satisfy the schema constraints. *)
  (UpdatePreservesSchemaConstraints (GetRelation qsHint Ridx) UpdatedTuples UpdateFunction (SatisfiesSchemaConstraints Ridx)
   (* And is compatible with the cross-schema constraints. *)
   /\ (forall Ridx',
         Ridx' <> Ridx
         -> UpdatePreservesCrossConstraints
              (GetRelation qsHint Ridx)
              (GetRelation qsHint Ridx')
              UpdatedTuples
              UpdateFunction
              (SatisfiesCrossRelationConstraints Ridx' Ridx)
   (* And is equivalent to updating the specified tuples
     in the original ensemble *)
   /\ (forall tup, GetRelation qs' Ridx tup <->
                   (IndexedEnsembleUpdate (GetRelation qsHint Ridx) UpdatedTuples UpdateFunction tup))
   (* And all other tables are unchanged*)
   /\ (forall Ridx',
         Ridx <> Ridx' ->
         GetRelation qsHint Ridx' = GetRelation qs' Ridx')))
  \/
  (* Otherwise, one of the schema constraints was violated. *)
  ((~ UpdatePreservesSchemaConstraints
      (GetRelation qsHint Ridx) UpdatedTuples UpdateFunction
      (SatisfiesSchemaConstraints Ridx)
    (* Or one of the cross-schema constraints was violated. *)
    \/ ~ (forall Ridx',
         Ridx' <> Ridx
         -> UpdatePreservesCrossConstraints
              (GetRelation qsHint Ridx)
              (GetRelation qsHint Ridx')
              UpdatedTuples
              UpdateFunction
              (SatisfiesCrossRelationConstraints Ridx' Ridx)))
    /\
   (* And all the tables are equivalent to the original *)
   (forall r tup, GetRelation qs' r tup <->
                (GetRelation qsHint r tup))).

Definition SuccessfulUpdateSpec
           (qs : QueryStructureHint)
           (Ridx : _)
           (qs' : QueryStructure qsSchemaHint')
           (UpdatedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (UpdateFunction : (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))) ->
                             (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (result : bool) : Prop :=
  decides result (forall t,
               GetRelation qs' Ridx t <->
               (IndexedEnsembleUpdate (GetRelation qsHint Ridx) UpdatedTuples UpdateFunction t)).

Definition QSUpdate (qs : QueryStructureHint) Ridx
           (UpdatedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))))
           (UpdateFunction : (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx))) ->
                             (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))) :=
  (qs'       <- Pick (QSUpdateSpec _ Ridx UpdatedTuples UpdateFunction);
   b         <- Pick (SuccessfulUpdateSpec _ Ridx qs' UpdatedTuples UpdateFunction);
   ret (qs', b))%comp.

Opaque QSUpdate.

Variable UpdateTuple : forall (attrs: list Attribute) (attr: Attribute) (value: Component attr),
                         @Tuple (BuildHeading attrs) -> @Tuple (BuildHeading attrs).

Notation "a := b" := (UpdateTuple _ {|bindex := a|} (a::b)) (at level 80).
Notation "[ a ; .. ; c ]" := (compose a .. (compose c id) ..).

Notation "'Update' b 'from' Ridx 'set' Trans 'where' Ens" :=
  (QSUpdate _ {|bindex := Ridx%comp |} (fun b => Ens) Trans)
    (at level 80) : QuerySpec_scope.
