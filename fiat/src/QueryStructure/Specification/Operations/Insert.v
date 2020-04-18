Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.Sets.Ensembles
        Coq.Arith.Arith
        Fiat.Computation.Core
        Fiat.ADT.ADTSig
        Fiat.ADT.Core
        Fiat.Common.StringBound
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.ADTNotation.BuildADT
        Fiat.ADTNotation.BuildADTSig
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure.

(* Definitions for updating query structures. *)

(* 'Inserting' a Tuple [tup] into a relation [R] represented
    as an ensemble produces a new ensemble that holds for any
    Tuple [tup'] equal to [tup] or which is already in [R]. *)

Definition QSInsertSpec
           {qs_schema}
           (qs : QueryStructure qs_schema)
           (Ridx : Fin.t _)
           (tup : @IndexedRawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx))
           (qs' : QueryStructure qs_schema)
: Prop :=
  (* All of the relations with a different index are untouched
     by insert. *)
  (forall Ridx',
     Ridx <> Ridx' ->
     GetRelation qs Ridx' = GetRelation qs' Ridx') /\
  (* If [tup] is consistent with the schema constraints, *)
  (SatisfiesAttributeConstraints Ridx (indexedElement tup))
  -> (forall tup',
        GetRelation qs Ridx tup'
        -> SatisfiesTupleConstraints Ridx (indexedElement tup) (indexedElement tup'))
  -> (forall tup',
        GetRelation qs Ridx tup'
        -> SatisfiesTupleConstraints Ridx (indexedElement tup') (indexedElement tup))
  (* and [tup] is consistent with the other tables per the cross-relation
     constraints, *)
  -> (forall Ridx', SatisfiesCrossRelationConstraints Ridx Ridx' (indexedElement tup)
                                                      ((GetRelation qs Ridx')))
  (* and each tuple in the other tables is consistent with the
     table produced by inserting [tup] into the relation indexed by [Ridx], *)
  -> (forall Ridx',
        Ridx' <> Ridx ->
        forall tup',
        (GetRelation qs Ridx') tup'
        -> SatisfiesCrossRelationConstraints
             Ridx' Ridx (indexedElement tup')
             (EnsembleInsert tup ((GetRelation qs Ridx))))
  (* [tup] is included in the relation indexed by [Ridx] after insert.
   The behavior of insertion is unspecified otherwise. *)
  -> (forall t, GetRelation qs' Ridx t <->
                (EnsembleInsert tup (GetRelation qs Ridx) t)).

Definition freshIdx {qs_schema} (qs : QueryStructure qs_schema) Ridx (n : nat) :=
  forall tup,
    GetRelation qs Ridx tup ->
    RawTupleIndex tup <> n.

Definition SuccessfulInsertSpec
           {qs_schema}
           (qs : QueryStructure qs_schema)
           (Ridx : _)
           (qs' : QueryStructure qs_schema)
           (tup : @IndexedRawTuple (GetNRelSchemaHeading (qschemaSchemas qs_schema) Ridx))
           (result : bool) : Prop :=
  decides result (forall t,
               GetRelation qs' Ridx t <->
               (EnsembleInsert tup
                               (GetRelation qs Ridx) t)).

Definition QSInsert {qs_schema} (qs : QueryStructure qs_schema) Ridx tup :=
  (idx <- Pick (freshIdx qs Ridx);
   qs' <- Pick (QSInsertSpec qs Ridx {| elementIndex := idx;
                                      indexedElement := tup |});
   b <- Pick (SuccessfulInsertSpec qs Ridx qs'
                                   {| elementIndex := idx;
                                      indexedElement := tup |});
   ret (qs', b))%comp.

Opaque QSInsert.

Notation "'Insert' b 'into' r '!' Ridx " :=
  (QSInsert r
            (ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames _) Ridx%string _))) b%Tuple)
    (r at level 0, at level 0) : QuerySpec_scope.
