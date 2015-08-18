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
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Operations.Mutate.

(* Definitions for updating query structures. *)

(* This update is fairly constrained:
   If the update is consistent with the constraints, it is
   applied to the table,
   OTHERWISE
   No tables are changed. *)
Definition QSUpdate
           qs_schema
           (qs : QueryStructure qs_schema)
           (Ridx : _)
           (UpdatedTuples : @Ensemble (@RawTuple (GetNRelSchemaHeading _ Ridx)))
           (UpdateFunction : Relation_Definitions.relation (@RawTuple (GetNRelSchemaHeading _ Ridx)))
: Comp (QueryStructure qs_schema * list RawTuple) :=
  QSMutate qs Ridx (IndexedEnsembleUpdate (GetRelation qs Ridx) UpdatedTuples UpdateFunction).

Notation "'Update' b 'from' r '!' Ridx 'as' c 'making' Trans 'where' Ens" :=
  (let qs_schema := _ in
   let r' : QueryStructure qs_schema := r in
   let Ridx' := ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames qs_schema) Ridx%string _)) in
   (QSUpdate r' Ridx'
            (fun b => Ens) (fun b c => Trans)))
    (r at level 0, Ridx at level 0, Ens at level 0, Trans at level 0, at level 80).
