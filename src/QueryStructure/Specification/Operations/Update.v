Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
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
           (UpdateFunction : @RawTuple (GetNRelSchemaHeading _ Ridx) ->
                             @RawTuple (GetNRelSchemaHeading _ Ridx))
: Comp (QueryStructure qs_schema * list RawTuple) :=
  QSMutate qs Ridx (IndexedEnsembleUpdate (GetRelation qs Ridx) UpdatedTuples UpdateFunction).

Opaque QSUpdate.


Notation "'Update' b 'from' r '!' Ridx 'making' Trans 'where' Ens" :=
  (QSUpdate r (ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames _) Ridx%string _))) (fun b => Ens) Trans)
    (r at level 0, at level 80) : QuerySpec_scope.
