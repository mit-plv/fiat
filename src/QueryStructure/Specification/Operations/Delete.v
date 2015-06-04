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
(* We augment [QSDeleteSpec] so that delete also returns a list of the
   deleted Tuples. *)

Definition QSDelete {qs_schema}
           (qs : QueryStructure qs_schema)
           (Ridx : @BoundedString _ (QSschemaNames qs_schema))
           (DeletedTuples : @Ensemble (@RawTuple (GetNRelSchemaHeading _ (ibound (indexb Ridx))))) :=
  QSMutate qs Ridx (EnsembleDelete (GetRelation qs Ridx) DeletedTuples).

Opaque QSDelete.

Notation "'Delete' b 'from' Ridx 'where' Ens" :=
  (let hint : QueryStructureHint := _ in
  QSDelete (@qsHint hint) (@Build_BoundedIndex _ _ (QSschemaNames qsSchemaHint) Ridx%string _) (fun b => Ens))
    (at level 80) : QuerySpec_scope.
