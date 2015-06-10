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
           (Ridx : Fin.t _)
           (DeletedTuples : @Ensemble (@RawTuple (GetNRelSchemaHeading _ Ridx))) :=
  QSMutate qs Ridx (EnsembleDelete (GetRelation qs Ridx) DeletedTuples).

Opaque QSDelete.

Notation "'Delete' b 'from' r '!' Ridx 'where' Ens" :=
  (QSDelete r (ibound (indexb (@Build_BoundedIndex _ _ (QSschemaNames _) Ridx%string _))) (fun b => Ens))
    (r at level 0, at level 80) : QuerySpec_scope.
