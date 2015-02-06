Require Import Coq.Lists.List Coq.Strings.String Coq.Sets.Ensembles Coq.Arith.Arith
        ADTSynthesis.Computation.Core
        ADTSynthesis.ADT.ADTSig ADTSynthesis.ADT.Core
        ADTSynthesis.Common.ilist ADTSynthesis.Common.StringBound ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.ADTNotation.BuildADT ADTSynthesis.ADTNotation.BuildADTSig
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.QueryStructure.Specification.Operations.Mutate.
(* We augment [QSDeleteSpec] so that delete also returns a list of the
   deleted Tuples. *)
Definition QSDelete (qs : QueryStructureHint) Ridx
           (DeletedTuples : @Ensemble (@Tuple (schemaHeading (QSGetNRelSchema _ Ridx)))) :=
  QSMutate qs Ridx (EnsembleDelete (GetRelation qsHint Ridx) DeletedTuples).

Opaque QSDelete.

Notation "'Delete' b 'from' Ridx 'where' Ens" :=
  (QSDelete _ {|bindex := Ridx%comp |} (fun b => Ens))
    (at level 80) : QuerySpec_scope.
