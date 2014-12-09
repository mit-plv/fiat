Require Export Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Computation ADTSynthesis.ADT ADTSynthesis.ADTRefinement ADTSynthesis.ADTNotation ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.ADTRefinement.BuildADTRefinements ADTSynthesis.QueryStructure.Specification.Operations.Query ADTSynthesis.QueryStructure.Specification.Operations.Insert ADTSynthesis.QueryStructure.Specification.Operations.Empty (* Add Update *)
        ADTSynthesis.QueryStructure.Specification.Operations.Delete ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure.

Notation "heading / attr_index" := ((fun x : Attributes heading => x)
                                       {| bindex := attr_index; indexb := _ |})
                                      (at level 40, left associativity) : QueryStructure_scope.

Notation "QSSchema # rel_key" := (TupleDef QSSchema rel_key) (at level 100, no associativity) : QueryStructure_scope.

Notation "?[ A ]" := (if A then true else false) (at level 50) : QueryStructure_scope.

Open Scope QSSchema.
Open Scope ADTSig.
Open Scope QueryImpl.
Open Scope QueryStructure.
Open Scope Schema.
Open Scope QuerySpec.
Open Scope string.
Open Scope Tuple.
Open Scope comp_scope.
