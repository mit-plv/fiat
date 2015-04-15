Require Export Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Computation Fiat.ADT
        Fiat.ADTRefinement Fiat.ADTNotation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Insert
        Fiat.QueryStructure.Specification.Operations.Empty
        Fiat.QueryStructure.Specification.Operations.Update
        Fiat.QueryStructure.Specification.Operations.Delete.

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
Open Scope string_scope.
Open Scope Tuple.
Open Scope comp_scope.
