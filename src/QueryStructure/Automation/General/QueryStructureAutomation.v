Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        ADTSynthesis.Computation
        ADTSynthesis.ADT
        ADTSynthesis.ADTRefinement
        ADTSynthesis.ADTNotation
        ADTSynthesis.ADTRefinement.BuildADTRefinements
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.QueryStructure.Specification.Operations.Query
        ADTSynthesis.QueryStructure.Specification.Operations.Insert
        ADTSynthesis.QueryStructure.Specification.Operations.Empty
        ADTSynthesis.QueryStructure.Specification.Operations.Delete
        ADTSynthesis.QueryStructure.Specification.Operations.Update
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.InsertRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.DeleteRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryStructureRefinements
        ADTSynthesis.QueryStructure.Automation.General.QueryAutomation
        ADTSynthesis.QueryStructure.Automation.General.InsertAutomation
        ADTSynthesis.QueryStructure.Automation.General.DeleteAutomation.

Ltac start_honing_QueryStructure :=
  pose_string_ids;
  match goal with
      |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
      hone representation using (@DropQSConstraints_AbsR Rep) with defaults;
        match goal with
            |- context [Build_consDef (@Build_consSig ?Id _)
                                      (@absConstructor _ _ _ _ _)] =>
            hone constructor Id;
              [ etransitivity;
                [apply Constructor_DropQSConstraints |
                 simplify with monad laws; finish honing]
              | ]
        end; pose_string_ids;
        repeat (match goal with
                  | |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (absMethod _ (fun _ _ => Insert _ into _))] =>
                    drop_constraints_from_insert Id
                  | |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (absMethod _ (fun _ _ => Delete _ from _ where _))] =>
                    drop constraints from delete Id
                  | |- context [Build_methDef (@Build_methSig ?Id _ _)
                                              (@absMethod _ _ _ _ _ _)] =>
                    drop constraints from query Id
                end; pose_string_ids)
  end.

Tactic Notation "start" "honing" "QueryStructure" := start_honing_QueryStructure.
