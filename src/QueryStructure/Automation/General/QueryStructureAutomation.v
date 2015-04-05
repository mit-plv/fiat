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
        ADTSynthesis.QueryStructure.Automation.Common
        ADTSynthesis.QueryStructure.Automation.General.QueryAutomation
        ADTSynthesis.QueryStructure.Automation.General.InsertAutomation
        ADTSynthesis.QueryStructure.Automation.General.DeleteAutomation.

Ltac start_honing_QueryStructure :=
  match goal with
      |- ?R ?QSSpec =>
      cbv delta [QSSpec
                   QSGetNRelSchemaHeading GetNRelSchema
                   GetNRelSchemaHeading Domain Specif.value
                   IndexBound_tail IndexBound_head] beta; simpl;
      pose_string_hyps; pose_heading_hyps;
      start_sharpening_ADT;
      eapply SharpenStep;
      [ match goal with
            |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
            eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
              [ repeat (first [eapply refine_Constructors_nil
                              | eapply refine_Constructors_cons;
                                [ intros;
                                  match goal with
                                    |  |- refine _ (?E _) => let H := fresh in set (H := E)
                                    | _ => idtac
                                  end;
                                  (* Drop constraints from empty *)
                                  try apply Constructor_DropQSConstraints
                                | ] ])
              | repeat (first [eapply refine_Methods_nil
                              | eapply refine_Methods_cons;
                                [ intros;
                                  match goal with
                                    |  |- refine _ (?E _ _) => let H := fresh in set (H := E)
                                    | _ => idtac
                                  end;
                                  match goal with
                                    | |- context [QSInsert _ _ _] => drop_constraints_from_insert
                                    | |- context [QSDelete _ _ _] => drop_constraints_from_delete
                                    | |- context [Query_For _] => drop constraints from query
                                    | |- _ => idtac
                                  end | ]
                              ])]
        end | ]
  end;
  pose_string_hyps; pose_heading_hyps.

Tactic Notation "start" "honing" "QueryStructure" := start_honing_QueryStructure.
