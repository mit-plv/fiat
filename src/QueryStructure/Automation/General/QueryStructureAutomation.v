Require Import Coq.Strings.String Coq.omega.Omega Coq.Lists.List Coq.Logic.FunctionalExtensionality Coq.Sets.Ensembles
        Coq.Sorting.Permutation
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.QueryStructure.Specification.Operations.Query
        Fiat.QueryStructure.Specification.Operations.Insert
        Fiat.QueryStructure.Specification.Operations.Empty
        Fiat.QueryStructure.Specification.Operations.Delete
        Fiat.QueryStructure.Specification.Operations.Update
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.InsertRefinements
        Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements
        Fiat.QueryStructure.Implementation.Operations.General.QueryStructureRefinements
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.General.QueryAutomation
        Fiat.QueryStructure.Automation.General.InsertAutomation
        Fiat.QueryStructure.Automation.General.DeleteAutomation.

Ltac start_honing_QueryStructure' :=
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ intros;
                              match goal with
                                |  |- refine _ (?E _) => let H := fresh in set (H := E)
                                | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ intros;
                              match goal with
                                |  |- refine _ (?E _ _) => let H := fresh in set (H := E)
                                | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl;
                              match goal with
                                | |- context [QSInsert _ _ _] => drop_constraints_from_insert
                                | |- context [QSDelete _ _ _] => drop_constraints_from_delete
                                | |- context [Query_For _] => drop_constraints_from_query
                                | |- _ => idtac
                              end | ]
                          ])]
    end | ].

Ltac start_honing_QueryStructure :=
  match goal with
      |- ?R ?QSSpec =>
      cbv delta [QSSpec
                   QSGetNRelSchemaHeading GetNRelSchema
                   GetNRelSchemaHeading Domain Specif.value
                   ] beta; simpl;
      (*pose_string_hyps; pose_heading_hyps;*)
      match R with
        | ?MostlySharpened =>
          eapply MostlySharpened_Start; start_honing_QueryStructure'
        | ?FullySharpened =>
          eapply FullySharpened_Start; [start_honing_QueryStructure' | ]
      end
  end; pose_string_hyps; pose_heading_hyps.

Tactic Notation "start" "honing" "QueryStructure" := start_honing_QueryStructure.
