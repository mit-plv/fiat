Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Automation.MasterPlan.

Require Import DFModule CertifiedExtraction.ADT2CompileUnit.

Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Require Import CompileUnit2.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction
        CertifiedExtraction.Extraction.QueryStructures
        CertifiedExtraction.ADT2CompileUnit.

Definition RepSpec := Eval simpl in (Rep SchedulerSpec).
Definition RepImpl := Eval simpl in (Rep PartialSchedulerImpl).
Definition SharpenedRepImpl := fst (projT2 SharpenedScheduler).
Opaque SharpenedRepImpl.
Definition AbsR' := AbsR SharpenedRepImpl.

Global Transparent CallBagMethod.

Ltac __compile_clear_bodies_of_ax_spec :=
  repeat (unfold GenExports, map_aug_mod_name, aug_mod_name,
          GLabelMapFacts.uncurry; simpl);
  repeat lazymatch goal with
    | |- context[GenAxiomaticSpecs ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] =>
      let a := fresh in
      pose (GenAxiomaticSpecs a0 a1 a2 a3 a4 a5 a6 a7) as a;
      change (GenAxiomaticSpecs a0 a1 a2 a3 a4 a5 a6 a7) with a;
      clearbody a
    end.

Ltac __compile_start_compiling_module imports ::=
  lazymatch goal with
  | [  |- sigT (fun _ => BuildCompileUnit2TSpec  _ _ _ _ _ _ _ _ _ _ _ _ _ _ ) ] =>
    eexists;
    unfold DecomposeIndexedQueryStructure', DecomposeIndexedQueryStructurePre', DecomposeIndexedQueryStructurePost';
    eapply (BuildCompileUnit2T' QSEnv_Ax); try apply eq_refl (* reflexivity throws an Anomaly *)
  | [  |- forall _: (Fin.t _), (sigT _)  ] =>
    __compile_clear_bodies_of_ax_spec;
    eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; repeat (apply Build_prim_prod || exact tt)
  end.

Definition methodBody
           methodName
           (CUnit: {env : Env QsADTs.ADTValue &
              BuildCompileUnit2TSpec env AbsR'
              (fun r : Rep (fst (projT1 SharpenedScheduler)) => BagSanityConditions (prim_fst r))
              (DecomposeIndexedQueryStructure' QsADTs.ADTValue
                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (icons3 SearchUpdateTerm inil3))
              (DecomposeIndexedQueryStructurePre' QsADTs.ADTValue
                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (icons3 SearchUpdateTerm inil3) (Scheduler_RepWrapperT (icons3 SearchUpdateTerm inil3)))
              (DecomposeIndexedQueryStructurePost' QsADTs.ADTValue
                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (icons3 SearchUpdateTerm inil3) (Scheduler_RepWrapperT (icons3 SearchUpdateTerm inil3)))
              (QueryStructureSchema.numQSschemaSchemas SchedulerSchema) "ProcessSchedulerAX" "ProcessSchedulerOP"
              Scheduler_coDomainWrappers Scheduler_DomainWrappers
              (Scheduler_RepWrapperT (icons3 SearchUpdateTerm inil3))
              (Scheduler_DecomposeRep_well_behaved QsADTs.ADTValue
                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (icons3 SearchUpdateTerm inil3) (Scheduler_RepWrapperT (icons3 SearchUpdateTerm inil3)))
              SharpenedRepImpl}) :=
  match (StringMap.find methodName (Funs (module (projT1 (projT2 CUnit))))) with
  | Some dffun => Some (Body (Core (dffun)))
  | None => None
  end.
