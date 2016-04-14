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
