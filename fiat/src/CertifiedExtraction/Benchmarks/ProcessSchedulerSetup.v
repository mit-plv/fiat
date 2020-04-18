Require Export
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.Examples.QueryStructure.ProcessScheduler.

Require Export
        CertifiedExtraction.Extraction.QueryStructures.Wrappers
        CertifiedExtraction.Extraction.QueryStructures.QueryStructures
        CertifiedExtraction.Extraction.QueryStructures.WrappersAreConsistent.

Definition UnitSigT (P: unit -> Type) :
  P tt -> sigT P :=
  fun s => existT P tt s.

Ltac __destruct :=
  match goal with
  | _ => apply UnitSigT
  | [  |- forall idx: Fin.t _, _ ] => eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; simpl
  | [  |- GoodWrapper _ _ ] => econstructor; reflexivity
  | [  |- prim_prod _ _ ] => split
  | [  |- prod _ _ ] => split
  | [  |- unit ] => constructor
  end.

Ltac domWrappers_t :=
  red; simpl; repeat __destruct; eauto using Good_bool, Good_listW, Good_W.

Definition Scheduler_coDomainWrappers
  : coDomainWrappers QsADTs.ADTValue PartialSchedulerImpl.
Proof.
  domWrappers_t.
Defined.

Definition Scheduler_DomainWrappers
  : domainWrappers QsADTs.ADTValue PartialSchedulerImpl.
Proof.
  domWrappers_t.
Defined.

Definition QueryStructureRepWrapperT
           av (qs_schema : QueryStructureSchema.QueryStructureSchema)
           (qs_schema' := QueryStructureSchema.QueryStructureSchemaRaw
                            qs_schema)
           Index
  := @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema')
                 Schema.RawSchema
                 (fun ns =>
                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                 (fun ns
                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                    @IndexedEnsembles.IndexedEnsemble
                      (@RawTuple (Schema.rawSchemaHeading ns)))
                 (QueryStructureSchema.qschemaSchemas qs_schema') Index.

Definition Scheduler_RepWrapperT Index
  : QueryStructureRepWrapperT QsADTs.ADTValue SchedulerSchema Index.
Proof.
  unfold QueryStructureRepWrapperT; simpl; split.
  apply (@QS_WrapWBagOfTuples2 3 1 0).   (* FIXME generalize *)
  constructor.
Defined.

Definition Scheduler_DecomposeRep_well_behaved av qs_schema Index
(rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

  :=
  (fun r r' : IndexedQueryStructure qs_schema Index =>
     DecomposePrei3list_Agree _ _ rWrap
                              (id r) (id r')).

Definition RepSpec := Eval simpl in (Rep SchedulerSpec).
Definition RepImpl := Eval simpl in (Rep PartialSchedulerImpl).
Definition SharpenedRepImpl := fst (projT2 SharpenedScheduler).
Opaque SharpenedRepImpl.
Definition AbsR' := AbsR SharpenedRepImpl.

Require Import
        Bedrock.Platform.Facade.DFModule
        Bedrock.Platform.Facade.CompileUnit2.

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

Global Transparent CallBagMethod.