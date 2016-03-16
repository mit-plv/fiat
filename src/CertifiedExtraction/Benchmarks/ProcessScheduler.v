Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction
        CertifiedExtraction.Extraction.QueryStructures
        CertifiedExtraction.ADT2CompileUnit.
Require Import CompileUnit2.

Require Import Benchmarks.ProcessSchedulerSetup.

(* For convenience, here is a copy of the Process Scheduler specs:

   Definition SchedulerSchema :=
     Query Structure Schema [
             relation "Processes" has schema
             <"pid" :: W, "state" :: State, "cpu" :: W>
             where (UniqueAttribute ``"pid")
     ] enforcing [].

    Definition SchedulerSpec : ADT _ :=
      QueryADTRep SchedulerSchema {
        Def Constructor0 "Init" : rep := empty,

        Def Method3 "Spawn" (r : rep) (new_pid cpu state : W) : rep * bool :=
          Insert (<"pid" :: new_pid, "state" :: state, "cpu" :: cpu> : RawTuple) into r!"Processes",

        Def Method1 "Enumerate" (r : rep) (state : State) : rep * list W :=
          procs <- For (p in r!"Processes")
                   Where (p!"state" = state)
                   Return (p!"pid");
          ret (r, procs),

        Def Method1 "GetCPUTime" (r : rep) (id : W) : rep * list W :=
            proc <- For (p in r!"Processes")
                    Where (p!"pid" = id)
                    Return (p!"cpu");
          ret (r, proc)
    }%methDefParsing. *)

(* Improve performance of general derivation *)
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

Definition CUnit
  : { env : _ &
    BuildCompileUnit2TSpec
      env
      AbsR'
      (fun r => BagSanityConditions (prim_fst r))
      (DecomposeIndexedQueryStructure' QsADTs.ADTValue _ _)
      (DecomposeIndexedQueryStructurePre' QsADTs.ADTValue _ _ _)
      (DecomposeIndexedQueryStructurePost' QsADTs.ADTValue _ _ (Scheduler_RepWrapperT _))
      (QueryStructureSchema.numQSschemaSchemas SchedulerSchema)
      "ProcessSchedulerAX"
      "ProcessSchedulerOP"
      Scheduler_coDomainWrappers
      Scheduler_DomainWrappers
      (Scheduler_RepWrapperT _)
      (Scheduler_DecomposeRep_well_behaved QsADTs.ADTValue _ _ (Scheduler_RepWrapperT _))
      SharpenedRepImpl} .
Proof.
  Time _compile QSEnv_Ax.
Defined.

Require Import DFModule.

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

Eval lazy in (methodBody "Spawn" CUnit).

(*
     = Some
         ("snd" <- "ADT"."Tuples2_findSecond"("rep", "arg");
          "test" <- "ADT"."TupleList_empty"("snd");
          If Const (Word.natToWord 32 1) = Var "test" Then
            "v1" <- Var "arg";
            "v2" <- Var "arg1";
            "v3" <- Var "arg0";
            "o1" <- Const (Word.natToWord 32 0);
            "o2" <- Const (Word.natToWord 32 1);
            "o3" <- Const (Word.natToWord 32 2);
            "vlen" <- Const (Word.natToWord 32 3);
            "tup" <- "ADT"."Tuple_new"("vlen");
            "vtmp" <- "ADT"."Tuple_set"("tup", "o1", "v1");
            "vtmp" <- "ADT"."Tuple_set"("tup", "o2", "v2");
            "vtmp" <- "ADT"."Tuple_set"("tup", "o3", "v3");
            "vtmp" <- "ADT"."Tuples2_insert"("rep", "tup");
            "tmp" <- Const (Word.natToWord 32 0);
            "test0" <- "ADT"."TupleList_empty"("snd");
            While (Var "test0" = Const (Word.natToWord 32 0))
                "head" <- "ADT"."TupleList_pop"("snd");
                "size" <- Const (Word.natToWord 32 3);
                "tmp'" <- "ADT"."Tuple_delete"("head", "size");
                "test0" <- "ADT"."TupleList_empty"("snd");
            "test0" <- "ADT"."TupleList_delete"("snd");
            __;
            "ret" <- Const (Word.natToWord 32 1)
          Else
            "tmp" <- Const (Word.natToWord 32 0);
            "test0" <- "ADT"."TupleList_empty"("snd");
            While (Var "test0" = Const (Word.natToWord 32 0))
                "head" <- "ADT"."TupleList_pop"("snd");
                "size" <- Const (Word.natToWord 32 3);
                "tmp'" <- "ADT"."Tuple_delete"("head", "size");
                "test0" <- "ADT"."TupleList_empty"("snd");
            "test0" <- "ADT"."TupleList_delete"("snd");
            __;
            "ret" <- Const (Word.natToWord 32 0)
          EndIf)%facade
     : option Stmt *)

Eval lazy in (methodBody "Enumerate" CUnit).

(*
   = Some
         ("snd" <- "ADT"."Tuples2_findFirst"("rep", "arg");
          "ret" <- "ADT"."WordList_new"();
          "test" <- "ADT"."TupleList_empty"("snd");
          While (Var "test" = Const (Word.natToWord 32 0))
              "head" <- "ADT"."TupleList_pop"("snd");
              "pos" <- Const (Word.natToWord 32 0);
              "head'" <- "ADT"."Tuple_get"("head", "pos");
              "size" <- Const (Word.natToWord 32 3);
              "tmp" <- "ADT"."Tuple_delete"("head", "size");
              "tmp" <- "ADT"."WordList_push"("ret", "head'");
              "test" <- "ADT"."TupleList_empty"("snd");
          "test" <- "ADT"."TupleList_delete"("snd");
          __)%facade
     : option Stmt *)

Eval lazy in (methodBody "GetCPUTime" CUnit).

(*
     = Some
         ("snd" <- "ADT"."Tuples2_findSecond"("rep", "arg");
          "ret" <- "ADT"."WordList_new"();
          "test" <- "ADT"."TupleList_empty"("snd");
          While (Var "test" = Const (Word.natToWord 32 0))
              "head" <- "ADT"."TupleList_pop"("snd");
              "pos" <- Const (Word.natToWord 32 2);
              "head'" <- "ADT"."Tuple_get"("head", "pos");
              "size" <- Const (Word.natToWord 32 3);
              "tmp" <- "ADT"."Tuple_delete"("head", "size");
              "tmp" <- "ADT"."WordList_push"("ret", "head'");
              "test" <- "ADT"."TupleList_empty"("snd");
          "test" <- "ADT"."TupleList_delete"("snd");
          __)%facade
     : option Stmt *)

295 derivation.
3.71 minutes Defined.
