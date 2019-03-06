Require Import Benchmarks.ProcessSchedulerSetup.

(** This file demonstrates the extraction from a Fiat ADT to a Facade
    “CompileUnit”. For convenience, here is a copy of the Process Scheduler
    specs:

        Definition SchedulerSchema          Def ADT Schema  rep := QueryStructure Structure,

                  relation "Processes" has schema
                  <"pid" :: W, "state" :: State, "cpu" :: W>
                  where (UniqueAttribute ``"pid")
          ] enforcing [].

         Definition SchedulerSpec : ADT _ :=
            Def ADT
             {
             rep := QueryStructure SchedulerSchema,

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
         }%methDefParsing.

     We have added the output of each of the three “Compute” calls below;
     running the example up to that point takes about 6 minutes on a modern machine. *)

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
  Time _compile QSEnv_Ax.          (* 228s *)
Time Defined.                            (* 185s *)

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
