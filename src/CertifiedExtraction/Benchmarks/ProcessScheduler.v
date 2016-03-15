Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Definition State := W.
Definition SLEEPING : State := Word.natToWord 32 0.
Definition RUNNING : State  := Word.natToWord 32 1.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.

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
              }%methDefParsing.

Definition SharpenedScheduler :
  MostlySharpened SchedulerSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  hone method "Spawn".
  { setoid_rewrite UniqueAttribute_symmetry.
    setoid_rewrite (@refine_uniqueness_check_into_query' SchedulerSchema Fin.F1 _ _ _ _).
    setoid_rewrite refine_For_rev.
    setoid_rewrite refine_Count.
    simplify with monad laws; simpl in *; subst.
    setoid_rewrite refine_pick_eq'.
    setoid_rewrite refine_bind_unit.
    setoid_rewrite refine_If_Then_Else_Duplicate.
    finish honing. }
  (* Now we implement the various set operations using BagADTs. *)
  - make_simple_indexes
      {|
      prim_fst := [ ("EqualityIndex", Fin.FS (@Fin.F1 1) );
                    ( "EqualityIndex", Fin.F1) ];
      prim_snd := () |}
               ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                      ltac:(LastCombineCase5 BuildLastEqualityIndex).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + setoid_rewrite refine_For_rev; simplify with monad laws.
      plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + setoid_rewrite refine_For_rev; simplify with monad laws.
      plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + hone method "Spawn".
      { subst; simplify with monad laws.
        unfold GetAttributeRaw at 1.
        simpl; unfold ilist2_hd at 1; simpl.
        unfold H1; apply refine_under_bind.
        intros; set_evars.
        setoid_rewrite refine_pick_eq'; simplify with monad laws.
        rewrite app_nil_r, map_map; simpl.
        unfold ilist2_hd; simpl; rewrite map_id.
        repeat setoid_rewrite refine_If_Then_Else_Bind.
        repeat setoid_rewrite refineEquiv_bind_unit; simpl.
        setoid_rewrite refineEquiv_bind_bind.
        setoid_rewrite refineEquiv_bind_unit.
        rewrite (CallBagFind_fst H0); simpl.
        finish honing.
      }
      hone method "Enumerate".
      { subst; simplify with monad laws.
        unfold H1; apply refine_under_bind.
        intros; set_evars; simpl in *.
        rewrite (CallBagFind_fst H0).
        setoid_rewrite refine_pick_eq'; simplify with monad laws.
        simpl; rewrite app_nil_r, map_map, <- map_rev.
        unfold ilist2_hd; simpl.
        finish honing.
      }
      hone method "GetCPUTime".
      { subst; simplify with monad laws.
        unfold H1; apply refine_under_bind.
        intros; set_evars; rewrite (CallBagFind_fst H0); simpl in *.
        setoid_rewrite refine_pick_eq'; simplify with monad laws.
        simpl; rewrite app_nil_r, map_map, <- map_rev.
        unfold ilist2_hd; simpl.
        finish honing.
      }
      simpl.
      eapply reflexivityT.
  - unfold CallBagFind, CallBagInsert.
    pose_headings_all;
      match goal with
      | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
        FullySharpenQueryStructure Schema Indexes
      end.
Defined.

Time Definition PartialSchedulerImpl : ADT _ :=
  Eval simpl in (fst (projT1 SharpenedScheduler)).

Time Definition SchedulerImplSpecs :=
  Eval simpl in (Sharpened_DelegateSpecs (snd (projT1 SharpenedScheduler))).

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction
        CertifiedExtraction.Extraction.QueryStructures
        CertifiedExtraction.ADT2CompileUnit.

Definition CUnit
  : { env : _ &
    BuildCompileUnit2TSpec
      env
      (AbsR (fst (projT2 SharpenedScheduler)))
      (fun r => BagSanityConditions (prim_fst r))
      (DecomposeIndexedQueryStructure' QsADTs.ADTValue _ _)
      (DecomposeIndexedQueryStructurePre' QsADTs.ADTValue _ _ _)
      (DecomposeIndexedQueryStructurePost' QsADTs.ADTValue _ _ (Scheduler_RepWrapperT _))
      (QueryStructureSchema.numQSschemaSchemas SchedulerSchema)
      "foo"
      "bar"
      Scheduler_coDomainWrappers
      Scheduler_DomainWrappers
      (Scheduler_RepWrapperT _)
      (Scheduler_DecomposeRep_well_behaved QsADTs.ADTValue _ _ (Scheduler_RepWrapperT _))
      (fst (projT2 SharpenedScheduler))} .
Proof.
  Time _compile QSEnv_Ax.
Time Defined.

(* Set Printing All. *)

Redirect "SpawnSmall" Eval compute in (projT1 CUnit).
Redirect "EnumerateSmall" Eval compute in (projT1 (progOKs (Fin.FS Fin.F1))).
Redirect "GetCPUTimeSmall" Eval compute in (projT1 (progOKs (Fin.FS (Fin.FS Fin.F1)))).
