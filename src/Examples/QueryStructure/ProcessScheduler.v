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
  Def ADT {
    rep := QueryStructure SchedulerSchema,

    Def Constructor0 "Init" : rep := empty,,

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
Print PartialSchedulerImpl.

Time Definition SchedulerImplSpecs :=
  Eval simpl in (Sharpened_DelegateSpecs (snd (projT1 SharpenedScheduler))).
Print SchedulerImplSpecs.

(*Print MostlySharpened.

Lemma GetRelation_Empty_eq  :
  forall MySchema R,
    GetRelation (QSEmptySpec MySchema) R = (Empty_set _).
Proof.
  intros; unfold GetRelation, QSEmptySpec.
  rewrite Build_EmptyRelation_IsEmpty; reflexivity.
Qed.

Lemma GetUnConstrRelation_Empty_eq  :
  forall MySchema R,
    GetUnConstrRelation (DropQSConstraints (QSEmptySpec MySchema)) R = (Empty_set _).
Proof.
  intros; rewrite GetRelDropConstraints; apply GetRelation_Empty_eq.
Qed.

Lemma wones_max :
  forall n w, ~ Word.wlt (Word.wones n) w.
Proof.
  admit.
Qed.

Lemma wones_eq :
  forall n w, ~ Word.wlt w (Word.wones n) -> w = Word.wones n.
Proof.
  admit.
Qed.

Lemma wlt_S :
  forall n w,
    Word.wlt w (Word.wplus (Word.natToWord n 1) w).
Proof.
  admit.
Qed.

Lemma wlt_trans :
  forall n (w w' w'' : Word.word n),
    Word.wlt w w'
    -> Word.wlt w' w''
    -> Word.wlt w w''.
Proof.
  admit.
Qed.

Lemma refine_If_Opt_Then_Else_cond {A B}
  : forall (c : option B) (e e': Comp A) (t t' : B -> Comp A),
    (forall b, c = Some b -> refine (t b) (t' b))
    -> (c = None -> refine e e')
    -> refine (Ifopt c as b' Then t b' Else e)
              (Ifopt c as b' Then t' b' Else e').
Proof.
  intros; destruct c; simpl in *; eauto.
Qed.

Definition If_OptC_Then_Else {A B : Type}
           (i : Ensemble A)
           (t : A -> Comp B)
           (e : Comp B) :=
  b <- {b | (forall b', b = Some b' -> i b') /\
            ((forall b', ~ i b') -> b = None)};
  If_Opt_Then_Else b t e.

Locate "Ifopt _ as _ Then _ Else _".

Definition GetRelationBnd
           (QSSchema : QueryStructureSchema)
           (qs : QueryStructure QSSchema)
           (idx : BoundedIndex (QSschemaNames QSSchema))
  : @IndexedEnsemble (@RawTuple (GetNRelSchemaHeading (qschemaSchemas QSSchema) (ibound (indexb idx)))) := @GetRelation QSSchema qs (ibound (indexb idx)).

Notation "'IfoptC' i 'as' a 'Then' t 'Else' e" :=
  (If_OptC_Then_Else (fun a => i) (fun a => t) e) (at level 90).

(* This scheduler variant allows new processes to be inserted, requiring a cache. *)
Definition SpawningSchedulerSpec : ADT _ :=
  Def ADrep := QueryStructure SchedulerSchema,
    Def Constructor0 "Init" : rep := empty,

    Def Method1 "Spawn" (r : rep) (cpu : W) : rep * bool :=
      IfoptC (forall proc, IndexedEnsemble_In (GetRelationBnd r ``"Processes") proc
                           -> (new_pid <> proc!"pid")) as new_pid
      Then Insert (<"pid" :: new_pid, "state" :: SLEEPING, "cpu" :: cpu> : RawTuple) into r!"Processes"
      Else ret (r, false),

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

(*Definition SpawningSharpenedScheduler :
  MostlySharpened SchedulerSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  {
    (* The tactics don't handle insertions inside of conditionals, so we instead manually *)
    (* drill inside the conditional and apply the tactic. *)
    unfold If_OptC_Then_Else.
    simplify with monad laws.
    etransitivity.
    eapply refine_under_bind; intros.
    set_evars; setoid_rewrite refine_If_Opt_Then_Else_Bind.
    unfold H2; apply refine_If_Opt_Then_Else.
    - intro; set_evars.
      drop_constraints_from_insert.
    - simplify with monad laws.
      simpl; refine pick val _; eauto.
      simplify with monad laws; finish honing.
    - simpl.
      unfold GetRelationBnd.
      rewrite <- GetRelDropConstraints; rewrite H.
      finish honing.
  }
  (* The next step is to cache the current pid. *)
  hone representation using
       (ADTCache.cachedRep_AbsR ((fun (r : UnConstrQueryStructure SchedulerSchema) max_pid =>
             match max_pid with
             | Some pid =>
               forall proc, IndexedEnsemble_In (GetUnConstrRelation r Fin.F1) proc
                            -> (Word.wlt (sz := 32) (GetAttributeRaw proc Fin.F1) pid)
             | None =>
               ~ exists pid,
                 forall proc, IndexedEnsemble_In (GetUnConstrRelation r Fin.F1) proc
                              -> (Word.wlt (GetAttributeRaw proc Fin.F1) pid)
             end)));
    [ setoid_rewrite ADTCache.refine_pick_cachedRep .. | ].
  - apply refine_under_bind; intros.
    computes_to_inv; subst.
    refine pick val (Some (Word.natToWord 32 0)).
    simplify with monad laws; finish honing.
    setoid_rewrite GetUnConstrRelation_Empty_eq.
    unfold IndexedEnsemble_In; intros; destruct_ex; inversion H0.
    - unfold If_OptC_Then_Else.
    simplify with monad laws.
    rewrite (proj1 H0).
    refine pick val (ADTCache.cachedVal r_n).
    simplify with monad laws.
    setoid_rewrite refine_If_Opt_Then_Else_Bind.
    unfold H; eapply refine_If_Opt_Then_Else_cond; set_evars.
    + intros.
      simplify with monad laws.
      repeat setoid_rewrite refine_if_If.
      setoid_rewrite refine_If_Then_Else_Bind.
      unfold H1.
      apply refine_under_bind; intros.
      eapply refine_under_bind; intros.
      apply refine_If_Then_Else.
      setoid_rewrite refine_if_If.
      rewrite refine_If_Then_Else_Bind.
      apply refine_If_Then_Else.
      simplify with monad laws.
      simpl.
      * refine pick val (match ADTCache.cachedVal r_n with
                       | Some v =>
                         if (Word.wlt_dec v (Word.wones _)) then
                           Some (Word.wplus (Word.natToWord 32 1) v)
                         else None
                       | None => None
                       end).
        simplify with monad laws.
        finish honing.
        rewrite H2.
        find_if_inside.
        intros; unfold IndexedEnsemble_In in H5; destruct_ex.
        rewrite get_update_unconstr_eq in H5.
        destruct H5; subst; eauto.
        injection H5; intros; subst.
        unfold GetAttributeRaw, ith2, Vector.caseS, AttrList,
        ilist2_hd, prim_fst, icons2.
        apply wlt_S.
        eapply wlt_trans.
        destruct H0.
        rewrite H2 in H6.
        eapply H6.
        rewrite H0.
        econstructor; unfold In; eauto.
        apply wlt_S.
        intro; destruct_ex.
        eapply wones_max with (n := 32).
        apply wones_eq in n; erewrite <- n.
        eapply (H5 (icons2 _ (icons2 SLEEPING (icons2 d inil2)))).
        econstructor.
        rewrite get_update_unconstr_eq.
        econstructor; reflexivity.
      * simplify with monad laws; simpl.
        refine pick val (Some b).
        simplify with monad laws; finish honing.
        destruct H0; subst; rewrite H2 in H5; eauto.
      * simplify with monad laws; simpl.
        refine pick val (Some b).
        simplify with monad laws; finish honing.
        destruct H0; subst; rewrite H2 in H5; eauto.
    + intros.
      simplify with monad laws; simpl.
      refine pick val None.
      simplify with monad laws; finish honing.
      destruct H0; subst; rewrite H2 in H3; eauto.
    + destruct H0; subst.
      revert H1; case_eq (ADTCache.cachedVal r_n); intros.
      * split.
        { intros; injections; intuition eauto; subst.
          apply H1 in H3; subst.
          eapply Word.eq_le; try eassumption.
          reflexivity. }
        { intros. exfalso; eapply (H2 w).
          intros.
          apply H1 in H3.
          intro; subst.
          eapply Word.eq_le; try eassumption.
          reflexivity. }
      * split.
        { intros; discriminate. }
        { reflexivity. }
  - simplify with monad laws.
    destruct H0; subst.
    unfold H; apply refine_under_bind; intros.
    refine pick val _; eauto.
    simplify with monad laws; finish honing.
  - simplify with monad laws.
    destruct H0; subst.
    unfold H; apply refine_under_bind; intros.
    refine pick val _; eauto.
    simplify with monad laws; finish honing.
  (* Now we implement the various set operations using BagADTs. *)
  (* Again, our tactics don't play nicely with the cache in the spec, so *)
  (* we have to manually massage the goals to get things in the right form. *)
  (* A little more tactic support in the caching refinement should make this *)
  (* much nicer. *)
  - let attrlist := constr:({)|
      prim_fst := [ ("EqualityIndex", Fin.F1);
                    ( "EqualityIndex", Fin.FS (@Fin.F1 1) ) ];
      prim_snd := () |} in
    let sch' := eval simpl in (qschemaSchemas SchedulerSchema) in
        makeIndex' sch' attrlist
                   ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                          ltac:(LastCombineCase5 BuildLastEqualityIndex)
                   ltac:(fun l =>
                           pose_string_hyps; pose_heading_hyps;
                         let index := fresh "Index" in
                         pose l as index;
                         simpl in index;
                         pose_string_hyps_in index; pose_heading_hyps_in index;
                         pose_search_term_in index;
                         pose_SearchUpdateTerms_in index).
    hone representation using (fun r_o r_n => @DelegateToBag_AbsR SchedulerSchema Index (ADTCache.origRep r_o) (ADTCache.origRep r_n) /\ ADTCache.cachedVal r_o = ADTCache.cachedVal r_n).
    + simplify with monad laws.
      refine pick pair.
      initializer.
      make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex

    + simplify with monad laws; simpl.
      refine pick val (Some w).
      simplify with monad laws; finish honing.
      eauto.
    + cbv beta.

      intro; destruct_ex.
      simpl.
      rewrite get_update_unconstr_eq in H6; destruct H6.
      destruct H5; subst; eauto.
      injection H5; intros; subst.
      apply n.
      unfold GetAttributeRaw, ith2, Vector.caseS, AttrList,
      ilist2_hd, prim_fst, icons2 in H7.
      rewrite H0 in H4; injection H4; intros; subst.
      eauto.


    eapply n.
    rewrite H0 in H4; injection H4; intros; subst.


    admit.

    simpl.

    simpl GetAttributeRaw.


    pose @get_update_unconstr_iff. in H6.
    unfold GetUnConstrRelation in H6; simpl.
    simpl in H6.
    setoid_rewrite refine_if_If.
    apply refine_under_bind; intros.
    refine pick val (ADTCache.cachedVal r_n).
    simplify with monad laws.
    finish honing.
    rewrite H0; intros; eapply H1.
    etransitivity.
    eapply refine_Pick_If_Then_Opt.


with
                     | Some v =>
                       if (Word.wlt_dec v (Word.wones _)) then
                         Some (Word.wplus v (Word.natToWord 32 1))
                       else None
                     | None => None
                     end).

    try match goal with
        H0 := _,
        H1 : ADTCache.cachedRep_AbsR _ _ _ |- _ =>
              let H' := fresh in
              destruct H1 as [H' ?]; rewrite H' in *;
              subst H0; apply refine_under_bind
      end.
      Focus 2.
  match goal with
        H0 := _,
        H1 : ADTCache.cachedRep_AbsR _ _ _ |- _ =>
              let H' := fresh in
              destruct H1 as [H' ?]; rewrite H' in *;
              subst H0
      end.
  destruct H0; subst.

  eapply refine_under_bind.
  etransitivity; [apply refine_under_bind | ] .. | ].
  Print LoadPath.
  Focus 2.
  etransitivity.
  apply refine_under_bind.
  unfold H.
  eapply refine_under_bind.
  apply refine_under_bind; intros.
  rewrite (@refine_pick_val _ (Some (Word.natToWord 32 0))).

  Ltac addCache cacheSpec' :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_refine_All with (AbsR := _);
    [ repeat (first [eapply refine_Constructors_nil
                    | eapply refine_Constructors_cons;
                      [ intros;
                        eapply ADTCache.refine_addCacheToConstructor_step with (cacheSpec := cacheSpec');
                        simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E) => is_evar E; let H := fresh in set (H := E)
                        | _ => idtac
                        end | ] ])
    | repeat (first [eapply refine_Methods_nil
                    | eapply refine_Methods_cons;
                      [ intros;
                        eapply ADTCache.refine_addCacheToMethod_step with (cacheSpec := cacheSpec');
                        unfold ADTCache.addCacheToMethod; simpl; intros;
                        match goal with
                        |  |- refine _ (?E _ _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _ _ ) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _ _) => is_evar E; let H := fresh in set (H := E)
                        |  |- refine _ (?E _) => is_evar E; let H := fresh in set (H := E)
                          | _ => idtac
                        end | ]
                    ])]
  | ].
  addCache (fun (r : QueryStructure SchedulerSchema) max_pid =>
             match max_pid with
             | Some pid =>
               forall proc, IndexedEnsemble_In (GetRelation r Fin.F1) proc
                            -> (Word.wlt (sz := 32) (GetAttributeRaw proc Fin.F1) pid)
             | None => ~ exists pid proc,
                   IndexedEnsemble_In (GetRelation r Fin.F1) proc
                   /\ (GetAttributeRaw proc Fin.F1) <> pid
             end).
  Focus 2.
  unfold refineMethod_eq; simpl; intros.
  eapply addCacheToConstructor


  (exists b', i b' /\ b = Some b') /\
            ((forall b', ~ i b') -> b = None)}


  hone method "Spawn".
  { simpl in *|-.


    Locate Ltac start_honing_QueryStructure'.

  Print UnConstrQueryStructure.

  Definition DelegateToBag_AbsR'
             (qs_schema : RawQueryStructureSchema)
             (r_o r_n : UnConstrQueryStructure qs_schema) :=
    forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
      Same_set _ (GetUnConstrRelation r_o idx)
               (GetUnConstrRelation r_n idx).

  eapply FullySharpened_Finish.
  Print refineADT.
  eapply SharpenFully with (cAbsR := DelegateToBag_AbsR' _).
  econstructor.
  hone representation using (@DelegateToBag_AbsR sch index))


  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics). *)
  master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics).

Time Defined.
(* 1336MB *)
Time Definition MessagesImpl : ComputationalADT.cADT MessagesSig :=
  Eval simpl in (projT1 SharpenedMessages).
Print MessagesImpl. *)
 *)
