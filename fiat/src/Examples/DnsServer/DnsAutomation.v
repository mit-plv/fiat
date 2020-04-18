Require Import
        Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.Computation.ListComputations
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.AuthoritativeDNSSchema
        Fiat.Examples.DnsServer.DnsLemmas.

(* Process automation *)

Ltac invert_For_once :=
  match goal with
  | [ H : computes_to (Query_For _) _ |- _ ] =>
    let H1 := fresh in
    let H2 := fresh in
    inversion H as [H1 H2]; inversion H2; clear H2
  end.

Ltac refine_under_bind' :=
  setoid_rewrite refine_under_bind; [ higher_order_reflexivity |
                                      let H := fresh in
                                      intros a H; try invert_For_once ].

Ltac refine_bind' :=
  apply refine_bind; [ idtac | unfold pointwise_relation; intros; higher_order_reflexivity ].

(* ------------------------ *)
(* AddData automation *)

Lemma eq_If_if {A}
  : forall (c : bool) (t e : Comp A),
    If c Then t Else e = if c then t else e.
Proof. intros. reflexivity. Qed.

(* don't rewrite inner If/Then/Else expressions *)
(* this can be made simpler by removing context[] to only do head matches *)
Ltac rewrite_if_head :=
  match goal with
  | [ |- context[ (refine (Bind _ (fun n => If_Then_Else _ _ _ )) _) ] ] =>
    setoid_rewrite Bind_refine_If_Then_Else
  end.

(* rewrite under bind the first time you can, then stop. otherwise fail *)
Ltac tac_under_bind tac :=
  first [ tac |
          (apply refine_under_bind; intros); tac_under_bind tac ].

(* only succeed if all subgoals can be solved with tac.
intended for use as setoid_rewrite_by *)
Ltac do_by tic tac :=
  tic; [ | solve [tac] | .. | solve [tac] ].

(* --------------------------- *)
(* General, unified automation *)

(* tac is of form [first [ x1 | ... | xn]] *)
Ltac repeat_and_simplify tac :=
  simpl in *;
  try simplify with monad laws;
  repeat (
      try tac;
      try simpl in *;
      try simplify with monad laws
    ).

(* For a tactic [top] that generates any number of subgoals, succeed only if tac (applied to each subgoal) EVENTUALLY makes progress on at least one of them [i.e. might need to drill twice in a row, the tac will work]. Then try cont again, keeping additional drilling/applying tac if it continues to make progress, until either tac fails everywhere or top fails.

Keep progress made in any of the subgoals (i.e. don't fail the whole thing because a sub-subgoal failed, even though progress was made in a subgoal).

Fails when top fails (fails iff tac never works on any subgoal) -- if top can loop forever, then this will loop forever

Subgoals: even if everything fails in the other subgoal, the tactic will succeed if progress is made in the first subgoal, because the failure will be wrapped in a [try] *)

Ltac progress_subgoal top tac cont :=
  top; (tac; try (cont ()) || (try (cont ()))).

(* Succeeds:
tac
top tac
top* tac
tac top* tac

Fails:
top (top fail)
top top (top fail)
top top top (top fail)
top*

Other cases:
tac top (top fails): keep progress up to tac
tac top (tac fails): keep progress up to tac, try cont
top tac top (top fails): keep progress up to tac
top tac top (tac fails): keep progress up to tac, try cont

All chains must end with tac, not top (because then there'd be no progress made under it) *)

(* ltac is call-by-value, so wrap the cont in a function *)
(* local definition in a_u_s *)
Ltac cont_fn top tac'' x :=
  apply_under_subgoal top tac'' with

  (* mutually recursive with progress_subgoal *)
  (* calls top on each subgoal generated, which may generate more subgoals *)
  (* fails when top fails in progress_subgoals *)
  apply_under_subgoal top tac'' :=
    progress_subgoal top tac'' ltac:(cont_fn top tac'').

Theorem testthm : forall n, n = n + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0.
Proof.
  intros.
  assert (forall y, y + 0 = y) as tm. intros. omega.
  specialize (tm n).
  apply_under_subgoal ltac:(rewrite tm) ltac:(try reflexivity).
Qed.

(* Simplify. Try all the rewrites until none work.
         If a rewrite works under a top, drill under the top and try all the rewrites until none work.
           (Do NOT drill down if no rewrite works. so: Try a drill, if failure for all rewrites, then backtrack, try a different trill. Difficult: there are multiple tops. )
         Keep doing this until none of the rewrites work at any layer of tops.
         Then, do the finishing tactics (eauto, reflexivity, various small lemmas).
         (These should all be done on all subgoals, keeping all progress made on each one.) *)

Ltac do_and_simplify tac :=
  tac; (* no repeat *)
  simpl in *;
  try simplify with monad laws.

Ltac srewrite_each_all :=
  first [
      (* Process *)
      setoid_rewrite refine_pick_eq' |
      rewrite (@refine_find_UpperBound resourceRecord _ _) |
      rewrite (@refine_decides_forall_In' _ _ _ _) |
      rewrite refine_check_one_longest_prefix_s |
      rewrite refine_if_If |
      rewrite refine_check_one_longest_prefix_CNAME |
      rewrite (@refine_filtered_list _ _ _ _) |
      setoid_rewrite refine_bind_unit |
      (* AddData *)
      (* Why does adding these rewrites prevent other rewrites? *)
      (* Should these be drills? *)
      (* TODO messes up Process (only this one) *)
      setoid_rewrite refine_If_Then_Else_Bind |
      setoid_rewrite refine_count_constraint_broken |
      setoid_rewrite refine_count_constraint_broken' |
      setoid_rewrite refine_Count |
      do_by
        ltac:(setoid_rewrite refine_subcheck_to_filter) ltac:(eauto with typeclass_instances) |
      (* set_evars needed because otherwise it rewrites forever in an evar *)
      (* hacky way to revert outer If to if *)
      try (set_evars; rewrite eq_If_if);
      set_evars; rewrite clear_nested_if by apply filter_nil_is_nil
                                                  (* set_evars; setoid_rewrite refine_if_If *) (* can be done later *)
    ].

Ltac subst_all' :=
  repeat match goal with H : _ |- _ => subst H end.

Ltac drills_each_all :=
  first [
      subst_all'; apply refine_under_bind_both; try intros; set_evars |
      subst_all'; apply refine_If_Then_Else; set_evars
    ].

Ltac finish_each_all :=
  first [
      progress subst_all' |
      (eapply tuples_in_relation_satisfy_constraint_specific; eauto) |
      solve [eapply For_computes_to_In; eauto using IsPrefix_string_dec] |
      reflexivity |
      higher_order_reflexivity |
      eauto |
      invert_For_once
    ].

Ltac doAny srewrite_fn drills_fn finish_fn :=
  let repeat_srewrite_fn := repeat_and_simplify srewrite_fn in
  let anyDrill_fn := do_and_simplify drills_fn in
  let repeat_finish_fn := repeat_and_simplify finish_fn in
  try repeat_srewrite_fn;
  apply_under_subgoal ltac:(anyDrill_fn) ltac:(repeat_srewrite_fn);
  repeat_finish_fn.

Ltac doAnyAll := doAny srewrite_each_all drills_each_all finish_each_all.
(* combinator libraries similar to (a, b, c) (d, e, f) ~> (a || d, b || e, c || f)
compose libraries together *)

(* For debugging *)
Ltac rep_rewrite := repeat_and_simplify srewrite_each_all.
Ltac do_drill := do_and_simplify drills_each_all.
Ltac rep_finish := repeat_and_simplify finish_each_all.

(* ------------------------ *)

Create HintDb refines.
(* Hint Rewrite refine_count_constraint_broken : refines. *)
Hint Rewrite refine_count_constraint_broken' : refines.

Create HintDb refines'.
(* Hint Resolve refine_count_constraint_broken : refines'. *)
Hint Resolve refine_count_constraint_broken' : refines'.

(*Ltac the_tactic :=
  let k lem := idtac lem ; fail in
  foreach [ refines ] run k.

(* this doesn't work well with the [ || ] notation *)
(* why does it need to end with fail? *)
Ltac srewrite :=
  let k lem := setoid_rewrite lem ; fail in
  foreach [ refines ] run k. *)

(* autorewrite with refines. *)
(* auto with refines'. *)
(* rewrite_strat topdown (hints refines). *)

Ltac hone_Dns :=
  start sharpening ADT;

  hone method "Process"; [ doAnyAll | ]; (* 241 seconds = 4 minutes *)
  start_honing_QueryStructure';
  hone method "AddData"; [ doAnyAll | ]; (* 202 seconds = 3.5 minutes *)
  finish_planning ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics)
                         ltac:(fun makeIndex =>
                                 GenerateIndexesForOne "Process" ltac:(fun attrlist =>
                                                                         let attrlist' := eval compute in (PickIndexes (CountAttributes' attrlist)) in makeIndex attrlist')).

Ltac srewrite_each_all ::=
     first
     [ rewrite refine_pick_eq'
     | rewrite (refine_find_UpperBound _ _)
     | rewrite (refine_decides_forall_In' _ _)
     | rewrite refine_check_one_longest_prefix_s
     | rewrite refine_if_If
     | rewrite refine_check_one_longest_prefix_CNAME
     | rewrite (refine_filtered_list _ _)
     | rewrite refine_bind_unit
     | rewrite refine_If_Then_Else_Bind
     | rewrite refine_count_constraint_broken
     | rewrite refine_count_constraint_broken'
     | rewrite refine_Count
     | do_by ltac:(rewrite refine_subcheck_to_filter)
                    ltac:(eauto  with typeclass_instances)
     | try (set_evars; rewrite eq_If_if); set_evars;
       rewrite clear_nested_if by apply filter_nil_is_nil ].

Ltac FullySharpenQueryStructure'' qs_schema Index :=
  let DelegateSigs := constr:(@Build_IndexedQueryStructure_Impl_Sigs _ (qschemaSchemas qs_schema) Index) in
  let DelegateSpecs := constr:(@Build_IndexedQueryStructure_Impl_Specs _ (qschemaSchemas qs_schema) Index) in
  let cRep' := constr:(@Build_IndexedQueryStructure_Impl_cRep _ (qschemaSchemas qs_schema) Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let ValidRefinements := fresh in
  let FullySharpenedImpl := fresh "FullySharpenedImpl" in
  match goal with
    |- @FullySharpenedUnderDelegates _ (@BuildADT ?Rep ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
    ilist_of_dep_evar n
                      (Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                      (fun D =>
                         forall idx,
                           ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                      (fun
                          (DelegateReps : Fin.t _ -> Type)
                          (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                          (Sig : consSig) =>
                          ComputationalADT.cConstructorType (cRep' DelegateReps)
                                                            (consDom Sig))
                      consSigs
                      ltac:(fun cCons =>
                              ilist_of_dep_evar n'
                                                (Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                (fun D =>
                                                   forall idx,
                                                     ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                                                (fun (DelegateReps : Fin.t _ -> Type)
                                                     (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                     (Sig : methSig) =>
                                                   ComputationalADT.cMethodType (cRep' DelegateReps)
                                                                                (methDom Sig) (methCod Sig))
                                                methSigs
                                                ltac:(fun cMeths =>
                                                        assert
                                                          ((forall
                                                               (DelegateReps : Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                               (DelegateImpls : forall idx,
                                                                   ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                               (ValidImpls
                                                                : forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
                                                                   refineADT (DelegateSpecs idx)
                                                                             (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                                               Iterate_Dep_Type_BoundedIndex
                                                                 (fun idx =>
                                                                    @refineConstructor _
                                                                                       (cRep' DelegateReps) (cAbsR' _ _ ValidImpls)
                                                                                       (consDom (Vector.nth consSigs idx))
                                                                                       (getConsDef consDefs idx)
                                                                                       (ComputationalADT.LiftcConstructor _ _ (ith  (cCons DelegateReps DelegateImpls) idx))))
                                                           * (forall
                                                                 (DelegateReps : Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                                 (DelegateImpls : forall idx,
                                                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                                 (ValidImpls
                                                                  : forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
                                                                     refineADT (DelegateSpecs idx)
                                                                               (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                                                 Iterate_Dep_Type_BoundedIndex
                                                                   (fun idx =>
                                                                      @refineMethod
                                                                        _ (cRep' DelegateReps)
                                                                        (cAbsR' _ _ ValidImpls)
                                                                        (methDom (Vector.nth methSigs idx))
                                                                        (methCod (Vector.nth methSigs idx))
                                                                        (getMethDef methDefs idx)
                                                                        (ComputationalADT.LiftcMethod (ith (cMeths DelegateReps DelegateImpls) idx))))) as ValidRefinements;
                                                        [ |
                                                          pose proof (@Notation_Friendly_SharpenFully'
                                                                        _
                                                                        _
                                                                        _
                                                                        consSigs
                                                                        methSigs
                                                                        consDefs
                                                                        methDefs
                                                                        _
                                                                        DelegateSigs
                                                                        cRep'
                                                                        cCons
                                                                        cMeths
                                                                        DelegateSpecs
                                                                        cAbsR'
                                                                        (fst ValidRefinements)
                                                                        (snd ValidRefinements))
                                                            as FullySharpenedImpl
                                                          ; clear ValidRefinements ] ))
  end;
  [ simpl; intros; split;
    [ repeat split; intros; try exact tt;
      try (etransitivity;
           [eapply (@Initialize_IndexedQueryStructureImpls_AbsR qs_schema Index)
           | ];
           cbv beta;
           unfold Initialize_IndexedQueryStructureImpls',
           CallBagImplConstructor; simpl;
           higher_order_reflexivity
          )
    | repeat split; intros; try exact tt;
      try implement_bag_methods
    ] | ];
  simpl in FullySharpenedImpl;
  fold_string_hyps_in FullySharpenedImpl;
  fold_heading_hyps_in FullySharpenedImpl;
  pose_SearchUpdateTerms_in FullySharpenedImpl;
  pose_search_term_in FullySharpenedImpl;
  let impl := fresh "impl" in
  match type of FullySharpenedImpl with
    @FullySharpenedUnderDelegates _ _ ?Impl =>
    set (impl := Impl) in *
  end;
  cbv beta in *; simpl in impl;
  let impl' :=
      match goal with
        |- @FullySharpenedUnderDelegates _ _ ?Impl => Impl
      end in
  (* Not having to worry about re-typing the body during zeta-expansion
     yields a 30x speedup.
   *)
  assert (True) by
      (clear FullySharpenedImpl; zeta_expand_all impl; unify impl impl'; econstructor);
  exact FullySharpenedImpl.

Ltac Finish_Master BuildEarlyBag BuildLastBag :=
  eapply FullySharpened_Finish;
  [pose_headings_all;
   match goal with
   | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
     FullySharpenQueryStructure'' Schema Indexes
   end
  | simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    match goal with
      |- context [ @Build_IndexedQueryStructure_Impl_Sigs _ ?indices ?SearchTerms _] => try unfold SearchTerms
    end;
    BuildQSIndexedBags' BuildEarlyBag BuildLastBag
  | cbv zeta; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    simpl Sharpened_Implementation;
    unfold
      Update_Build_IndexedQueryStructure_Impl_cRep,
    Join_Comp_Lists',
    GetIndexedQueryStructureRelation,
    GetAttributeRaw; simpl;
    higher_order_reflexivityT ].

Ltac Focused_refine_TopMost_Query :=
  match goal with
  | |- refine (Bind (Count (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_Count ResultT body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (MaxN (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_MaxN body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (SumN (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_SumN body') at 1;
                       clear refine_body' ] )
  | |- refine (Bind (MaxZ (@Query_For ?ResultT ?body)) ?k) _ =>

    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_MaxZ body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (SumZ (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_SumZ body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (Max (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_Max body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (Sum (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_Sum body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (@Query_For ?ResultT ?body) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       clear refine_body' ] )

  end.

Ltac implement_TopMost_Query' k k_dep:=
  Focused_refine_TopMost_Query;
  [ (* Step 1: Implement [In / Where Combinations] by enumerating and joining. *)
    implement_In_opt;
    (* Step 2: Move filters to the outermost [Join_Comp_Lists] to which *)
    (* they can be applied. *)
    repeat progress distribute_filters_to_joins;
    (* Step 3: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep
  |
  ]; pose_string_hyps; pose_heading_hyps.

Ltac implement_TopMost_Query CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  implement_TopMost_Query'
    ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex)
           ltac:(find_simple_search_term_dep makeClause_dep EarlyIndex_dep LastIndex_dep).

Ltac implement_insert' CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  first
    [simplify with monad laws; simpl
    | simpl; rewrite !map_app
    | simpl; rewrite !map_length
    | simpl; rewrite !app_nil_r
    | simpl; rewrite !map_map
    | simpl; rewrite !filter_map
    | simpl; setoid_rewrite refine_if_Then_Else_Duplicate
    | simpl; setoid_rewrite refine_If_Then_Else_Bind
    | simpl; setoid_rewrite refine_If_Opt_Then_Else_Bind
    | match goal with
        H : DelegateToBag_AbsR ?r_o ?r_n
        |- context[Pick (fun idx => UnConstrFreshIdx (GetUnConstrRelation ?r_o ?Ridx) idx)] =>
        let freshIdx := fresh in
        destruct (exists_UnConstrFreshIdx H Ridx) as [? freshIdx];
        setoid_rewrite (refine_Pick_UnConstrFreshIdx H Ridx freshIdx)
      end
    | implement_QSDeletedTuples ltac:(find_simple_search_term
                                        CreateTerm EarlyIndex LastIndex)
    | implement_TopMost_Query CreateTerm EarlyIndex LastIndex
                              makeClause_dep EarlyIndex_dep LastIndex_dep
    | implement_Pick_DelegateToBag_AbsR ].

Ltac master_implement_drill CreateTerm EarlyIndex LastIndex :=
  subst_refine_evar;
  first
    [ eapply refine_BagADT_QSInsert'; try eassumption; intros
    | implement_UpdateUnConstrRelationDeleteC ltac:(find_simple_search_term
                                                      CreateTerm EarlyIndex LastIndex);
      intros
    | eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else;
      [intro; set_refine_evar | set_refine_evar ] ].

Ltac implement_insert'' :=
  implement_insert'
    ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
           ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                  ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                         ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                                ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                       ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).

Ltac doOne srewrite_fn drills_fn finish_fn :=
  first [srewrite_fn | drills_fn | finish_fn].

Ltac drop_constraintsfrom_DNS :=
  eapply SharpenStep;
  [ match goal with
      |- context [ @BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
      eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
      [ repeat (first [eapply refine_Constructors_nil
                      | eapply refine_Constructors_cons;
                        [ simpl; intros;
                          match goal with
                          | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                          | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                          | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                          | |- refine _ (?E _) => let H := fresh in set (H := E)
                          | |- refine _ (?E) => let H := fresh in set (H := E)
                          | _ => idtac
                          end;
                          (* Drop constraints from empty *)
                          try apply Constructor_DropQSConstraints;
                          cbv delta [GetAttribute] beta; simpl
                        | ] ])
      | repeat (first [eapply refine_Methods_nil
                      | eapply refine_Methods_cons;
                        [ simpl; intros;
                          match goal with
                          | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                          | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                          | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                          | |- refine _ (?E _) => let H := fresh in set (H := E)
                          | |- refine _ (?E) => let H := fresh in set (H := E)
                          | _ => idtac
                          end;
                          cbv delta [GetAttribute] beta; simpl | ]
      ])]
    end | ].
