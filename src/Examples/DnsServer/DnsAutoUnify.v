Require HintDbTactics.          (* plugin to pass a hint db to a tactic *)

Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.
        (* Fiat.Examples.DnsServer.DnsAutomation. *) (* TODO put back in *)

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

                                               (* in start honing querystructure, it inserts constraints before every insert / decision procedure *)
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > () then.. *)
                                               (* For refines decision procedure *)
    update "AddData" (this : rep, t : DNSRRecord) : bool :=
      Insert t into this!sCOLLECTIONS,

    query "Process" (this : rep, p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in this!sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsPrefix r!sNAME n) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
               (* TODO: this does not filter by matching QTYPE *)
            Then
              bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              if b                (* If the record's QNAME is an exact match  *)
              then
                unique b,                         (* only one match (unique / otherwise) *)
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ t <> CNAME ->>      (* and the query did not request a CNAME *)

                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                                                    (* ?? Shouldn't this use the sDATA ?? *)
                  ret (addan p' b)
                      (* addan : packet -> DNSRRecord -> packet *)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                (* multiple matches -- add them all as answers in the packet *)
                  ret (List.fold_left addan bfrs (buildempty p))
              else              (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records --
                 ask the authoritative servers *) (* TODO does this return one, or return all? *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

(* -------------------------------------------------------------------------------------- *)
(* Process automation moved down *)

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

      (* tac is of form [first [ x1 | ... | xn]] *)
      Ltac repeat_and_simplify tac :=
        simpl in *;
        try simplify with monad laws;
        repeat (
            try tac;
            try simpl in *;
            try simplify with monad laws
          ).

      (* For a tactic [top] that generates 1-3 subgoals, succeed only if tac (applied to each subgoal) makes progress on at least one of them. Then try cont again, keeping additional drilling/applying tac if it continues to make progress, until either tac fails everywhere or top fails.

In the other subgoals, try doing top again, then tac, then cont. Keep progress made in any of the subgoals (i.e. don't fail the whole thing because a sub-subgoal failed, even though progress was made in a subgoal). 

fails when top fails -- if top can loop forever, then this will loop forever *)
      (* TODO factor out (try cont ()) *)
      Ltac progress_subgoal top tac cont :=
        first [
          (* progresses on all subgoals no matter the number *)
            top; progress tac; try (cont ()) |
          (* progresses on 1 of 2 *)
            top; [progress tac; try (cont ()) | try (cont ())] |
            top; [try (cont ()) | progress tac; try (cont ())]

          (* progresses on 2 of 3 *)
          (* top; [progress tac; try (cont ()) | progress tac; try (cont ()) | try (cont ())] | *)
          (* top; [progress tac; try (cont ()) | try (cont ()) | progress tac; try (cont ())] | *)
          (* top; [try (cont ()) | progress tac; try (cont ()) | progress tac; try (cont ())] | *)
          (* progresses on 1 of 3 *)
          (* top; [progress tac; try (cont ()) | try (cont ()) | try (cont ())] | *)
          (* top; [try (cont ()) | progress tac; try (cont ()) | try (cont ())] | *)
          (* top; [try (cont ()) | try (cont ()) | progress tac; try (cont ())] | *)
          ].

      (* ltac is call-by-value, so wrap the cont in a function *)
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
        apply_under_subgoal ltac:(rewrite tm) ltac:(rewrite tm; try reflexivity).
      Qed.

      (* Simplify. Try all the rewrites until none work.
         If a rewrite works under a top, drill under the top and try all the rewrites until none work.
           (Do NOT drill down if no rewrite works. so: Try a drill, if failure for all rewrites, then backtrack, try a different trill. Difficult: there are multiple tops. )
         Keep doing this until none of the rewrites work at any layer of tops.
         Then, do the finishing tactics (eauto, reflexivity, various small lemmas). 
         (These should all be done on all subgoals, keeping all progress made on each one.) *)

      (* TODO what happens if I change the order? *)
      (* refine_under_bind' || refine_bind' || apply refine_If_Then_Else; *)
      (* ?? TODO *)

      Ltac srewrite_each :=
        first
          [
            setoid_rewrite (@refine_find_upperbound DNSRRecord _ _) |
            setoid_rewrite (@refine_decides_forall_In' _ _ _ _) |
            setoid_rewrite refine_check_one_longest_prefix_s |
            setoid_rewrite refine_if_If |
            setoid_rewrite refine_check_one_longest_prefix_CNAME
          ].

      Ltac finish_each :=
        first
          [
            (eapply tuples_in_relation_satisfy_constraint_specific; eauto) |
            solve [eapply For_computes_to_In; eauto using IsPrefix_string_dec] |
            reflexivity |
            higher_order_reflexivity |
            invert_For_once (* should this be outside the [first]? *)
          ].

      Ltac repeat_srewrite :=
        repeat_and_simplify srewrite_each.

      Ltac finishProcess :=
        repeat_and_simplify finish_each.
      (* --- *)

      Ltac drills :=
        first [
            subst_all; apply refine_under_bind_both; try intros | (* generates 2 cases to refine *)
            apply refine_If_Then_Else
          ].

      Ltac do_and_simplify tac :=
        tac; (* no repeat *)
        simpl in *;
        try simplify with monad laws.

      Ltac anyDrill :=
        do_and_simplify drills.

      Ltac doProcess_withLoop :=
        (* repeat_srewrite; *)
        (* this works but i should try to figure out why (repeat_srewrite; try anyDrill) works *)
        (* there should be a more concise way to alternate drilling and rewriting TODO *)
        (* i don't think this does proof search with all the drills correctly since i use [first]. it doesn't backtrack, does it? drill w/ 1 could lead to a dead end? *)
        (* putting [try anyDrill] in the second tac isn't quite right because then it won't deal with case generation correctly? what about the rewriting too? is it okay to do [try cont ()] on all the cases? actually that might be okay *)
        apply_under_subgoal ltac:(try repeat_srewrite; anyDrill) ltac:(repeat_srewrite; try anyDrill);
        finishProcess.

(* -------------------- *)
(* AddData automation *)

    (* don't rewrite inner If/Then/Else expressions *)
    (* this can be made simpler by removing context[] to only do head matches *)
    Ltac rewrite_if_head :=
      match goal with
      | [ |- context[ (refine (Bind _ (fun n => If_Then_Else _ _ _ )) _) ] ] =>
        setoid_rewrite Bind_refine_If_Then_Else
      end. 

      Ltac srewrite_manual :=
        repeat first [
                 setoid_rewrite refine_count_constraint_broken 
                                || setoid_rewrite refine_count_constraint_broken'
                                || setoid_rewrite refine_If_Then_Else_Bind
                                || rewrite_if_head
                                || setoid_rewrite refine_Count
               ]. 

      (* rewrite under bind the first time you can, then stop. otherwise fail *)
      Ltac tac_under_bind tac :=
        first [ tac |
                (apply refine_under_bind; intros); tac_under_bind tac ].

      (* only succeed if all subgoals can be solved with tac. 
intended for use as setoid_rewrite_by *)
      Ltac do_by tic tac :=
        tic; [ | solve [tac] | .. | solve [tac] ].

      Ltac srewrite_each_ad :=
        first [
            setoid_rewrite refine_count_constraint_broken |
            setoid_rewrite refine_count_constraint_broken' |
            setoid_rewrite refine_If_Then_Else_Bind |
            rewrite_if_head |
            setoid_rewrite refine_Count |
            (* TODO: always makes progress *)
            (* rewrite clear_nested_if by apply filter_nil_is_nil | *)
            do_by ltac:(setoid_rewrite refine_subcheck_to_filter) ltac:(eauto with typeclass_instances)
          ].

      Ltac repeat_srewrite_ad :=
        repeat_and_simplify srewrite_each_ad.

      Ltac drills_ad :=
        first [
            apply refine_If_Then_Else |
            subst_all; apply refine_under_bind_both; try intros
            (* apply refine_under_bind; intros *)
          ].

      Ltac anyDrill_ad :=
        do_and_simplify drills_ad.

      Ltac finish_each_ad :=
        first [reflexivity | eauto].

      Ltac finishAddData :=
        repeat_and_simplify finish_each_ad.

      Ltac doAddData_withLoop :=
        apply_under_subgoal
          ltac:(try repeat_srewrite_ad; anyDrill_ad) ltac:(repeat_srewrite_ad; try anyDrill_ad);
        finishAddData.

(* -------------------- *)
(* Unified automation *)

Check Bind_refine_If_Then_Else.
Check refine_If_Then_Else_Bind.

Ltac srewrite_each_all :=
    first [
           (* Process *)
            setoid_rewrite (@refine_find_upperbound DNSRRecord _ _) |
            setoid_rewrite (@refine_decides_forall_In' _ _ _ _) |
            setoid_rewrite refine_check_one_longest_prefix_s |
            setoid_rewrite refine_if_If |
            setoid_rewrite refine_check_one_longest_prefix_CNAME |
            (* AddData *)
            (* Why does adding these rewrites prevent other rewrites? *)
            (* Should these be drills? *)
            (* TODO messes up Process (only this one) *)
            (* setoid_rewrite refine_If_Then_Else_Bind | *)
            rewrite_if_head |
            setoid_rewrite refine_count_constraint_broken |
            setoid_rewrite refine_count_constraint_broken' |
            setoid_rewrite refine_Count |
            do_by ltac:(setoid_rewrite refine_subcheck_to_filter) ltac:(eauto with typeclass_instances)
          ].
            (* rewrite clear_nested_if by apply filter_nil_is_nil | *)

Ltac drills_each_all :=
  first [
      (* refine_under_bind' | *)
      (* refine_bind' | *)
      subst_all; apply refine_under_bind; try intros |
      apply refine_If_Then_Else 
    ].

Ltac finish_each_all :=
  first [
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
        apply_under_subgoal
          ltac:(try repeat_srewrite_fn; anyDrill_fn) ltac:(repeat_srewrite_fn; try anyDrill_fn);
        repeat_finish_fn.

Ltac doAnyAll := doAny srewrite_each_all drills_each_all finish_each_all.

(* -------------------- *)

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof. unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". { 
    (* doProcess_withLoop. *)
    doAnyAll.
}

  start_honing_QueryStructure'.

  hone method "AddData".
  {
    doAddData_withLoop.
    (* doAnyAll. (* 4 min *) *)
    (* fyi the extra beq_nat (length (filter)... is b/c clear_nested_if was removed *)
}

  GenerateIndexesForAll         (* ? in IndexSelection, see GenerateIndexesFor *)
  (* specifies that you want to use the suffix index structure TODO *)
  ltac:(CombineCase3 matchFindPrefixIndex matchEqIndex)
         ltac:(fun attrlist =>
  make_simple_indexes
    attrlist
    ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
           ltac:(CombineCase5 BuildLastFindSuffixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex))).
  (* SearchTerm and SearchUpdateTerm: efficiently do quality test on the name columns *)
  (* it figures out what datac structure to use *)
  (* BagMatchSearchTerm *)
  (* implement query as calls to abstract bag find function *)
  (* then plug in data structures that impl bag find (chooses b/t them?) *)

  (* hone constructor "Init". *)
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
   }

  (* how much of this can be factored out into the other hone? *)
  (* TODO: there seems to be refinement mixed with index choosing. need a clean separation *)
    (* hone method "AddData". *) {
    etransitivity.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    - apply refine_If_Then_Else.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                        ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                        ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        (* setoid_rewrite refine_if_If. *)
        implement_Insert_branches. (* this removes the nat choosing, so I guess the nondeterminism is okay if it involves indexed. the matching involves some of UnConstrFreshIdx *)
        (* ok, i guess getting a fresh ID for the index depends on the index specifics *)
        reflexivity.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                                      ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                             ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        setoid_rewrite refine_if_If.
        implement_Insert_branches.
        reflexivity.
    - reflexivity.              (* seems fully deterministic here *)
    - finish honing.
  }
  (* hone method "Process". *) {
    simplify with monad laws.
    implement_Query             (* in AutoDB, implement_Query' has steps *)
      ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                           ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).
    simplify with monad laws.
    simpl.
    setoid_rewrite (refine_pick_val _ H).
    simplify with monad laws.
    setoid_rewrite (@refine_filtered_list _ _ _ _).
    finish honing.
  }
  pose_headings_all.
  FullySharpenQueryStructure DnsSchema Index.
}                               (* ending "start sharpening ADT" *)

{ simpl; pose_string_ids; pose_headings_all;
  pose_search_term;  pose_SearchUpdateTerms.
  unfold name in *.
  BuildQSIndexedBags'
  ltac:(CombineCase6 BuildEarlyTrieBag BuildEarlyEqualityBag)
         ltac:(CombineCase5 BuildLastTrieBag BuildLastEqualityBag). }

{ cbv zeta; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    simpl Sharpened_Implementation;
    unfold
      Update_Build_IndexedQueryStructure_Impl_cRep,
    Join_Comp_Lists',
    GetIndexedQueryStructureRelation,
    GetAttributeRaw; simpl;
    higher_order_reflexivityT. }

Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.

(* TODO extraction, examples/messagesextraction.v *)
