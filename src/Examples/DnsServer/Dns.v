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
        Fiat.QueryStructure.Automation.QSImplementation
        Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "AddData" : rep x DNSRRecord -> rep x bool,
      Method "Process" : rep x packet -> rep x packet
    }.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddData" (this : rep, t : DNSRRecord) : bool :=
      Insert t into this!sCOLLECTIONS,

      (* this server changes packet in the way that buildempty does *)
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

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

  unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    Ltac invert_For_once :=
      match goal with
      | [ H : computes_to (Query_For _) _ |- _ ] =>
        let H1 := fresh in
        let H2 := fresh in
        inversion H as [H1 H2]; inversion H2; clear H2
      end.

    (* Ltac refine_under_bind' := *)
    (*   setoid_rewrite refine_under_bind; [ higher_order_reflexivity | *)
    (*                                       let H := fresh in *)
    (*                                       intros a H; try invert_For_once ]. *)

Ltac refine_bind' :=
  apply refine_bind; [ idtac | unfold pointwise_relation; intros; higher_order_reflexivity ].
  Locate refine_bind.
    simpl in *. simplify with monad laws.
    
    setoid_rewrite (@refine_find_upperbound DNSRRecord _ _).
    setoid_rewrite (@refine_decides_forall_In' _ _ _ _).

    (* TODO *)
    setoid_rewrite refine_If_Then_Else_Bind.
    (* used in AddData; causes this one to fail due to rets *)
    Check refine_under_bind_both.

    Print Ltac subst_all.
    (* subst_all; apply refine_under_bind_both. higher_order_reflexivity. intros.  *)
    (* not clear which case we should be working on, and if we use two different tactics, it's the same as having them split before... *)
    (* i guess it's okay to try refinements on both cases! *)
    (* subst_all; apply refine_under_bind_both. intros. *)
    subst_all; apply refine_under_bind_both; [ higher_order_reflexivity | intros ]. 
    (* if you don't want to work on the first case *)
     (* setoid_rewrite refine_if_If. *)
    (* does this terminate? takes 2 min and fails; might be causing the long runtimes *)
    (* subst_all; *) apply refine_under_bind_both; [ idtac | intros; higher_order_reflexivity ].

    apply refine_If_Then_Else.
    {
      simplify with monad laws.
      setoid_rewrite refine_check_one_longest_prefix_s.
      simplify with monad laws.
      setoid_rewrite refine_if_If;
      setoid_rewrite refine_check_one_longest_prefix_CNAME.
      reflexivity.

      (* TODO: bake in inversion in the finish tactic *)
      inversion H. inversion H0. clear H0.
      - eapply (tuples_in_relation_satisfy_constraint_specific n). eauto.
      - eapply For_computes_to_In; eauto using IsPrefix_string_dec.
      - eapply For_computes_to_In; eauto using IsPrefix_string_dec.
    }
   { reflexivity. }
}
(*
    simpl in *. simplify with monad laws.

    setoid_rewrite (@refine_find_upperbound DNSRRecord _ _).
    setoid_rewrite (@refine_decides_forall_In' _ _ _ _).

    Print Ltac subst_all.
    subst_all; apply refine_under_bind; intros. (* skips to the end *)
    (* setoid_rewrite refine_if_If. *)
    (* does this terminate? takes 2 min and fails; might be causing the long runtimes *)
    refine_bind'.

    apply refine_If_Then_Else.
    {
      simplify with monad laws.
      setoid_rewrite refine_check_one_longest_prefix_s.
      simplify with monad laws.
      setoid_rewrite refine_if_If.
      Check refine_check_one_longest_prefix_CNAME.
      setoid_rewrite refine_check_one_longest_prefix_CNAME.
      reflexivity.

      (* TODO: bake in inversion in the finish tactic *)
      inversion H. inversion H0. clear H0.
      - eapply (tuples_in_relation_satisfy_constraint_specific n). eauto.
      - eapply For_computes_to_In; eauto using IsPrefix_string_dec.
      - eapply For_computes_to_In; eauto using IsPrefix_string_dec.
    }
   { reflexivity. }
*)


(*    simplify with monad laws.
    (* Find the upperbound of the results. *)
    etransitivity.
    apply refine_under_bind; intros. (* rewrite? *)
    (* rewrite map_app, map_map, app_nil_r, map_id; simpl. *)
    etransitivity.
    apply refine_bind.
    match goal with
      |- refine _ (?H) => let id := fresh in set (id := H) in *
    end. (* rename ?whatever to H(number) *)
    (* Should honing if branches also be their own tactic? *)
    etransitivity.
    apply refine_If_Then_Else.
    match goal with
      |- context [ [[r in ?A | upperbound ?f ?l r]] ] =>
      pose (@refine_find_upperbound _ f A)
    end.
    etransitivity.
    { apply refine_bind; eauto.
      intro; higher_order_reflexivity. }

    setoid_rewrite (@refine_decides_forall_In' _ _ _ _).
    simplify with monad laws.
    etransitivity.
    Check refine_bind.
    (* implement decision procedure *)
    {
      apply refine_bind;
      [ apply refine_check_one_longest_prefix_s
      | intro; higher_order_reflexivity ].
      intros. clear H. clear H1. unfold get_name.
      eapply For_computes_to_In in H0.
      inv H0.
      - apply H.
      - pose proof IsSuffix_string_dec. intros. auto.
      - auto.
    }
    simplify with monad laws.
    setoid_rewrite refine_if_If.
    apply refine_If_Then_Else.
    etransitivity.
    { (* Locate "unique". *)

      (* setoid_rewrite refine_check_one_longest_prefix_CNAME. *)
      (* simplify with monad laws. *)
      (* reflexivity. *)

      apply refine_bind;        (* rewrite instead of apply *)
      [ eapply refine_check_one_longest_prefix_CNAME | intro; higher_order_reflexivity ].

      inversion H0.
      inversion H2. clear H2.
      - eapply tuples_in_relation_satisfy_constraint_specific.
        Check refine_check_one_longest_prefix_CNAME. apply H0.
      (* exciting! *)
      -
        clear H.
        intros.
        instantiate (1 := (qname (questions n))).
        eapply For_computes_to_In in H0.
        inv H0. unfold get_name.
      + apply H2.
      + pose proof IsSuffix_string_dec. intros. auto.
      + auto.
    }
    simplify with monad laws.
    reflexivity. reflexivity.

    reflexivity. subst H1; reflexivity.
    unfold pointwise_relation; intros; higher_order_reflexivity.
    finish honing. finish honing. *)

(* Print Ltac *)
  start_honing_QueryStructure'.

  hone method "AddData".
  { 
    (* whatever data-integrity constraints there are on the relation, they get automatically added as checks/decision procedures on this (the mutator)  *)
    simpl in *.
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    setoid_rewrite refine_Count.
   
    Check refine_If_Then_Else_Bind.
    setoid_rewrite refine_If_Then_Else_Bind. simpl in *.
    (* need to do this so we can use refine_subcheck_to_filter on BOTH the [For]s (so they're sequential) *)

    subst_all; apply refine_under_bind_both; [reflexivity | intros].
    apply refine_If_Then_Else; simplify with monad laws.
    {      
      (* subst_all; apply refine_under_bind_both; [idtac | intros]. *)
      subst_all; apply refine_under_bind_both; [reflexivity | intros].
      (* ?8535 matches any rewrite rule *)
      (* progress (rewrite clear_nested_if by apply filter_nil_is_nil). *)
      (* progress (rewrite clear_nested_if by apply filter_nil_is_nil). *)
      setoid_rewrite refine_subcheck_to_filter; eauto.
      simplify with monad laws.
      Check clear_nested_if.
      unfold dec in *. simpl in *.
      (* Set Printing All. auto. *)
      Check clear_nested_if.

  Lemma eq_If_if {A}
  : forall (c : bool) (t e : Comp A),
      If c Then t Else e = if c then t else e.
  Proof.
    intros.
    reflexivity.
  Qed.

Lemma clear_nested_If :
  forall {A : Type} (c c' : bool) (t e e' : A),
    (c = true -> c' = true) ->
    (If c Then If c' Then t Else e Else e') = (If c Then t Else e').
Proof.
  intros. apply clear_nested_if. auto.
Qed. 
      set_evars; rewrite clear_nested_if by apply filter_nil_is_nil. (* rewrites in right place *)
      (* Need to replace if with If for implement_bag_methods to work. *)
      set_evars; setoid_rewrite refine_if_If.
      simpl in *.
      higher_order_1_reflexivity.
      (* clears goal, but H1 is still in the context, and it still has the
         For/Where/Return ~> _ unimplemented *)
      eauto with typeclass_instances.
    } 
    { reflexivity. }
  } 

(*
{
      simpl in *.
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    setoid_rewrite refine_Count.

    Check refine_If_Then_Else_Bind.
    setoid_rewrite refine_If_Then_Else_Bind. simpl in *.

    Check Bind_refine_If_Then_Else.
    (* turns the entire thing into if/then/else toplevel *)
    subst_all; apply refine_under_bind_both; [reflexivity | intros].
    (* simplify with monad laws. *)
    apply refine_If_Then_Else; simplify with monad laws.
    {
      subst_all; apply refine_under_bind_both; [reflexivity | intros].
      (* ?8535 matches any rewrite rule *)
      subst_all.
      (* progress (rewrite clear_nested_if by apply filter_nil_is_nil). *)
      (* progress (rewrite clear_nested_if by apply filter_nil_is_nil). *)
      setoid_rewrite refine_subcheck_to_filter; eauto.
      simplify with monad laws.
      Check clear_nested_if.
      rewrite clear_nested_if by apply filter_nil_is_nil. (* rewrites in right place *)
      (* Need to replace if with If for implement_bag_methods to work. *)
      set_evars; setoid_rewrite refine_if_If.
      simpl in *.
      higher_order_1_reflexivity.
      (* clears goal, but H1 is still in the context, and it still has the
         For/Where/Return ~> _ unimplemented *)
      eauto with typeclass_instances.
    } 
    { reflexivity. } 
} *)

  (*     (* whatever data-integrity constraints there are on the relation, they get automatically added as checks/decision procedures on this (the mutator)  *)
    simpl in *.
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    setoid_rewrite refine_Count.

    Check refine_If_Then_Else_Bind.
    setoid_rewrite refine_If_Then_Else_Bind. simpl in *.

    Check Bind_refine_If_Then_Else.
    (* turns the entire thing into if/then/else toplevel *)
    setoid_rewrite Bind_refine_If_Then_Else.
    apply refine_If_Then_Else; simplify with monad laws.
    -
      subst_all; apply refine_under_bind_both; [reflexivity | intros].
      subst_all; apply refine_under_bind_both; [reflexivity | intros].
      (* ?8535 matches any rewrite rule *)
      (* progress (rewrite clear_nested_if by apply filter_nil_is_nil). *)
      (* progress (rewrite clear_nested_if by apply filter_nil_is_nil). *)
      setoid_rewrite refine_subcheck_to_filter; eauto.
      simplify with monad laws.
      Check clear_nested_if.
      rewrite clear_nested_if by apply filter_nil_is_nil. (* rewrites in right place *)
      (* Need to replace if with If for implement_bag_methods to work. *)
      set_evars; setoid_rewrite refine_if_If.
      simpl in *.
      higher_order_1_reflexivity.
      (* clears goal, but H1 is still in the context, and it still has the
         For/Where/Return ~> _ unimplemented *)
      eauto with typeclass_instances.

    - reflexivity. *)


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
        setoid_rewrite refine_if_If.
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
}

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