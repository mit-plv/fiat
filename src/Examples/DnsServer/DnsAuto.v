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
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > 0 then.. *)
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

(* For Process (here temporarily; move back to DnsAutomation) *)

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

Ltac srewrite_each :=
  first
    [
      setoid_rewrite (@refine_find_upperbound DNSRRecord _ _) |
      setoid_rewrite (@refine_decides_forall_In' _ _ _ _) |
      setoid_rewrite refine_check_one_longest_prefix_s |
      setoid_rewrite refine_if_If |
      setoid_rewrite refine_check_one_longest_prefix_CNAME
    ].

Ltac srewrite_manual' :=
  repeat (
      try srewrite_each;
      try simplify with monad laws
    );
  repeat (
      try (eapply tuples_in_relation_satisfy_constraint_specific; eauto);
      try solve [eapply For_computes_to_In; eauto using IsPrefix_string_dec];
      (* otherwise loops forever *)
      try reflexivity
    );
  try simplify with monad laws.

(* not very automated -- TODO try to get rid of these / use setoid_rewrite
can i get rid of refine_under_bind/refine_bind'/refine_If_Then_Else? *)
Ltac drill :=
  simpl in *;
  try simplify with monad laws;
  try refine_under_bind';
  try refine_bind';
  try apply refine_If_Then_Else.

(* drill. srewrite_manual'. reflexivity. (* nothing applies to this last goal *) *)

Ltac automateProcess :=
  drill; srewrite_manual'.

(* --------------- *)
(* For AddData *)

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

Ltac finishHone H :=
  repeat (simpl in *;
           try simplify with monad laws;
          try (apply refine_If_Then_Else);
          try simplify with monad laws;
          try tac_under_bind ltac:(
            do_by ltac:(setoid_rewrite refine_subcheck_to_filter) ltac:(eauto with typeclass_instances);
            try (simplify with monad laws);
            try (rewrite clear_nested_if by apply filter_nil_is_nil));
          try simplify with monad laws;
          try eauto;
          try (clear H; reflexivity) (* TODO why clear. does h_o_r work here? *)
         ).

Ltac automateAddData H := srewrite_manual; finishHone H.
(* TODO why need to clear H? *)
(* ---------------------- *)

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof. unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    automateProcess.
  }

    (* Check refine_under_bind.    (* bring an entire line (up to ;) into context *) *)
    (* Check refine_bind.          (* refine X in r <- X; r' *) *)
    (* refine_bind'.          (* refine the If/Then/Else part only *) *)
    (* Check refine_If_Then_Else. *)
    
    (* need both bind and if_then_else for simplify to work *)
    (* we need a stronger [simplify with monad laws] (inside bind)! i don't think we should need refine_bind and refine_if_then_else for most things *)
    (* setoid_rewrite refine_check_one_longest_prefix_s. *)
    (* simplify with monad laws. *)
  (* bfrs' is still not deterministic? it's also not right; should be "choose one of" *)

  start_honing_QueryStructure'.

  hone method "AddData".
  {
    (* automateProcess. *)
    (* simpl in *. *)
    (* try refine_under_bind'. *)
    (* try refine_bind'. *)
    (* eauto. *)

    (* this doesn't change the code, but completes subproof *)
    (* drill. *)
    (* this is going to do the same thing: refine just the inner statement in the second line *)
    (* need a more general notion of breaking it into each line as a subgoal, with the assumptions from refine_bind? no, but what about simplify with monad laws (may combine multiple lines)? *)
    (* it would also be nice to setoid_rewrite EVERYTHING without the need for drilling into binds *)
    (* we also need a better [simplify with monad laws] (under bind) *)
    (* maybe need a high-level/metatactic to deal with binds and combining results? think about what each line of tactics is doing to the whole function *)
    (* TODO: talk to ben about this *)

    automateAddData H.
  }

  (* should I expand one ltac to include the other? should i test each ltac on the other problem?
compare to dns? write one big one to encompass both? what's a nice incremental way to do/test it? 
write one that covers both head parts, then both setoid rewrites, then both conclusions/eautos?
*)
  (* match goal with...?  *)
  (* do any of the setoid rewrites interact problematically with the goals of the other? *)

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

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
