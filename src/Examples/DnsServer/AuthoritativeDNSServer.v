Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation.Decidable
        Fiat.Computation.FoldComp
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.Packet
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation
        Fiat.Examples.DnsServer.AuthoritativeDnsSchema.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * packet -> rep * packet
    }.

Definition DnsSpec (recurseDepth : nat) : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" : rep := empty,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sCOLLECTIONS,

    Def Method1 "Process" (this : rep) (p : packet) : rep * packet :=
        Repeat recurseDepth initializing n with p!"questions"!"qname"
               defaulting rec with (ret (buildempty true p))
        {{ results <- ArgMax (fun r r' : resourceRecord => IsPrefix r!sNAME r'!sNAME)
                             (For (r in this!sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                               Where (IsPrefix r!sNAME n)   (* prefixed with [n] to [rs] *)
                               Return r);
            If (is_empty results) (* Are there any matching records? *)
            Then ret (buildempty true p) (* No matching records! *)
            Else                 (* TODO: this does not filter by matching QTYPE *)
              IfDec (forall r, List.In r results -> n = r!sNAME) (* If the record's QNAME is an exact match  *)
              Then
                b <- Unique (fun b => List.In b results
                                    /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                                    /\ p!"questions"!"qtype" <> CNAME); (* and a non-CNAME was requested*)
                Ifopt b as b'
                Then  (* only one matching CNAME record *)
                  p' <- rec b'!sNAME; (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b') (* Add the CNAME RR to the answer section *)
                Else     (* Copy the records with the correct QTYPE into the answer *)
                         (* section of an empty response *)
                (results <- [[element in results | element!sTYPE = p!"questions"!"qtype" ]];
                  ret (List.fold_left add_answer results (buildempty true p)))
              Else (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records -- *)
                (* ask the authoritative servers *)
                (ns_results <- [[x in results | x!sTYPE = NS]];
                 (* Append all the clue records to the additional section. *)
                 glue_results <- For (rRec in this!sCOLLECTIONS)
                                 Where (List.In rRec!sNAME (map (fun r : resourceRecord => r!sRDATA) ns_results))
                                 Return rRec;
                 ret (List.fold_left add_additional glue_results
                                     (List.fold_left add_ns ns_results (buildempty true p))))
          }} >>= fun p => ret (this, p)}%methDefParsing.

Local Arguments packet : simpl never.

(* Making fold_list Opaque greatly speeds up setoid_rewriting. *)
Opaque fold_left.

(* Need to update derivation to work with arbitrary recursion depth. *)

(*Theorem DnsManual (recurseDepth : nat) :
  FullySharpened (DnsSpec recurseDepth).
Proof.
  start sharpening ADT; unfold DnsSpec.
  simpl; pose_string_hyps; pose_heading_hyps.
  hone method "Process".
  simpl in *.
  { simplify with monad laws.

    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
  }
  drop_constraintsfrom_DNS.
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
        doOne drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone method "AddData".
    simplify with monad laws; etransitivity; set_evars.
    doAny simplify_queries
          Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    doOne srewrite_each_all drills_each_all finish_each_all.
    setoid_rewrite refine_count_constraint_broken.
    repeat doOne srewrite_each_all drills_each_all finish_each_all.
    repeat doOne srewrite_each_all drills_each_all finish_each_all.
    make_simple_indexes ({|prim_fst := [("FindPrefixIndex", Fin.F1)];
                           prim_snd := () |} : prim_prod (list (string * Fin.t 6)) ())
                        ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
                               ltac:(CombineCase5 BuildLastFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + repeat doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
    + doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).


      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      Focused_refine_TopMost_Query.
      implement_In_opt.
      repeat progress distribute_filters_to_joins.
      implement_filters_with_find
        ltac:(find_simple_search_term ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                      ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                             ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm))
               ltac:(find_simple_search_term_dep
                       ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                              ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                     ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep)).



      doOne implement_insert''
            ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars) ltac:(finish honing).
      implement_In_opt.
      repeat progress distribute_filters_to_joins.
      setoid_rewrite
      match goal with
  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (refine_Filtered_Query_In_Enumerate H (idx := idx) f) in
            apply H'
      | apply refine_under_bind; intros; implement_In_opt' ]

  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (List_Query_In ?b (fun b : ?QueryT => Where (@?P b) (@?resultComp b))) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (@refine_List_Query_In_Where QueryT _ b P resultComp _) in
            apply H'
      | implement_In_opt'; implement_In_opt' ] end.


    +  unfold SearchUpdateTerm in Index; simpl in Index.
       simpl.
Finish_Master ltac:(CombineCase6 BuildEarlyTrieBag  BuildEarlyBag )
                           ltac:(CombineCase5 BuildLastTrieBag BuildLastBag).
Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl. *)

(* TODO extraction, examples/messagesextraction.v *)
