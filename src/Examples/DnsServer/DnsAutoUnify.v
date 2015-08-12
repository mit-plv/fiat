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
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation.

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

Theorem DnsManual :
  FullySharpened DnsSpec.
Proof. unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    Time doAnyAll. 
  (* 241 seconds = 4 minutes *)
}

  (* hack to fix Process's ret statement for now *)
  (* need to pull out the three [ret (r_n, a)] into p <- ret a; ret (r_n, p) *)
  hone method "Process". {
    simpl in *. subst_all.
    apply refine_under_bind_both; [reflexivity | intros].

    Lemma refine_If_Then_Else_same'
      : forall (A B : Type) i (t : Comp A) (b : A -> A) (c : A) (r_n : B),
        refine
          (If i Then (a <- t;
                      ret (r_n, b a))
                Else (ret (r_n, c))) 
          (res <- If i Then (a <- t;
                             ret (b a))
                       Else (ret c);
           ret (r_n, res)).
    Proof.
      intros; destruct i; simpl; 
      autosetoid_rewrite with refine_monad; reflexivity.
    Qed.

    set_evars. simpl in *. 
    repeat rewrite refine_If_Then_Else_same'.
    finish honing.
  }

  start_honing_QueryStructure'.

  hone method "AddData".
  {
    Time doAnyAll.
  (* 202 seconds = 3.5 minutes *)
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

    (* etransitivity. *)
    setoid_rewrite Bind_refine_If_Then_Else.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    -
      apply refine_If_Then_Else.
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                        ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                        ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).
        (* simplify with monad laws. *)
        idtac.
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
        (* setoid_rewrite refine_if_If. *)
        implement_Insert_branches.
        reflexivity.
    - higher_order_reflexivity.              (* seems fully deterministic here *)
    (* - finish honing. *)
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
