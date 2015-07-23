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
        Fiat.QueryStructure.Automation.SearchTerms.FindSuffixSearchTerms
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
                                               (* n<- count (For (r in _) where (r = tup) return True); if n > 0 then.. *)
                                               (* For refines decision procedure *)
    update "AddData" (t : DNSRRecord) : bool :=
      Insert t into sCOLLECTIONS,

    query "Process" (p : packet) : packet :=
      let t := qtype (questions p) in
      Repeat 1 initializing n with qname (questions p)
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsSuffix n r!sNAME) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (negb (is_empty rs))        (* Are there any matching records? *)
            Then                    (* TODO: reverse these if/then cases *)
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
                 ask the authoritative servers *)
                bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left addns bfrs' (buildempty p))
            Else ret (buildempty p) (* No matching records! *)
          }}}.

(* -------------------------------------------------------------------------------------- *)

Theorem DnsManual :
  MostlySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

  unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    automateProcess.
  }

    (* TODO can we remove these and just setoid rewrite? or does setoid rewrite need the vars? *)
    (* TODO can we remove If/Then/Else too? *)
    (* refine_under_bind'.  *)
    (* Check refine_under_bind.    (* bring an entire line (up to ;) into context *) *)
    (* Check refine_bind.          (* refine X in r <- X; r' *) *)
    (* refine_bind'.          (* refine the If/Then/Else part only *) *)
    (* Check refine_If_Then_Else. *)
    (* apply refine_If_Then_Else. *)
    
    (* setoid_rewrite (@refine_find_upperbound DNSRRecord _ _). *)
    (* setoid_rewrite (@refine_decides_forall_In' _ _ _ _). *)
    (* simplify with monad laws. *)

    (* need both bind and if_then_else for simplify to work *)
    (* we need a stronger [simplify with monad laws] (inside bind)! i don't think we should need refine_bind and refine_if_then_else for most things *)
    (* setoid_rewrite refine_check_one_longest_prefix_s. *)
    (* simplify with monad laws. *)

    (* setoid_rewrite refine_if_If. *)
    (* setoid_rewrite refine_check_one_longest_prefix_CNAME. (* no morphism for normal if/then *) *)
  (* bfrs' is still not deterministic? it's also not right; should be "choose one of" *)
  (* commented out if/then/else that refined tha *)


  start_honing_QueryStructure'.

  hone method "AddData".
  {
    automateAddData H.
  }

  GenerateIndexesForAll         (* ? in IndexSelection, see GenerateIndexesFor *)
  (* specifies that you want to use the suffix index structure TODO *)
  ltac:(CombineCase2 matchFindSuffixIndex matchEqIndex)
         ltac:(fun attrlist => make simple indexes using attrlist).
  (* SearchTerm and SearchUpdateTerm: efficiently do quality test on the name columns *)
  (* it figures out what data structure to use *)
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
          ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                        ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                        ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
        simplify with monad laws.
        rewrite (@refineEquiv_swap_bind nat).
        implement_Insert_branches. (* this removes the nat choosing, so I guess the nondeterminism is okay if it involves indexed. the matching involves some of UnConstrFreshIdx *)
        (* ok, i guess getting a fresh ID for the index depends on the index specifics *)
        reflexivity.            (* broken *)
      + simplify with monad laws.
        implement_Query
          ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
                 ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                        ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                               ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                      ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                             ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
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
      ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                           ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
    simplify with monad laws.
    simpl.
    setoid_rewrite (refine_pick_val _ H).
    simplify with monad laws.
    setoid_rewrite (@refine_filtered_list _ _ _ _).
    finish honing.
  }
  
  FullySharpenQueryStructure' DnsSchema Index.
  (* implement_bag_methods needs to be patched for this goal. *)

  - implement_bag_methods.
  - implement_bag_methods.
Time Defined.

    Definition DnsDelegateReps
    : ilist (fun ns => Type) (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact (list (@Tuple
           <sNAME :: name, sTYPE :: RRecordType, sCLASS :: RRecordClass,
              sTTL :: nat, sDATA :: string>%Heading)).
    Defined.

    Definition DnsDelegateSearchUpdateTerms
    : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
             (qschemaSchemas DnsSchema).
      simpl; econstructor; [ | econstructor ].
      exact  DnsSearchUpdateTerm.
    Defined.



    Definition DnsDelegateImpls
    : i2list2 (fun ns (SearchTerm : SearchUpdateTerms (schemaHeading (relSchema ns)))
                   (Rep : Type) =>
                 ComputationalADT.pcADT
                   (BagSig (@Tuple (schemaHeading (relSchema ns)))
                           (BagSearchTermType SearchTerm)
                           (BagUpdateTermType SearchTerm))
                   Rep)
              DnsDelegateSearchUpdateTerms
              DnsDelegateReps.
      simpl; econstructor; [ | econstructor ].
      let p := eval simpl in (projT2 (BagADTImpl (fun _ => true)
                         (@ListAsBag
                            _
                            (BagSearchTermType DnsSearchUpdateTerm)
                            (BagUpdateTermType DnsSearchUpdateTerm)
                            {| pst_name := nil;
                               pst_filter := fun _ => true |}
                            (BagMatchSearchTerm DnsSearchUpdateTerm)
                            (BagApplyUpdateTerm DnsSearchUpdateTerm) ))) in
          exact p.
    Defined.

    Definition DnsImpl : SharpenedUnderDelegates DnsSig.
      Time let
          Impl := eval simpl in (projT1 DnsManual) in exact Impl.
    Defined.

    Print DnsImpl.
    Definition ExtractWorthyDNSImpl : ComputationalADT.cADT DnsSig.
      let s := eval unfold DnsImpl in DnsImpl in
          let Impl := eval simpl in
          (Sharpened_Implementation s
                                    (LookupQSDelegateReps DnsDelegateReps)
                                    (LookupQSDelegateImpls DnsDelegateImpls)) in exact Impl.
    Defined.

    Print ExtractWorthyDNSImpl.

    Extraction "bar.ml" ExtractWorthyDNSImpl.
