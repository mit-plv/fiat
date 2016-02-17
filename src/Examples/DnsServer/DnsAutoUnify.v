Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsLemmas
        Fiat.Examples.DnsServer.DnsAutomation.

Require Import Fiat.Examples.DnsServer.DnsSchema.

Definition DnsSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddData" : rep * resourceRecord -> rep * bool,
      Method "Process" : rep * packet -> rep * packet
    }.

(* First stab at a declarative specification for the matching algorithm. *)
Inductive matchRR (RRecords : @IndexedEnsemble resourceRecord)
  : RRecordType
    -> name
    -> list resourceRecord (* answers *)
    -> list resourceRecord (* authority *)
    -> list resourceRecord (* additional *)
    -> Prop :=
  (* If the whole of QNAME is matched, we have found the node. *)

  (* If the data at the node is a CNAME, and QTYPE doesn't
     match CNAME, copy the CNAME RR into the answer section
     of the response, change QNAME to the canonical name in
     the CNAME RR, and go back to step 1. *)
| match_eq_CNAME :
    forall nm ttl qtype class rlength rdata answers authority additional,
      IndexedEnsemble_In RRecords
      <sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: CNAME, sRLENGTH :: rlength, sRDATA :: (inl rdata)>
      -> qtype <> CNAME
      -> matchRR RRecords qtype rdata answers authority additional
      -> matchRR RRecords qtype nm
                 (<sNAME :: nm, sTTL :: ttl, sCLASS :: class,
                  sTYPE :: qtype, sRLENGTH :: rlength, sRDATA :: (inl rdata)>
                  :: answers) authority additional

(* Otherwise, copy all RRs which match QTYPE into the answer section. *)
| match_eq_qtype :
    forall nm ttl qtype class rlength rdata,
      IndexedEnsemble_In RRecords
      <sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: qtype, sRLENGTH :: rlength, sRDATA :: rdata>
      -> matchRR RRecords qtype nm
                 [<sNAME :: nm, sTTL :: ttl, sCLASS :: class,
                  sTYPE :: qtype, sRLENGTH :: rlength, sRDATA :: rdata>] nil nil

(* If a match would take us out of the authoritative data,
   we have a referral.  This happens when we encounter a
   node with NS RRs marking cuts along the bottom of a
   zone.

   Copy the NS RRs for the subzone into the authority
   section of the reply.  Put whatever addresses are
   available into the additional section, using glue RRs
   if the addresses are not available from authoritative
   data or the cache. *)

| match_referral :
    forall qname nm ttl qtype class rlength rdata,
      IndexedEnsemble_In RRecords
      <sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: NS, sRLENGTH :: rlength, sRDATA :: rdata>
     -> IsPrefix nm qname
      -> matchRR RRecords qtype nm
                 nil [<sNAME :: nm, sTTL :: ttl, sCLASS :: class, sTYPE :: NS, sRLENGTH :: rlength, sRDATA :: rdata>] nil.

Definition updateresponse (p : packet) answers authority additional :=
  p ○ [o !! "flags" / replace_order o zero_lt_sixteen true;
        (* 0 = query (changed by client); 1 = response (changed by server) *)
        (* set QR bit to true, meaning this is a response *)
        (* do we want an AA (authoritative answer) flag? *)
        "answers" ::= answers; "authority"  ::= authority; "additional" ::= additional ].

Definition DeclarativeDnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" : rep := empty,

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sCOLLECTIONS,

    Def Method1 "Process" (this : rep) (p : packet) : rep * packet :=
        answers <- {answers' | forall answer,
                       List.In answer answers' <->
                       exists answers authority additional,
                         List.In answer answers /\
                         matchRR (GetRelation this Fin.F1)
                                 (p!"questions"!"qtype")
                                 (p!"questions"!"qname")
                                 answers authority additional};
        authority <- {authority' | forall auth,
                           List.In auth authority' <->
                           exists answers authority additional,
                             List.In auth authority /\
                           matchRR (GetRelation this Fin.F1)
                                 (p!"questions"!"qtype")
                                 (p!"questions"!"qname")
                                 answers authority additional};
        additional <- {additional' | forall add,
                          List.In add additional' <->
                          exists answers authority additional,
                            List.In add additional /\
                            matchRR (GetRelation this Fin.F1)
                                    (p!"questions"!"qtype")
                                    (p!"questions"!"qname")
                                    answers authority additional};
        (* Should check to see if everything is empty, in which case set an error. *)
        ret (this, updateresponse p answers authority additional)}%methDefParsing.

Definition DnsSpec : ADT DnsSig :=
  QueryADTRep DnsSchema {
    Def Constructor "Init" : rep := empty,

    (* in start honing querystructure, it inserts constraints before *)
    (* every insert / decision procedure *)

    Def Method1 "AddData" (this : rep) (t : resourceRecord) : rep * bool :=
      Insert t into this!sCOLLECTIONS,

    Def Method1 "Process" (this : rep) (p : packet) : rep * packet :=
        Repeat 1 initializing n with p!"questions"!"qname"
               defaulting rec with (ret (buildempty p))
         {{ rs <- For (r in this!sCOLLECTIONS)      (* Bind a list of all the DNS entries *)
                  Where (IsPrefix r!sNAME n) (* prefixed with [n] to [rs] *)
                  (* prefix: "com.google" is a prefix of "com.google.scholar" *)
                  Return r;
            If (is_empty rs)        (* Are there any matching records? *)
            Then ret (buildempty p) (* No matching records! *)
            Else                (* TODO: this does not filter by matching QTYPE *)
              (bfrs <- [[r in rs | upperbound name_length rs r]]; (* Find the best match (largest prefix) in [rs] *)
              b <- { b | decides b (forall r, List.In r bfrs -> n = r!sNAME) };
              If b                (* If the record's QNAME is an exact match  *)
              Then
                unique b,                         (* only one match (unique / otherwise) *)
                List.In b bfrs /\ b!sTYPE = CNAME     (* If the record is a CNAME, *)
                               /\ p!"questions"!"qtype" <> CNAME ->>      (* and the query did not request a CNAME *)
                  p' <- rec b!sNAME;                  (* Recursively find records matching the CNAME *)
                  ret (add_answer p' b)               (* ?? Shouldn't this use the sDATA ?? *)
                otherwise ->>     (* Copy the records into the answer section of an empty response *)
                (* multiple matches -- add them all as answers in the packet *)
                  ret (List.fold_left add_answer bfrs (buildempty p))
              Else              (* prefix but record's QNAME not an exact match *)
                (* return all the prefix records that are nameserver records --
                 ask the authoritative servers *) (* TODO does this return one, or return all? *)
                (bfrs' <- [[x in bfrs | x!sTYPE = NS]];
                ret (List.fold_left add_ns bfrs' (buildempty p))))
          }} >>= fun p => ret (this, p)}%methDefParsing.

Local Arguments packet : simpl never.

Ltac hone_Dns :=
  start sharpening ADT;

  hone method "Process"; [ doAnyAll | ]; (* 241 seconds = 4 minutes *)
  start_honing_QueryStructure';
  hone method "AddData"; [ doAnyAll | ]; (* 202 seconds = 3.5 minutes *)
  finish_planning ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics)
                         ltac:(fun makeIndex =>
                                 GenerateIndexesForOne "Process" ltac:(fun attrlist =>
                                                                         let attrlist' := eval compute in (PickIndexes (CountAttributes' attrlist)) in makeIndex attrlist')).

Ltac srewrite_each_all :=
    first
  [ rewrite refine_pick_eq'
  | rewrite (refine_find_upperbound _ _)
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
        repeat implement_insert'
               ltac:(CombineCase5 PrefixIndexUse EqIndexUse)
                      ltac:(CombineCase10 createEarlyPrefixTerm createEarlyEqualityTerm)
                             ltac:(CombineCase7 createLastPrefixTerm createLastEqualityTerm)
                                    ltac:(CombineCase7 PrefixIndexUse_dep EqIndexUse_dep)
                                           ltac:(CombineCase11 createEarlyPrefixTerm_dep createEarlyEqualityTerm_dep)
                                                  ltac:(CombineCase8 createLastPrefixTerm_dep createLastEqualityTerm_dep).

(* Making fold_list Opaque greatly speeds up setoid_rewriting. *)
Opaque fold_left.
Opaque packet.
Theorem DnsManual :
  FullySharpened DnsSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  hone method "Process".
  simpl in *.
  { (* Stepping through doAnyAll. Uncomment the below line and *)
    (* comment the up until start_honing_QueryStructure' to see the *)
    (* automated tactic work it's magic. *)
    (* Time doAnyAll. *)
    simpl in *.
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      repeat_and_simplify finish_each_all. }
    { repeat_and_simplify srewrite_each_all.
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify srewrite_each_all.
        do_and_simplify drills_each_all.
        { repeat_and_simplify srewrite_each_all.
          do_and_simplify drills_each_all.
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
        }
        { repeat_and_simplify srewrite_each_all.
          repeat_and_simplify finish_each_all. }
      }
      repeat_and_simplify finish_each_all.
      repeat_and_simplify finish_each_all.
      repeat_and_simplify finish_each_all.
    }
  }
  pose_string_hyps.
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
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone method "AddData".
    simplify with monad laws.
    etransitivity.
    set_evars.
    doAny simplify_queries
          Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      repeat_and_simplify finish_each_all. }
    { repeat_and_simplify srewrite_each_all.
      do_and_simplify drills_each_all.
      { setoid_rewrite refine_count_constraint_broken.
        repeat_and_simplify srewrite_each_all.
        do_and_simplify drills_each_all.
        repeat_and_simplify finish_each_all.
        repeat_and_simplify finish_each_all.
      }
      { repeat_and_simplify srewrite_each_all.
        do_and_simplify drills_each_all.
        { repeat_and_simplify srewrite_each_all.
          repeat_and_simplify finish_each_all. }
        do_and_simplify drills_each_all.
        { repeat_and_simplify srewrite_each_all.
          do_and_simplify drills_each_all.
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
        }
        { repeat_and_simplify srewrite_each_all.
          repeat_and_simplify finish_each_all. }
        }
    }
    simpl.
    make_simple_indexes ({|prim_fst := [("FindPrefixIndex", Fin.F1)];
                           prim_snd := () |} : prim_prod (list (string * Fin.t 6)) ())
                        ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
                               ltac:(CombineCase5 BuildLastFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      implement_insert''.
      finish honing.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      finish honing.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      set_evars.
      implement_insert''.
      finish honing.
      implement_insert''.
      finish honing.
      implement_insert''.
      finish honing.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      finish honing.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars.
      implement_insert''.
      finish honing.
      implement_insert''.
      finish honing.
    +  implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars.
      finish honing.
      implement_insert''.
      master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm; set_evars.
      implement_insert''.
      first [master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm;
              set_evars
            | finish honing ].
      implement_insert''.
      first [master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm;
              set_evars
            | finish honing ].
      implement_insert''.
      first [master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm;
              set_evars
            | finish honing ].
      implement_insert''.
      first [master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm;
              set_evars
            | finish honing ].
      implement_insert''.
      first [master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm;
              set_evars
            | finish honing ].
      implement_insert''.
      first [master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm;
              set_evars
            | finish honing ].
    +  unfold SearchUpdateTerm in Index; simpl in Index.
Finish_Master ltac:(CombineCase6 BuildEarlyTrieBag  BuildEarlyBag )
                           ltac:(CombineCase5 BuildLastTrieBag BuildLastBag).

Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.



  (* This is setup for the generalized delegation tactic. *)
  - hone representation using (@FiniteTables_AbsR DnsSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + simplify with monad laws.
      etransitivity.
      set_evars.
      doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      repeat_and_simplify srewrite_each_all.
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify srewrite_each_all.
        do_and_simplify drills_each_all.
        { setoid_rewrite refine_count_constraint_broken.
          repeat_and_simplify srewrite_each_all.
          do_and_simplify drills_each_all.
          repeat_and_simplify finish_each_all.
          repeat_and_simplify finish_each_all.
        }
        { repeat_and_simplify srewrite_each_all.
          do_and_simplify drills_each_all.
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
          do_and_simplify drills_each_all.
          { repeat_and_simplify srewrite_each_all.
            do_and_simplify drills_each_all.
            { repeat_and_simplify srewrite_each_all.
              repeat_and_simplify finish_each_all. }
            { repeat_and_simplify srewrite_each_all.
              repeat_and_simplify finish_each_all. }
          }
          { repeat_and_simplify srewrite_each_all.
            repeat_and_simplify finish_each_all. }
        }
      }
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + simpl.
      Print Ltac CombineIndexTactics.
      Unset Ltac Debug.
      GenerateIndexesForAll
        ltac:(IsPrefixExpressionAttributeCounter EqExpressionAttributeCounter)
        ltac:(fun attrlist =>
                let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in
                    pose attrlist').
                    make_simple_indexes attrlist'
                                                                                                                    ltac:(CombineCase6 BuildEarlyFindPrefixIndex ltac:(LastCombineCase6 BuildEarlyEqualityIndex))
                                                                                                                           ltac:(CombineCase5 BuildLastFindPrefixIndex ltac:(LastCombineCase5 BuildLastEqualityIndex))).

      master_plan ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics).


  start_honing_QueryStructure'.
  hone method "AddData".
  { (* Stepping through doAnyAll. Uncomment the below line and *)
    (* comment the up until start_honing_QueryStructure' to see the *)
    (* automated tactic work it's magic. *)
    (* Time doAnyAll. *)
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      repeat_and_simplify finish_each_all. }
    repeat_and_simplify srewrite_each_all.
    do_and_simplify drills_each_all.
    { repeat_and_simplify srewrite_each_all.
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify rewrite_each_all.
        repeat_and_simplify finish_each_all. } }
    do_and_simplify drills_each_all.
      { repeat_and_simplify srewrite_each_all.
        repeat_and_simplify finish_each_all. }
      do_and_simplify drills_each_all.
      { repeat_and_simplify rewrite_each_all.
        repeat_and_simplify finish_each_all. }
      { repeat_and_simplify rewrite_each_all.
        repeat_and_simplify finish_each_all. } }
  simpl.
  (* Still need to update master_plan with some search instances. *)
  master_plan ltac:(CombineIndexTactics PrefixIndexTactics EqIndexTactics).

Time Defined.

Time Definition DNSImpl := Eval simpl in (projT1 DnsManual).

Print DNSImpl.

(* TODO extraction, examples/messagesextraction.v *)
