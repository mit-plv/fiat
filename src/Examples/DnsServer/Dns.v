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

(* TODO [autorewrite with monad laws] breaks when this is moved into DnsLemmas *)

(* implement the DNS record constraint check as code that counts the number of occurrences of
the constraint being broken (refines the boolean x1 in AddData) *)
Lemma refine_count_constraint_broken :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       n!sNAME = (indexedElement tup')!sNAME -> n!sTYPE <> CNAME)}
           (If (beq_RRecordType n!sTYPE CNAME)
               Then count <- Count
               For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                     (fun tup : Tuple =>
                                        Where (n!sNAME = tup!sNAME)
                                              Return tup ));
            ret (beq_nat count 0) Else ret true).
Proof.
  intros; setoid_rewrite refine_pick_decides at 1;
  [ | apply refine_is_CNAME__forall_to_exists | apply refine_not_CNAME__independent ].
  (* refine existence check into query. *)
  match goal with
      |- context[{b | decides b
                              (exists tup : @IndexedTuple ?heading,
                                 (@GetUnConstrRelation ?qs_schema ?qs ?tbl tup /\ @?P tup))}]
      =>
      let H1 := fresh in
      let H2 := fresh in
      makeEvar (Ensemble (@Tuple heading))
               ltac:(fun P' => assert (Same_set (@IndexedTuple heading) (fun t => P' (indexedElement t)) P) as H1;
                     [unfold Same_set, Included, Ensembles.In;
                       split; [intros x H; pattern (indexedElement x);
                               match goal with
                                   |- ?P'' (indexedElement x) => unify P' P'';
                                     simpl; eauto
                               end
                              | eauto]
                     |
                     assert (DecideableEnsemble P') as H2;
                       [ simpl; eauto with typeclass_instances (* Discharge DecideableEnsemble w/ intances. *)
                       | setoid_rewrite (@refine_constraint_check_into_query' qs_schema tbl qs P P' H2 H1); clear H1 H2 ] ]) end.
  remember n!sTYPE; refine pick val (beq_RRecordType d CNAME); subst;
  [ | case_eq (beq_RRecordType n!sTYPE CNAME); intros;
      rewrite <- beq_RRecordType_dec in H; find_if_inside;
      unfold not; simpl in *; try congruence ].
  simplify with monad laws.
  autorewrite with monad laws.
  setoid_rewrite negb_involutive.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------------------- *)

Theorem DnsManual :
  MostlySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

  unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    simplify with monad laws.
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
        inv H0. unfold IsSuffix in *. unfold get_name.
      + apply H2.
      + pose proof IsSuffix_string_dec. intros. auto.
      + auto.
    }
    simplify with monad laws.
    reflexivity. reflexivity.
    
    reflexivity. subst H1; reflexivity.
    unfold pointwise_relation; intros; higher_order_reflexivity.
    finish honing. finish honing.
}

  start_honing_QueryStructure'.

  hone method "AddData".
  {
    (* whatever data-integrity constraints there are on the relation, they get automatically added as checks/decision procedures on this (the mutator)  *)
    simpl in *.
    (* what is H? I guess an unimplemented something of the right type (or whose type is of the right type)? *)

    (* refine (AddData body) (H r_n n) <-- what is that? *)
    (* H := existential variable of the correct (?) type,
       r_n : UnConstrQueryStructure DnsSchema, n : DNSRRecord*)
    (* x1 = check constraint between n (the record) and every other tuple  *)
    (* x2 = check constraint between every other tuple and n (the record) *)
    (* differs in the final step ((_)!sTYPE <> CNAME) *)
    
    (* redundant *)
    (* subst_all. *)
    (* match goal with *)
    (*   |- refine _ (?H _ _) => let id := fresh in set (id := H) in * *)
    (* end.                        (* replace ex var with name H again *) *)
    (* simpl in *. *)
    Check refine_count_constraint_broken.
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    setoid_rewrite refine_If_Then_Else_Bind. simpl in *.
    (* body after x1 gets pasted inside again *)

    Check Bind_refine_If_Then_Else. (* x2 replaced with a *)
    setoid_rewrite Bind_refine_If_Then_Else.
    (* this was done an extra time *)
    (* etransitivity. *)
    apply refine_If_Then_Else.
    -
      (* simplify with monad laws. *)
      Check refine_under_bind.
      apply refine_under_bind; intros.
      (* apply refine_under_bind; intros. *) 
      Check refine_Count.
      setoid_rewrite refine_Count. simplify with monad laws.
      apply refine_under_bind.  Check refine_under_bind. intros.
      setoid_rewrite refine_subcheck_to_filter; eauto.
      Check refine_subcheck_to_filter.
      (* Set Printing All. auto. *)
      simplify with monad laws.
      Check clear_nested_if.
      rewrite clear_nested_if by apply filter_nil_is_nil.
      higher_order_1_reflexivity.
      (* clears goal, but H1 is still in the context, and it still has the 
         For/Where/Return ~> _ unimplemented *)
      eauto with typeclass_instances.
    - simplify with monad laws.
      setoid_rewrite refine_Count. simplify with monad laws.
      (* ^ added by automation, thanks! *)
      (* setoid_rewrite refine_subcheck_to_filter; eauto. *)
      (* did something break? nondeterministic ^ TODO *)
      (* why is this OK? it didn't get rid of x0 nondeterminism *)
      reflexivity.
    (* - finish honing. *)
  } 
  (* higher level of reasoning *)

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
        setoid_rewrite refine_if_If.
        implement_Insert_branches. (* this removes the nat choosing, so I guess the nondeterminism is okay if it involves indexed. the matching involves some of UnConstrFreshIdx *)
        (* ok, i guess getting a fresh ID for the index depends on the index specifics *)
        reflexivity.
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
