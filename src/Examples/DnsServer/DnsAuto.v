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

Hint Resolve refine_count_constraint_broken.

Lemma computes_to_in_specific : forall a n r_n,
 @computes_to
         (list
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute)))))))))
         (@Query_For
            (@Tuple
               (BuildHeading
                  (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                     (@Datatypes.cons Attribute
                        (Build_Attribute sTYPE RRecordType)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sCLASS RRecordClass)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTTL nat)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sDATA string)
                                 (@Datatypes.nil Attribute))))))))
            (@Query_In
               (@Tuple
                  (BuildHeading
                     (@Datatypes.cons Attribute (Build_Attribute sNAME name)
                        (@Datatypes.cons Attribute
                           (Build_Attribute sTYPE RRecordType)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sCLASS RRecordClass)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTTL nat)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sDATA string)
                                    (@Datatypes.nil Attribute))))))))
               (@Build_QueryStructureHint DnsSchema r_n)
               (@Build_BoundedIndex string
                  (@Datatypes.cons string sCOLLECTIONS
                     (@Datatypes.nil string)) sCOLLECTIONS
                  (@Build_IndexBound string sCOLLECTIONS
                     (@Datatypes.cons string sCOLLECTIONS
                        (@Datatypes.nil string)) O
                     (@eq_refl (option string) (@Some string sCOLLECTIONS))))
               (fun
                  r : @Tuple
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) =>
                @Query_Where
                  (@Tuple
                     (BuildHeading
                        (@Datatypes.cons Attribute
                           (Build_Attribute sNAME name)
                           (@Datatypes.cons Attribute
                              (Build_Attribute sTYPE RRecordType)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sCLASS RRecordClass)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sTTL nat)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sDATA string)
                                       (@Datatypes.nil Attribute))))))))
                  (@IsSuffix string (qname (questions n))
                     (@GetAttribute
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute))))))) r
                        (@Build_BoundedIndex string
                           (@Datatypes.cons string sNAME
                              (@Datatypes.cons string sTYPE
                                 (@Datatypes.cons string sCLASS
                                    (@Datatypes.cons string sTTL
                                       (@Datatypes.cons string sDATA
                                          (@Datatypes.nil string)))))) sNAME
                           (@Build_IndexBound string sNAME
                              (@Datatypes.cons string sNAME
                                 (@Datatypes.cons string sTYPE
                                    (@Datatypes.cons string sCLASS
                                       (@Datatypes.cons string sTTL
                                          (@Datatypes.cons string sDATA
                                             (@Datatypes.nil string)))))) O
                              (@eq_refl (option string) (@Some string sNAME))))))
                  (@Query_Return
                     (@Tuple
                        (BuildHeading
                           (@Datatypes.cons Attribute
                              (Build_Attribute sNAME name)
                              (@Datatypes.cons Attribute
                                 (Build_Attribute sTYPE RRecordType)
                                 (@Datatypes.cons Attribute
                                    (Build_Attribute sCLASS RRecordClass)
                                    (@Datatypes.cons Attribute
                                       (Build_Attribute sTTL nat)
                                       (@Datatypes.cons Attribute
                                          (Build_Attribute sDATA string)
                                          (@Datatypes.nil Attribute)))))))) r))))
         a
 ->
   forall n' : DNSRRecord, 
   @List.In DNSRRecord n' a -> @IsPrefix string (get_name n') (qname (questions n)).
Proof.
  intros. 
  eapply For_computes_to_In in H; try eauto.
  inv H.
  + eauto. 
  + pose proof IsSuffix_string_dec. intros. auto.
Qed.


(* -------------------------------------------------------------------------------------- *)

Theorem DnsManual :
  MostlySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

  unfold DnsSpec.

  (* | [ |- context[(@Pick nat) ?X] ] => *)
start sharpening ADT. {
  hone method "Process". {
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
          try (eapply computes_to_in_specific; eauto);
          try reflexivity
        );
    try simplify with monad laws.

    (* not very automated -- TODO try to get rid of these / use setoid_rewrite *)
    Ltac drill :=
      simpl in *;
      try simplify with monad laws;
      try refine_under_bind';
      try refine_bind';
      try apply refine_If_Then_Else.

    (* drill. srewrite_manual'. reflexivity. (* nothing applies to this last goal *) *)

    Ltac automateProcess :=
      drill; srewrite_manual'.

    automateProcess.
  (* TODO compare to original *)
  (* TODO should I try to generalize the ltac to deal wih BOTH methods now? *)
  (* TODO make it more general than that, or just write the recursive one and see what it needs? *)
  (* TODO try to make drill more general? *)
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
(*     (* | [ |- context[(@Pick nat) ?X] ] => *) *)

Create HintDb refines.
Hint Rewrite refine_count_constraint_broken : refines.
Hint Rewrite refine_count_constraint_broken' : refines.

Create HintDb refines'.
Hint Resolve refine_count_constraint_broken : refines'.
Hint Resolve refine_count_constraint_broken' : refines'.

Lemma hi : True. Admitted.
Lemma bye : True. Admitted.
Create HintDb test.
Hint Resolve hi : test.
Hint Resolve bye : test.

Ltac the_tactic :=
  let k lem := idtac lem ; fail in
  foreach [ refines ] run k.

(* this doesn't work well with the [ || ] notation *)
(* why does it need to end with fail? *)
Ltac srewrite :=
  let k lem := setoid_rewrite lem ; fail in
  foreach [ refines ] run k.

(* autorewrite with refines. *)
(* auto with refines'. *)
(* rewrite_strat topdown (hints refines). *)

(* don't rewrite inner If/Then/Else expressions *)
  Ltac rewrite_if_head :=
    match goal with
    | [ |- context[ (refine (Bind _ (fun n => If_Then_Else _ _ _ )) _) ] ] =>
      setoid_rewrite Bind_refine_If_Then_Else
    end. 

(* rewrite under bind the first time you can, then stop. otherwise fail *)
Ltac tac_under_bind tac :=
  first [ tac |
              (apply refine_under_bind; intros); tac_under_bind tac ].

Ltac srewrite_manual :=
  repeat first [
           setoid_rewrite refine_count_constraint_broken
                          || setoid_rewrite refine_count_constraint_broken'
                          || setoid_rewrite refine_If_Then_Else_Bind
                          || rewrite_if_head
                          || setoid_rewrite refine_Count
         ]. 

srewrite_manual.
(* TODO: problem: this takes 30 seconds *)

(* or do progress/first [||]? *)
Ltac finishHone H :=
  repeat (simpl in *;
          try simplify with monad laws;
          try (apply refine_If_Then_Else);
          try simplify with monad laws;
          try tac_under_bind ltac:(setoid_rewrite refine_subcheck_to_filter; eauto;
                               try (simplify with monad laws);
                               try (rewrite clear_nested_if by apply filter_nil_is_nil));
          try simplify with monad laws;
         try eauto;
         try eauto with typeclass_instances;
         try (clear H; reflexivity) (* TODO why clear *)
         ).

(* finishHone H. *)
(* TODO: ??? where is this new unsolvable goal from (adding tac_under_bind) :( *)

simpl in *.
apply refine_If_Then_Else; simplify with monad laws.
(* try w/ semicolon here: only do tac_under_bind on first goal? *)
tac_under_bind ltac:(setoid_rewrite refine_subcheck_to_filter; eauto;
                     try (simplify with monad laws);
                     try (rewrite clear_nested_if by apply filter_nil_is_nil)).
(* TODO: uh, how do i finish this goal *)
reflexivity.


(* TODO: try to simplify the argument to tac_under_bind 
integrate it with automateAddData? *)

Ltac automateAddData H := srewrite_manual; finishHone H.

(* automateAddData H. *)

(* TODO compare to version in DNS *)
(* TODO see if this goes through *)
  (* TODO I removed etransitivity/finish honing here; is that okay? *)

  (* TODO why need to clear H? *)
(* apply refine_If_Then_Else; simplify with monad laws; simpl in *. *)
(* (* Error: Impossible to unify "?24239" with "?20175". *) *)
(* (* former existential is not in Show Existentials; implicit? *) *)
(* reflexivity. *)
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
        setoid_rewrite refine_if_If.
        (* TODO: did an extra rewrite above; is this ok? *)
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
    (* simplify with monad laws. *)
    (* fails -- why? *)
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
