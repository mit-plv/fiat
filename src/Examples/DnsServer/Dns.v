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

(* Refinement lemmas that depend on DnsSchema (other lemmas are in DnsLemmas) *)

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


(* uses refine_forall_to_exists; refines x2 in AddData 
very similar to refine_count_constraint_broken; comments below are relative to refine_count_constraint_broken *)
Lemma refine_count_constraint_broken' :
  forall (n : DNSRRecord) (r : UnConstrQueryStructure DnsSchema),
    refine {b |
            decides b
                    (forall tup' : @IndexedTuple (GetHeading DnsSchema sCOLLECTIONS),
                       (r!sCOLLECTIONS)%QueryImpl tup' ->
                       (indexedElement tup')!sNAME = n!sNAME (* switched *)
                       -> (indexedElement tup')!sTYPE <> CNAME)} (* indexedElement tup', not n *)
           (* missing the If/Then statement *)
           (count <- Count
                  For (UnConstrQuery_In r ``(sCOLLECTIONS)
                                        (fun tup : Tuple =>
                                           Where (n!sNAME = tup!sNAME
                                                  /\ tup!sTYPE = CNAME ) (* extra /\ condition *)
                                                 Return tup ));
            ret (beq_nat count 0)).
Proof.
  intros; setoid_rewrite refine_forall_to_exists.
  (*refine existence check into query. *)
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
  (* apply @DecideableEnsemble_And.  apply DecideableEnsemble_EqDec.
  apply Query_eq_list. apply DecideableEnsemble_EqDec. apply Query_eq_RRecordType.
  Print Instances DecideableEnsemble. *)
  simplify with monad laws.
  setoid_rewrite negb_involutive; f_equiv.
Qed.

(* ------------------------ *)
(* Debugging lemmas for prefix lemma *)

Check BoundedIndex.
Print BoundedIndex.

(*
Lemma minimal: 
    let heading := <sNAME :: name, sTYPE :: RRecordType, 
                   sCLASS :: RRecordClass, sTTL :: nat, 
                   sDATA :: string>%Heading : Heading in

    let BStringId0 := ``(sNAME) (* : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] *) in
    let BStringId1 := ``(sTYPE) (* : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] *) in

    let schma := {|
          schemaHeading := heading;
          attrConstraints := None;
          tupleConstraints := Some
                                (fun t t' : Tuple =>
                                   GetAttribute t BStringId0 =
                                   GetAttribute t' BStringId0 ->
                                   GetAttribute t BStringId1 <> CNAME) |}
                 : Schema in
 
    True.
(* CNAME error *)
Proof.
Admitted.

Check GetAttribute.
Print GetAttribute.
Check Attributes.
Print Attributes.
Locate GetAttribute.

Lemma minimal_annotated: 
    let heading := <sNAME :: name, sTYPE :: RRecordType, 
                   sCLASS :: RRecordClass, sTTL :: nat, 
                   sDATA :: string>%Heading : Heading in

    let BStringId0 := ``(sNAME) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
    let BStringId1 := ``(sTYPE) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
    (* annotated, error goes away when schma is commented out *)
    let schma := {|
          schemaHeading := heading;
          attrConstraints := None;
          tupleConstraints := Some
                                (fun t t' : Tuple =>
                                   (* typeclass magic error? *)
                                   @GetAttribute heading t BStringId0 =
                                   @GetAttribute heading t' BStringId0 ->
                                   @GetAttribute heading t BStringId1 <> CNAME) |}
                 : Schema in
 
    True.
Proof.

Admitted.
*)

Ltac inv H := inversion H; clear H; try subst.

(* TODO: move into another file if possible
TODO: clean up annotations/typeclass magic *)
Lemma found_names_are_prefixes_of_question : 
    (* large context here is pasted from the proof *)
    let StringId2 := "EqualityIndex" : string in
    let StringId3 := "Name" : string in
    let BStringId := ``(sCOLLECTIONS) : BoundedIndex [sCOLLECTIONS] in
    let BStringId2 := ``(StringId3)
                      : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in


    let heading := <sNAME :: name, sTYPE :: RRecordType, 
  sCLASS :: RRecordClass, sTTL :: nat, 
  sDATA :: string>%Heading : Heading in

    (* let SearchTerm := @BuildIndexSearchTerm heading *)
    (*                     [{| *)
    (*                         KindIndexKind := StringId2; *)
    (*                         KindIndexIndex := BStringId2 |}] :  *)
    (*                     Type in *)

    (* TODO *)
    let SearchTerm := @BuildIndexSearchTerm heading
                  (@Datatypes.cons (@KindIndex heading)
                     (@Build_KindIndex heading StringId2 BStringId2)
                     (@Datatypes.nil (@KindIndex heading)))
                  (prod (option (Domain heading BStringId2))
                     (@Tuple heading -> bool)) : Type in
    (* TODO *)
    (* let SearchUpdateTerm := {| *)
    (*       BagSearchTermType := SearchTerm; *)
    (*       BagMatchSearchTerm := MatchIndexSearchTerm; *)
    (*       BagUpdateTermType := Tuple -> Tuple; *)
    (*       BagApplyUpdateTerm := fun z : Tuple -> Tuple => z |} *)
    (*                         : SearchUpdateTerms heading in *)

let  SearchUpdateTerm := @Build_SearchUpdateTerms heading SearchTerm
                        (@MatchIndexSearchTerm heading
                           (@Datatypes.cons (@KindIndex heading)
                              (@Build_KindIndex heading StringId2 BStringId2)
                              (@Datatypes.nil (@KindIndex heading)))
                           (prod (option (Domain heading BStringId2))
                              (@Tuple heading -> bool))
                           (fun
                              (st : prod (option (Domain heading BStringId2))
                                      (@Tuple heading -> bool))
                              (tup : @Tuple heading) =>
                            andb
                              match
                                @fst (option (Domain heading BStringId2))
                                  (@Tuple heading -> bool) st 
                                return bool
                              with
                              | Some val =>
                                  match
                                    @list_eq_dec string string_dec
                                      (@GetAttribute heading tup BStringId2)
                                      val return bool
                                  with
                                  | left _ => true
                                  | right _ => false
                                  end
                              | None => true
                              end
                              (@snd (option (Domain heading BStringId2))
                                 (@Tuple heading -> bool) st tup)))
                        (@Tuple heading -> @Tuple heading)
                        (fun z : @Tuple heading -> @Tuple heading => z)
                   : SearchUpdateTerms heading in

    let BStringId0 := ``(sNAME) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in
    let BStringId1 := ``(sTYPE) : BoundedIndex [sNAME; sTYPE; sCLASS; sTTL; sDATA] in

    let schma := {|
          schemaHeading := heading;
          attrConstraints := None;
          tupleConstraints := Some
                                (fun t t' : Tuple =>
                                   @GetAttribute heading t BStringId0 =
                                   @GetAttribute heading t' BStringId0 ->
                                   @GetAttribute heading t BStringId1 <> CNAME) |}
                 : Schema in
    let   nschma := relation sCOLLECTIONS has (schma)%NamedSchema : NamedSchema in

  (* TODO *)
    (* let Index := icons SearchUpdateTerm *)
    (*                    (inil *)
    (*                       (fun ns : NamedSchema => *)
    (*                          SearchUpdateTerms (schemaHeading (relSchema ns)))) *)
    (*               : ilist *)
    (*                  (fun ns : NamedSchema => *)
    (*                     SearchUpdateTerms (schemaHeading (relSchema ns))) *)
    (*                  [nschma] in *)

  let Index := @icons NamedSchema
             (fun ns : NamedSchema =>
              SearchUpdateTerms (schemaHeading (relSchema ns))) nschma
             (@Datatypes.nil NamedSchema) SearchUpdateTerm
             (@inil NamedSchema
                (fun ns : NamedSchema =>
                 SearchUpdateTerms (schemaHeading (relSchema ns))))
        : @ilist NamedSchema
            (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns)))
            (@Datatypes.cons NamedSchema nschma (@Datatypes.nil NamedSchema)) in

  forall (a : IndexedEnsemble * list Tuple) (d : packet) (r_n : IndexedQueryStructure DnsSchema Index),

    (* hypothesis 1 *)
        (
    @CallBagMethod DnsSchema Index BStringId BagFind r_n
                  (None,
                   fun y : Tuple =>
                     ?[IsSuffix_dec (qname (questions d)) (@GetAttribute heading y BStringId0)])
                  ↝ a) ->

    (* hypothesis 2 *)
    forall (n' : DNSRRecord),
      List.In n' (snd a) ->

      (* conclusion *)
      IsPrefix (get_name n') (qname (questions d)).
Proof.
  intros.
  inv H.
  inv H1.
  inv H2.
  unfold BagMatchSearchTerm in H0.
  simpl in H0.
  unfold MatchIndexSearchTerm in H0.
  simpl in H0.
  
  unfold IsSuffix_dec in H0.
  unfold GetAttribute in H0.
  (* simpl in H0. *)

  apply filter_In in H0.
 (* Set Printing All. *)
  inv H0.

(* TODO fix *)
  destruct ( @IsPrefix_dec string FindSuffixSearchTerms.Astring_eq
             (@ith_Bounded Attribute string attrName attrType
                (AttrList heading) n' BStringId0) (qname (questions d))).
  apply i.
  inversion H2.
Qed.

(* -------------------------------------------------------------------------------------- *)

(* TODO: working on this code; please excuse the comments *)

Print MostlySharpened.

Theorem DnsManual :
  MostlySharpened DnsSpec.
Proof.

  (* the two components here (start honing + GenerateIndexesForAll) are manual versions of
     partial_master_plan' in AutoDB *)

(*
  unfold DnsSpec.

start sharpening ADT. {
  hone method "Process". {
    Check refine_check_one_longest_prefix_CNAME.

 simplify with monad laws.
    (* implement_Query             (* in AutoDB, implement_Query' has steps *)
      ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                           ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep). *)
    (* simplify with monad laws. *)
    (* Find the upperbound of the results. *)
    etransitivity.
    apply refine_under_bind; intros.
    (* rewrite map_app, map_map, app_nil_r, map_id; simpl. *)
    match goal with
      |- refine _ (?H _) => let id := fresh in set (id := H) in *
    end. (* rename ?whatever to H(number) *)
    setoid_rewrite refine_If_Then_Else_Bind.
    (* Should honing if branches also be their own tactic? *)
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
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

{
      apply refine_bind;
      [ apply refine_check_one_longest_prefix_s | intro; higher_order_reflexivity ].
      intros. clear H. clear H1. admit.
    }
    simplify with monad laws.
    setoid_rewrite refine_if_If.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
    etransitivity.
    { apply refine_bind;
      [ eapply refine_check_one_longest_prefix_CNAME | intro; higher_order_reflexivity ].

      (* [for] query in H0 *)
      inversion H0.
      (* need a lemma for reasoning about tuples that result from [for] clauses *)
      (* for ... ~> a <=> a satisfies... *)
      inversion H2. clear H2.
      (* sub-lemma: [a] is included in the enumeration of scollections *)
      Print QueryStructure.
      (* crossConstr = data struct x constraint *)
      Print Relation.
      (* two kinds of constraints, attr and tuple -- want to use tupleconstr *)
      (* a in scollection -> a in rel -> tuple part of scollections *)
      (* need a lemma about it; constraints *****TODO***** *)
      (* use constraints to justify further refinements -- conditional refinements / preconditions -- e.g. the lemma *)
      (* "no one else can do this as cleanly as we can *)

      (* ----------- this stuff was copied from the end of the file *)
    
*)
  (* unfold MostlySharpened. *)
  start honing QueryStructure. (* what does this do? what's the stuff in the context? *)
  (* drops the proofs for data integrity *)

  (* Implement the constraint checks as queries. *)
  (* original: update "AddData" (t : DNSRRecord) : bool :=
      Insert t into sCOLLECTIONS *)
  (* mutates, so need to check constraints on NAME/CNAME *)

  (* TODO: hone this first here instead? *)
hone method "Process".
{
  finish honing.
}

  hone method "AddData".        (* ? *)
  {
    (* AddData has been expanded in method StringId0 *)
    (* refine (AddData body) (H r_n n) <-- what is that? *)
    (* H := existential variable of the correct (?) type,
       r_n : UnConstrQueryStructure DnsSchema, n : DNSRRecord*)
    (* x1 = check constraint between n (the record) and every other tuple  *)
    (* x2 = check constraint between every other tuple and n (the record) *)
    (* doesn't know that the constraint is symmetric? *)

    (* one-liner with rewrites? *)
    subst_all.
    match goal with
      |- refine _ (?H _ _) => let id := fresh in set (id := H) in *
    end.                        (* replace ex var with name H again *)
    setoid_rewrite refine_count_constraint_broken.        (* refine x1 *)
    setoid_rewrite refine_count_constraint_broken'.        (* refine x2 *)
    Check refine_If_Then_Else_Bind.
    Check Bind_refine_If_Then_Else.
    setoid_rewrite refine_If_Then_Else_Bind.
    setoid_rewrite Bind_refine_If_Then_Else.
    etransitivity.
    Check refine_If_Then_Else.
    apply refine_If_Then_Else.
    - simplify with monad laws.
      apply refine_under_bind; intros. (* x0 disappears? *)
      Check refine_Count.
      setoid_rewrite refine_Count; simplify with monad laws.
      apply refine_under_bind; intros.
      (* remove duplicate check *)
      (* (simplifies x1) *)
      setoid_rewrite refine_subcheck_to_filter; eauto.
      simplify with monad laws.
      rewrite clear_nested_if by apply filter_nil_is_nil.
      (* removes one of the repeated rets, and the filter dec -- how? *)
      higher_order_1_reflexivity. (* ? where did the next goal come from? *)
      eauto with typeclass_instances.
    - simplify with monad laws.
      reflexivity.              (* refine (code) (existential variable) is cleared by reflexivity *)
    - finish honing.            (* can finish honing anywhere? *)
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
  (*  *)

  (* hone constructor "Init". *)
  { 
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    finish honing.
   }

  (* why stop honing AddData, hone Init, then come back to this? *)
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
        implement_Insert_branches.
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
    - reflexivity.
    - finish honing.
    }

  (* hone method "Process". *) {
    (* this looks different from the Process method in DnsSpec. how was it changed so far?? *)
    (* maybe if i remove GenerateIndexesForAll and admit the other cases and do this one, it'll look the same? *)
    (* where are x0 and x1 coming from? *)
    (* where's ret (buildempty p)? *)
    simplify with monad laws.
    implement_Query             (* in AutoDB, implement_Query' has steps *)
      ltac:(CombineCase5 SuffixIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlySuffixTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastSuffixTerm createLastEqualityTerm)
                           ltac:(CombineCase7 SuffixIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlySuffixTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastSuffixTerm_dep createLastEqualityTerm_dep).
    simplify with monad laws.
    (* Find the upperbound of the results. *)
    etransitivity.
    apply refine_under_bind; intros.
    rewrite map_app, map_map, app_nil_r, map_id; simpl.
    match goal with
      |- refine _ (?H _) => let id := fresh in set (id := H) in *
    end. (* rename ?whatever to H(number) *)
    setoid_rewrite refine_If_Then_Else_Bind.
    (* Should honing if branches also be their own tactic? *)
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
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
    { 
      apply refine_bind;
      [ apply refine_check_one_longest_prefix_s; clear H2 H0;
        eapply found_names_are_prefixes_of_question; apply H1
      | intro; higher_order_reflexivity ].
    }
    simplify with monad laws.
    setoid_rewrite refine_if_If.
    setoid_rewrite refine_If_Then_Else_Bind.
    etransitivity.
    apply refine_If_Then_Else.
    simplify with monad laws.
    etransitivity.
    { apply refine_bind;
      [ eapply refine_check_one_longest_prefix_CNAME; clear H2 H0 | intro; higher_order_reflexivity ].
      (* result of data integrity constraints *)
      (*  where (fun t t' => t!sNAME = t'!sNAME -> t!sTYPE <> CNAME) ] *)
      (* are the hypotheses here the dynamic check? *)
      Print nth_error.          (* ? *)
      intros.
      admit.

      (* should prove it earlier? where? already dropped the proof -- where? *)
      (* drop condition before honing? *)

      instantiate (1 := qname (questions d)).
      eapply found_names_are_prefixes_of_question; apply H1.
    }
    simplify with monad laws.
    apply refine_If_Opt_Then_Else_Bind.
    setoid_rewrite (@refine_filtered_list _ _ _ _).
    simplify with monad laws.
    refine pick val _; eauto.
    simplify with monad laws.
    reflexivity.
    simpl.
    apply refine_If_Then_Else.
    eapply refine_If_Opt_Then_Else.
    intro; simplify with monad laws.
    refine pick val _; eauto.
    simplify with monad laws.
    higher_order_reflexivity.
    simplify with monad laws.
    refine pick val _; eauto.
    simplify with monad laws.
    higher_order_reflexivity.
    higher_order_reflexivity.
    simplify with monad laws.
    refine pick val _; eauto.
    simplify with monad laws.
    higher_order_reflexivity.
    unfold H2.
    higher_order_reflexivity.
    simpl.
    finish honing.
  } (* ends here *)
  
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
