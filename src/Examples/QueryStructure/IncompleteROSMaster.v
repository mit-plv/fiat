Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition int := nat.
Definition ERROR := 2. (* should have been defined as -1 *)
Definition FAILURE := 0.
Definition SUCCESS := 1.

Definition any := string.

Definition sSUBSCRIPTIONS := "Subscriptions".
Definition sPUBLICATIONS := "Publications".
Definition sSERVICES := "Services".
Definition sTOPICS := "Topics".
Definition sTOPIC := "topic".
Definition sNODE_ID := "node_id".
Definition sNODE_API := "node_api".
Definition sSERVICE_API := "service_api".
Definition sSERVICE := "service".
Definition sTOPIC_TYPE := "topic_type".
Definition sNODES := "Nodes".
Definition sPARAMS := "Parameters".
Definition sKEY := "key".
Definition sVALUE := "value".
Definition sPARAMSUBSCRIPTIONS := "ParamSubscriptions".

(* what happen if the same tuple is repeatedly inserted in sNODES? *)
(* want drop it when the same thing comes in *)

Definition DuplicateFree {heading} (tup1 tup2 : @RawTuple heading) := tup1 <> tup2.

Fixpoint BuildFinUpTo (n : nat) {struct n} : list (Fin.t n) :=
  match n return list (Fin.t n) with
  | 0  => nil
  | S n' => cons (@Fin.F1 _) (map (@Fin.FS _) (BuildFinUpTo n'))
  end.

Definition allAttributes heading
  : list (Attributes heading) :=
  BuildFinUpTo (NumAttr heading).

Lemma refine_DuplicateFree
      {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx tup',
    refine
      {b : bool |
       decides b
               (forall tup : IndexedElement,
                   GetUnConstrRelation qs Ridx tup ->
                   DuplicateFree tup' (indexedElement tup))}
      (xs <- For (UnConstrQuery_In qs Ridx
                           (fun tup => Where (tupleAgree_computational tup' tup (allAttributes _) )
                                             Return ()));
       ret (if hd_error xs then true else false)).
Proof.
Admitted.

Lemma refine_DuplicateFree_symmetry
      {qsSchema}
  : forall (qs : UnConstrQueryStructure qsSchema) Ridx tup' b',
    computes_to {b : bool | decides b
                                     (forall tup : IndexedElement,
                                         GetUnConstrRelation qs Ridx tup ->
                                         DuplicateFree tup' (indexedElement tup)  )} b'
    -> refine
         {b : bool |
          decides b
                  (forall tup : IndexedElement,
                      GetUnConstrRelation qs Ridx tup ->
                      DuplicateFree (indexedElement tup) tup')}
         (ret b').
Proof.
Admitted.

Ltac implement_DuplicateFree :=
  match goal with
    |- context [{b : bool |
                 decides b
                         (forall tup' : IndexedElement,
                             GetUnConstrRelation ?r ?Ridx tup' ->
                                 DuplicateFree ?tup (indexedElement tup'))}] =>
    rewrite (@refine_DuplicateFree _ r Ridx)
  end.

Ltac implement_DuplicateFree_symmetry :=
  match goal with
    |- context [{b : bool |
                 decides b
                         (forall tup' : IndexedElement,
                             GetUnConstrRelation ?r ?Ridx tup' ->
                                 DuplicateFree  (indexedElement tup') ?tup)}] =>
    rewrite (@refine_DuplicateFree_symmetry _ r Ridx)
  end.


Definition stringPrefix str str' : Prop :=
  prefix str str' = true.

Instance prefixDecideable {B} (f : B -> _) str'
    : DecideableEnsemble (fun str => stringPrefix (f str) str')
    := { dec str := prefix (f str) str'}.
  intros.
  unfold stringPrefix. destruct (prefix (f a) str'); simpl; split; eauto.
Defined.

Instance prefixDecideable' {B} (f : B -> _) str'
  : DecideableEnsemble (fun str => stringPrefix str' (f str))
    := { dec str := prefix str' (f str)}.
  intros.
  unfold stringPrefix. destruct (prefix str' (f a)); simpl; split; eauto.
Defined.

Ltac PickIndexes BuildEarlyIndex BuildLastIndex :=
GenerateIndexesForAll
   EqExpressionAttributeCounter
   ltac:(fun attrlist =>
           let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in make_simple_indexes attrlist' BuildEarlyIndex BuildLastIndex).


Ltac implement_nested_Query
         CreateTerm EarlyIndex LastIndex
         makeClause_dep EarlyIndex_dep LastIndex_dep :=
    Focused_refine_Query;
      [ match goal with
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
      etransitivity;
        [ let H' := (eval simpl in (@refine_UnConstrQuery_In resultT _ r_o idx)) in
          eapply H'; intro;
          implement_Query CreateTerm EarlyIndex LastIndex
                          makeClause_dep EarlyIndex_dep LastIndex_dep;
          simpl; repeat first [setoid_rewrite refine_bind_unit
                              | setoid_rewrite refine_bind_bind ];
          simplify with monad laws; finish honing
        | let H' := eval simpl in (refine_Filtered_Query_In_Enumerate (ResultT := resultT) H (idx := idx)) in
              apply H']

    end | ].


    Lemma List_Query_In_Return' :
      forall (n : nat) (ResultT : Type) (headings : Vector.t RawHeading n) (f f' : _ -> Comp (list ResultT))
             (l : list (ilist2 (B := @RawTuple) headings)),
        (forall tup, refine (f tup) (f' tup))
        -> refine (List_Query_In l f)
                  (List_Query_In l f').
    Admitted.

    Ltac Implement_Nested_Query_In :=
      let r_o' := fresh "r_o'" in
      let AbsR_r_o' := fresh "AbsR_r_o'" in
      let refines_r_o' := fresh "refines_r_o'" in
      match goal with
      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls _ _
        |- refine (Bind (List_Query_In ?l ?f) ?k) _ =>
        setoid_rewrite (@List_Query_In_Return' _ _ _ f _ l);
          [ | intros; repeat Implement_Bound_Bag_Call; finish honing];
          setoid_rewrite List_Query_In_Return
      end.

    Ltac implement_bag_methods :=
      etransitivity;
      [ repeat (first [
                    simpl; simplify with monad laws
                  | remove_spurious_Dep_Type_BoundedIndex_nth_eq
                  | Implement_If_Then_Else
                  | Implement_If_Opt_Then_Else
                  | Implement_Bound_Bag_Call
                  | Implement_Bound_Join_Comp_Lists
                  | Implement_Bound_Join_Comp_Lists'
                  | Implement_AbsR_Relation
                  | match goal with
                      |- context[CallBagImplMethod _ _ _ _ _] =>
                      unfold CallBagImplMethod; cbv beta; simpl
                    end
                  | Implement_Nested_Query_In
                  | higher_order_reflexivity ]; simpl) |];
      (* Clean up any leftover CallBagImplMethods *)
      repeat (cbv beta; simpl;
              match goal with
                |- appcontext[CallBagImplMethod] =>
                unfold CallBagImplMethod; cbv beta; simpl;
                try remove_spurious_Dep_Type_BoundedIndex_nth_eq
              end);
      higher_order_reflexivity.


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
        |- context [@Build_IndexedQueryStructure_Impl_Sigs _ ?indices ?SearchTerms _] => try unfold SearchTerms
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

Ltac implement_insert' CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
        repeat first
         [simplify with monad laws; simpl
         | setoid_rewrite refine_If_Then_Else_Bind
         | match goal with
             H : DelegateToBag_AbsR ?r_o ?r_n
             |- context[Pick (fun idx => UnConstrFreshIdx (GetUnConstrRelation ?r_o ?Ridx) idx)] =>
             let freshIdx := fresh in
             destruct (exists_UnConstrFreshIdx H Ridx) as [? freshIdx];
               setoid_rewrite (refine_Pick_UnConstrFreshIdx H Ridx freshIdx)
           end
         | etransitivity; [eapply refine_BagADT_QSInsert'; [ eassumption
                                                           | eauto
                                                           | intros ] | set_evars ]
         | implement_Query CreateTerm EarlyIndex LastIndex
                           makeClause_dep EarlyIndex_dep LastIndex_dep
         |  setoid_rewrite refine_Pick_DelegateToBag_AbsR; [ | solve [ eauto ] .. ] ].


Opaque QSInsert.
Opaque UpdateUnconstrRelationC.

Definition RosMasterSchema :=
    Query Structure Schema
    [
      relation sNODES has
               schema <sNODE_ID :: string, sNODE_API :: string>;

      relation sTOPICS has
                schema <sTOPIC :: string, sTOPIC_TYPE :: string>;

      relation sPARAMS has
                schema <sKEY :: string, sVALUE :: any>;

      relation sSUBSCRIPTIONS has
                schema <sNODE_ID :: string, sTOPIC :: string>;

      relation sPARAMSUBSCRIPTIONS has
                schema <sNODE_ID :: string, sKEY :: string>;

      relation sPUBLICATIONS has
                schema <sNODE_ID :: string, sTOPIC :: string>;

      relation sSERVICES has
                schema <sNODE_ID :: string, sSERVICE :: string, sSERVICE_API :: string>
    ]
    enforcing [ ].



Definition RosMasterSpec : ADT _ :=
  Eval simpl in
    QueryADTRep RosMasterSchema {

    Def Constructor0 "Init" : rep := empty

    ,

    Def Method4 "registerSubscriber"
      (r : rep) (caller_id : string) (topic : string) (topic_type : string) (caller_api : string)
      : rep * (int * string * list string)%type
      :=
        res1 <- Insert <sNODE_ID :: caller_id, sTOPIC :: topic> into r ! sSUBSCRIPTIONS;

        if (snd res1) then
          (res2 <- Insert <sNODE_ID :: caller_id, sNODE_API :: caller_api> into (fst res1) ! sNODES;
           if (snd res2) then
             (res3 <- Insert <sTOPIC :: topic, sTOPIC_TYPE :: topic_type> into (fst res2) ! sTOPICS;
              if snd res3 then
                (publishers <- For (pub in r ! sPUBLICATIONS) (node in r ! sNODES)
                            Where ( pub ! sTOPIC = topic  /\  pub ! sNODE_ID = node ! sNODE_ID )
                            Return ( node ! sNODE_API );
                 ret(fst res3, (SUCCESS, "You are now subscribed.  Publishers are:", publishers)))
              else
                ret(r, (FAILURE, "That topic exists but with a different type.", [])))
           else
             ret(r, (FAILURE, "That node exists but with a different api.", [])))
        else
          ret(r, (FAILURE, "You are already subscribed to that topic.", []))
    ,

    Def Method4 "registerPublisher"
      (r : rep) (caller_id : string) (topic : string) (topic_type : string) (caller_api : string)
      : rep * (int * string * list string)%type
      :=
        res1 <- Insert <sNODE_ID :: caller_id, sTOPIC :: topic> into r ! sPUBLICATIONS;
        If snd res1 Then
           (res2 <- Insert <sNODE_ID :: caller_id, sNODE_API :: caller_api> into (fst res1) ! sNODES;
            If snd res2 Then
               (res3 <- Insert <sTOPIC :: topic, sTOPIC_TYPE :: topic_type> into (fst res2) ! sTOPICS;
                If snd res3 Then
                   subscribers <- For (sub in r ! sSUBSCRIPTIONS) (node in r ! sNODES)
                   Where ( sub ! sTOPIC = topic  /\  sub ! sNODE_ID = node ! sNODE_ID )
                   Return ( node ! sNODE_API );

                   ret(fst res3, (SUCCESS, "You are now publishing.  Subscribers are:", subscribers))
               Else
               ret(r, (FAILURE, "That topic exists but with a different type.", [])))
           Else
           ret(r, (FAILURE, "That node exists but with a different api.", [])))
           Else
           ret(r, (FAILURE, "You are already publishing to that topic.", [])),

    Def Method2 "lookupNode"
      (r : rep) (caller_id : string) (node_name : string)
      : rep * (int * string * string)%type
      (* Returns (code, statusMessage, URI) *)
      :=
        apis <- For (node in r ! sNODES)
              Where ( node ! sNODE_ID = node_name )
              Return ( node ! sNODE_API );

        api <- ret (List.hd "" apis);
        c <- ret (List.length apis); (* should be either 0 or 1 *)

        if beq_nat c 0 then
          ret (r, (FAILURE, "Node not found.", api))
        else
          ret (r, (SUCCESS, "Node URI is :", api))
    ,

    Def Method2 "getPublishedTopics"
      (r : rep) (caller_id : string) (subgraph : string)
      : rep * (int * string * list (string * string))%type
      (* Returns (code, statusMessage, [(topic,type)]) *)
                                                           :=
        res <- For (topic in r ! sTOPICS) (pub in r ! sPUBLICATIONS)
            Where ( topic ! sTOPIC = pub ! sTOPIC)
            Where (stringPrefix topic!sTOPIC subgraph )
              Return ( (topic ! sTOPIC, topic ! sTOPIC_TYPE) );
        ret (r, (SUCCESS, "Topics with publishers are :", res))  (* should remove duplicates *)
    ,

    Def Method1 "getTopicTypes"
      (r : rep) (caller_id : string)
      : rep * (int * string * list (string * string))%type
      :=
        res <- For (topic in r ! sTOPICS)
              Return ( (topic ! sTOPIC, topic ! sTOPIC_TYPE) );
        ret (r, (SUCCESS, "Topics are :", res))
    ,

    Def Method1 "getSystemState"
      (r : rep) (caller_id : string)
      : rep * (int * string * list (list (string * list string)) )%type
        :=
        publishers <- For (topic in r ! sTOPICS)
                 (
                   pubs <- For (pub in r ! sPUBLICATIONS)
                             Where (topic ! sTOPIC = pub ! sTOPIC)
                             Return (pub ! sNODE_ID);
                   Return ( (topic ! sTOPIC, pubs) )
                 );

        subscribers <- For (topic in r ! sTOPICS)
                 (
                   subs <- For (sub in r ! sSUBSCRIPTIONS)
                             Where (topic ! sTOPIC = sub ! sTOPIC)
                             Return (sub ! sNODE_ID);
                   Return ( (topic ! sTOPIC, subs) )
                 );

        services <- For (serv in r ! sSERVICES)
                      Return (serv ! sSERVICE, [serv ! sNODE_ID]);

        ret (r, (SUCCESS, "System state is :", [publishers; subscribers; services]))
    ,

    Def Method1 "getUri"
      (r : rep) (caller_id : string)
      : rep * (int * string * string)%type
      :=
        ret (r, (SUCCESS, "My URI is :", "http://localhost:11311"))
    ,

    Def Method2 "lookupService"
      (r : rep) (caller_id : string) (service : string)
      : rep * (int * string * string)%type
      :=
        ids <- For (serv in r ! sSERVICES)
              Where ( serv ! sSERVICE = service )
              Return ( serv ! sNODE_ID );

        id <- ret (List.hd "" ids);
        c <- ret (List.length ids); (* should be either 0 or 1 *)

        if beq_nat c 0 then (* could use 'match ... with' instead of if *)
          ret (r, (FAILURE, "No one is provind that service.", id))
        else
          ret (r, (SUCCESS, "Service provider is :", id))

}%methDefParsing.

(*raise_error.

Set Ltac Debug.
*)

Theorem SharpenedRosMaster :
  FullySharpened RosMasterSpec.
Proof.
  unfold RosMasterSpec.
  pose_string_hyps.
  start sharpening ADT.
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
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
  - simplify with monad laws.
    etransitivity.
    eapply QSInsertSpec_refine_subgoals; try eassumption; set_evars.
    + rewrite decides_True; finish honing.
    + simpl. refine pick val true; simpl; eauto; finish honing.
    + simpl. intros; refine pick val true; simpl; eauto; finish honing.
    + simpl. repeat foreignToQuery'. finish honing.
    + simpl. intros; finish honing.
    + simpl; intros; simplify with monad laws.
      etransitivity.
      eapply QSInsertSpec_refine_subgoals; try eassumption; set_evars.
      * simpl; rewrite decides_True; finish honing.
      * simpl. refine pick val true; simpl; eauto; finish honing.
      * simpl. intros; refine pick val true; simpl; eauto; finish honing.
      * simpl. repeat foreignToQuery'. finish honing.
      * simpl. intros; repeat (remove_trivial_fundep_insertion_constraints; simpl).
        finish honing.
      * simpl; intros; simplify with monad laws.
        etransitivity.
        { eapply QSInsertSpec_refine_subgoals; try eassumption; set_evars.
          * simpl; rewrite decides_True; finish honing.
          * simpl. refine pick val true; simpl; eauto; finish honing.
          * simpl. intros; refine pick val true; simpl; eauto; finish honing.
          * simpl. repeat foreignToQuery'. finish honing.
          * simpl. intros; repeat (remove_trivial_fundep_insertion_constraints; simpl).
            finish honing.
          * simpl; intros.
            simplify with monad laws; cbv beta; simpl.
            drop_constraints_from_query.
          * intros; simpl; simplify with monad laws.
            simpl; refine pick val _; try eassumption.
            simplify with monad laws; finish honing.
        }
        simplify with monad laws.
        repeat setoid_rewrite refine_if_Then_Else_Duplicate.
        finish honing.
      * intros; simpl; simplify with monad laws.
        simpl; refine pick val _; try eassumption.
        simplify with monad laws; finish honing.
      * intros; simpl; simplify with monad laws.
        repeat setoid_rewrite refine_if_Then_Else_Duplicate.
        finish honing.
    + intros; simpl; simplify with monad laws.
      simpl; refine pick val _; try eassumption.
      simplify with monad laws; finish honing.
    + intros; simpl; simplify with monad laws.
      finish honing.
  - simplify with monad laws.
    etransitivity.
    eapply QSInsertSpec_refine_subgoals; try eassumption; set_evars.
    + rewrite decides_True; finish honing.
    + simpl. refine pick val true; simpl; eauto; finish honing.
    + simpl. intros; refine pick val true; simpl; eauto; finish honing.
    + simpl. repeat foreignToQuery'. finish honing.
    + simpl. intros; finish honing.
    + simpl; intros; simplify with monad laws.
      etransitivity.
      eapply QSInsertSpec_refine_subgoals; try eassumption; set_evars.
      * simpl; rewrite decides_True; finish honing.
      * simpl. refine pick val true; simpl; eauto; finish honing.
      * simpl. intros; refine pick val true; simpl; eauto; finish honing.
      * simpl. repeat foreignToQuery'. finish honing.
      * simpl. intros; repeat (remove_trivial_fundep_insertion_constraints; simpl).
        finish honing.
      * simpl; intros; simplify with monad laws.
        etransitivity.
        { eapply QSInsertSpec_refine_subgoals; try eassumption; set_evars.
          * simpl; rewrite decides_True; finish honing.
          * simpl. refine pick val true; simpl; eauto; finish honing.
          * simpl. intros; refine pick val true; simpl; eauto; finish honing.
          * simpl. repeat foreignToQuery'. finish honing.
          * simpl. intros; repeat (remove_trivial_fundep_insertion_constraints; simpl).
            finish honing.
          * simpl; intros.
            simplify with monad laws; cbv beta; simpl.
            drop_constraints_from_query.
          * intros; simpl; simplify with monad laws.
            simpl; refine pick val _; try eassumption.
            simplify with monad laws; finish honing.
        }
        simplify with monad laws.
        repeat setoid_rewrite refine_if_Then_Else_Duplicate.
        finish honing.
      * intros; simpl; simplify with monad laws.
        simpl; refine pick val _; try eassumption.
        simplify with monad laws; finish honing.
      * intros; simpl; simplify with monad laws.
        repeat setoid_rewrite refine_if_Then_Else_Duplicate.
        finish honing.
    + intros; simpl; simplify with monad laws.
      simpl; refine pick val _; try eassumption.
      simplify with monad laws; finish honing.
    + intros; simpl; simplify with monad laws.
      finish honing.
  - drop_constraints_from_query.
  - drop_constraints_from_query.
  - drop_constraints_from_query.
  - drop_constraints_from_query.
  - drop_constraints_from_query.
  - drop_constraints_from_query.
  - GenerateIndexesForAll
   EqExpressionAttributeCounter
   ltac:(fun attrlist =>
           let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in make_simple_indexes attrlist'
                                                                                                               ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                                                                                                      ltac:(LastCombineCase5 BuildLastEqualityIndex)).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + implement_insert' EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                        EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep;
      doAny ltac:(implement_insert'
                    EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                    EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
                   rewrite_drill ltac:(finish honing).
    + implement_insert' EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                        EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep;
      doAny ltac:(implement_insert'
                    EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                    EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
                   rewrite_drill ltac:(finish honing).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + implement_nested_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                             EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
      implement_nested_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                             EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
      implement_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                      EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
      simplify with monad laws.
      cbv beta; simpl; commit.
      finish honing.
    + simplify with monad laws; simpl.
      refine pick val _; eauto.
      simplify with monad laws.
      finish honing.
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + Finish_Master BuildEarlyBag BuildLastBag.
Time Defined.


Time Definition ROSMasterImpl : ComputationalADT.cADT _ :=
  Eval simpl in projT1 SharpenedRosMaster.

Print BookstoreImpl.
