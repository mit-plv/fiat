Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Fiat.QueryStructure.Specification.Constraints.DuplicateFree.

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

Opaque QSInsert.
Opaque QSDelete.
Opaque UpdateUnConstrRelationInsertC.
Opaque UpdateUnConstrRelationDeleteC.

Definition RosMasterSchema :=
  Query Structure Schema
        [
          relation sNODES has
                   schema <sNODE_ID :: string, sNODE_API :: string>
          where attributes [sNODE_API] depend on [sNODE_ID];

            relation sTOPICS has
                     schema <sTOPIC :: string, sTOPIC_TYPE :: string>
          where attributes [sTOPIC_TYPE] depend on [sTOPIC];

            relation sPARAMS has
                     schema <sKEY :: string, sVALUE :: any>
          where attributes [sVALUE] depend on [sKEY];

            relation sSUBSCRIPTIONS has
                     schema <sNODE_ID :: string, sTOPIC :: string>
          where DuplicateFree;

            relation sPARAMSUBSCRIPTIONS has
                     schema <sNODE_ID :: string, sKEY :: string>
          where DuplicateFree;

            relation sPUBLICATIONS has
                     schema <sNODE_ID :: string, sTOPIC :: string>
          where DuplicateFree;

            relation sSERVICES has
                     schema <sNODE_ID :: string, sSERVICE :: string, sSERVICE_API :: string>
          where attributes [sNODE_ID; sSERVICE_API] depend on [sSERVICE]
        ]
        enforcing [ attribute sNODE_ID for sSUBSCRIPTIONS references sNODES;
                    attribute sTOPIC for sSUBSCRIPTIONS references sTOPICS;
                    attribute sNODE_ID for sPUBLICATIONS references sNODES;
                    attribute sTOPIC for sPUBLICATIONS references sTOPICS;
                    attribute sNODE_ID for sPARAMSUBSCRIPTIONS references sNODES;
                    attribute sKEY for sPARAMSUBSCRIPTIONS references sPARAMS ].

Definition RosMasterSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,

      (* register/unregister methods *)

      Method "registerService" : rep * string * string * string * string
                                    -> rep * (int * string * int),

      Method "unregisterService" : rep * string * string * string
                                    -> rep * (int * string * int),

      Method "registerSubscriber" : rep * string * string * string * string
                                    -> rep * (int * string * list string),

      Method "unregisterSubscriber" : rep * string * string * string
                                      -> rep * (int * string * int),

      Method "registerPublisher" : rep * string * string * string * string
                                    -> rep * (int * string * list string),

      Method "unregisterPublisher" : rep * string * string * string
                                      -> rep * (int * string * int),

      (* name service and system state *)

      Method "lookupNode" : rep * string * string
                          -> rep * (int * string * string),

      Method "getPublishedTopics" : rep * string * string
                          -> rep * (int * string * list (string * string)),

      Method "getTopicTypes" : rep * string
                               -> rep * (int * string * list (string * string)),

      Method "getSystemState" : rep * string
                          -> rep * (int * string * list ( list (string * list string) ) ),

      Method "getUri" : rep * string
                          -> rep * (int * string * string),

      Method "lookupService" : rep * string * string
                          -> rep * (int * string * string),

      (* parameter server API *)

      Method "deleteParam" : rep * string * string
                             -> rep * (int * string * int),

      Method "setParam" : rep * string * string * any
                          -> rep * (int * string * int),

      Method "getParam" : rep * string * string
                          -> rep * (int * string * any),

      Method "searchParam" : rep * string * string
                             -> rep * (int * string * string),

      Method "subscribeParam" : rep * string * string * string
                              -> rep * (int * string * any),

      Method "unsubscribeParam" : rep * string * string * string
                                  -> rep * (int * string * int),

      Method "hasParam" : rep * string * string
                          -> rep * (int * string * bool),

      Method "getParamNames" : rep * string
                               -> rep * (int * string * list string)
  }.

Definition RosMasterSpec : ADT RosMasterSig :=
  Eval simpl in
    Def ADT {
      rep := QueryStructure RosMasterSchema,

    Def Constructor0 "Init" : rep := empty,,

    Def Method4 "registerService"
      (r : rep) (caller_id : string) (service : string) (service_api : string) (caller_api : string)
      : rep * (int * string * int)%type
      :=

        res1 <- Insert <sNODE_ID::caller_id, sSERVICE::service_api, sNODE_API::caller_api> into r ! sSERVICES;
        If snd res1 Then
          res2 <- Insert <sNODE_ID :: caller_id, sNODE_API :: caller_api> into (fst res1) ! sNODES;
          If snd res2 Then
            ret(fst res2, (SUCCESS, "Service registered.", 0))
          Else
            ret(r, (FAILURE, "That node exists but with a different api.", 0))
        Else
          ret(r, (FAILURE, "That service is already being provided", 0))
    ,

    Def Method3 "unregisterService"
      (r : rep) (caller_id : string) (service : string) (service_api : string)
      : rep * (int * string * int)%type
      :=
        res1 <- Delete serv from r ! sSERVICES
                where (serv ! sNODE_ID = caller_id /\ serv ! sSERVICE = service /\ serv ! sSERVICE_API = service_api );

        c1 <- ret (List.length (snd res1));

        (* c1 should be either 0 or 1. How can it be guaranteed?*)

        if beq_nat c1 0 then
          ret (fst res1, (SUCCESS, "Service was not registered in the first place.", c1))
        else
          ret (fst res1, (SUCCESS, "Service unsubscribed.", c1))
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

    Def Method3 "unregisterSubscriber"
      (r : rep) (caller_id : string) (topic : string) (caller_api : string)
      : rep * (int * string * int)%type
      :=
        res1 <- Delete sub from r ! sSUBSCRIPTIONS
                where (sub ! sNODE_ID = caller_id /\ sub ! sTOPIC = topic );

        c1 <- ret (List.length (snd res1)); (* or, c1 <- Count (ret (snd res1)); *)

        if beq_nat c1 0 then
          ret (fst res1, (SUCCESS, "You weren't subscribed to begin with.", c1))
        else
          ret (fst res1, (SUCCESS, "You are now unsubscribed.", c1))
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

    Def Method3 "unregisterPublisher"
      (r : rep) (caller_id : string) (topic : string) (caller_api : string)
      : rep * (int * string * int)%type
      :=
        res1 <- Delete pub from r ! sPUBLICATIONS
                where (pub ! sNODE_ID = caller_id /\ pub ! sTOPIC = topic );

        c1 <- ret (List.length (snd res1));

        if beq_nat c1 0 then
          ret (fst res1, (SUCCESS, "You weren't publishing to begin with.", c1))
        else
          ret (fst res1, (SUCCESS, "You are now unregistered.", c1))
    ,

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
          ret (r, (SUCCESS, "Service provider is :", id)),

            Def Method2 "deleteParam"
      (r : rep) (caller_id : string) (key : string)
      : rep * (int * string * int)%type
      :=
        res <- Delete param from r ! sPARAMS
                where (param ! sKEY = key);
        ret (fst res, (SUCCESS, "Parameter deleted", 0))
    ,

    Def Method3 "setParam"
      (r : rep) (caller_id : string) (key : string) (value : any)
      : rep * (int * string * int)%type
      :=
        res1 <- Delete param from r ! sPARAMS
                where (param ! sKEY = key);

        res2 <- Insert <sKEY :: key, sVALUE :: value> into (fst res1) ! sPARAMS;

        ret (fst res2, (SUCCESS, "Parameter set", 0))
    ,

    Def Method2 "getParam" (* not supported for key being a namespace *)
      (r : rep) (caller_id : string) (key : string)
      : rep * (int * string * any)%type
      := values <- For (param in r ! sPARAMS)
                    Where ( param ! sKEY = key )
                    Return ( param ! sVALUE  );
        Ifopt hd_error values as v
        Then
        ret (r, (SUCCESS, "Parameter value is :", v))
        Else
        ret (r, (FAILURE, "Parameter not set yet", ""))
    ,

    Def Method2 "searchParam" (* unimplemented *)
      (r : rep) (caller_id : string) (key : string)
      : rep * (int * string * string)%type
      := ret (r, (ERROR, "This API is not implemented.", ""))
    ,

    Def Method3 "subscribeParam"
      (r : rep) (caller_id : string) (caller_api : string) (key : string)
      : rep * (int * string * any)%type
      :=

        res1 <- Insert <sNODE_ID :: caller_id, sKEY :: key> into r ! sPARAMSUBSCRIPTIONS;
        If snd res1 Then
           res2 <- Insert <sNODE_ID :: caller_id, sNODE_API :: caller_api> into (fst res1) ! sNODES;
        If snd res2 Then
            values <- For (param in r ! sPARAMS)
                    Where ( param ! sKEY = key )
                    Return ( param ! sVALUE  );
        Ifopt hd_error values as v Then
           ret (fst res2, (SUCCESS, "Parameter is not set yet.", v))
           Else ret (fst res2, (SUCCESS, "Parameter value is :", ""))
          Else
            ret(r, (FAILURE, "That node exists but with a different api.", ""))
        Else
          ret(r, (FAILURE, "You are already subscribing to that parameter.", ""))
    ,

    Def Method3 "unsubscribeParam"
      (r : rep) (caller_id : string) (caller_api : string) (key : string)
      : rep * (int * string * int)%type
      :=
        res1 <- Delete paramsub from r ! sPARAMSUBSCRIPTIONS
                where (paramsub ! sNODE_ID = caller_id /\ paramsub ! sKEY = key);

        c1 <- ret (List.length (snd res1));

        if beq_nat c1 0 then
          ret (fst res1, (SUCCESS, "You weren't subscribed to begin with.", c1))
        else
          ret (fst res1, (SUCCESS, "You are now unsubscribed.", c1))
    ,

    Def Method2 "hasParam"
      (r : rep) (caller_id : string) (key : string)
      : rep * (int * string * bool)%type
      := values <- For (param in r ! sPARAMS)
                    Where ( param ! sKEY = key )
                    Return ();
        Ifopt hd_error values as _ Then
          ret (r, (SUCCESS, "Parameter is set.", true))
          Else ret (r, (FAILURE, "Parameter is not set.", false))
                             ,

    Def Method1 "getParamNames"
      (r : rep) (caller_id : string)
      : rep * (int * string * list string)%type
      :=
        keys <- For (param in r ! sPARAMS)
                  Return (param ! sKEY);
        ret (r, (SUCCESS, "Parameter names are :", keys))

}%methDefParsing.

(*raise_error.

Set Ltac Debug.
*)

Ltac implement_QSInsertSpec :=
  match goal with
    H : DropQSConstraints_AbsR ?r_o ?r_n
    |- refine (u <- QSInsert ?r_o ?Ridx ?tup;
               @?k u) _ =>
    eapply (@QSInsertSpec_refine_subgoals _ _ r_o r_n Ridx tup); try exact H
  end; try set_refine_evar;
  [  try rewrite decides_True; finish honing
   | simpl; repeat funDepToQuery; repeat implement_DuplicateFree; finish honing
   | simpl; intros; try set_refine_evar;
     repeat first [
              setoid_rewrite FunctionalDependency_symmetry';
              [ | solve [ eauto ] ]
            | implement_DuplicateFree_symmetry; [ | solve [ eauto ] ]
            | funDepToQuery
            | implement_DuplicateFree]; eauto;
     finish honing
   | simpl; repeat foreignToQuery'; finish honing
   |  simpl; intros; try set_refine_evar;
      repeat (remove_trivial_fundep_insertion_constraints; simpl);
      finish honing
   | simpl; intros; try set_refine_evar;
     try simplify with monad laws
   | simpl; intros; try set_refine_evar;
     try simplify with monad laws].

Ltac implement_QSDeleteSpec :=
  match goal with
    H : DropQSConstraints_AbsR ?r_o ?r_n
    |- refine (u <- QSDelete ?r_o ?Ridx ?DeletedTuples;
               @?k u) _ =>
    eapply (@QSDeleteSpec_refine_subgoals _ _ r_o r_n Ridx _ _ _ _ DeletedTuples k); try exact H
  end; try set_refine_evar;
  [ simpl; repeat RemoveDeleteDuplicateFreeCheck;
    repeat RemoveDeleteFunctionalDependencyCheck
  | simpl; repeat ImplementDeleteForeignKeysCheck
  | simpl; intros; set_refine_evar
  | simpl; intros; set_refine_evar
  ].

Ltac master_rewrite_drill :=
  subst_refine_evar;
  first
    [ try set_refine_evar; implement_QSInsertSpec
    | try set_refine_evar; implement_QSDeleteSpec
    | eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else;
      [intro; set_refine_evar | set_refine_evar ] ].

Ltac implement_DropQSConstraints_AbsR :=
  simpl; intros;
  try simplify with monad laws; cbv beta; simpl;
  simpl; refine pick val _; [ | eassumption].

Ltac drop_constraints_from_query' :=
  match goal with
    [ H : DropQSConstraints_AbsR ?r_o ?r_n
      |- context [Query_In ?r_o _ _] ] =>
    setoid_rewrite (DropQSConstraintsQuery_In r_o);
      rewrite !H
  end.

Ltac drop_constraints :=
  first
    [ simplify with monad laws
    | drop_constraints_from_query'
    | setoid_rewrite refine_If_Then_Else_Bind; simpl
    | setoid_rewrite refine_If_Opt_Then_Else_Bind; simpl
    | setoid_rewrite refine_if_Then_Else_Duplicate
    | implement_DropQSConstraints_AbsR].

Ltac progress_subgoal' top tac cont :=
  idtac "doAnyBreak"; top; (tac; try (cont ()) || (try (cont ()))).

(* ltac is call-by-value, so wrap the cont in a function *)
(* local definition in a_u_s *)
Ltac cont_fn' top tac'' x :=
  apply_under_subgoal' top tac'' with

  (* mutually recursive with progress_subgoal *)
  (* calls top on each subgoal generated, which may generate more subgoals *)
  (* fails when top fails in progress_subgoals *)
  apply_under_subgoal' top tac'' :=
    progress_subgoal' top tac'' ltac:(cont_fn' top tac'').

Ltac doAny' srewrite_fn drills_fn finish_fn :=
  let repeat_srewrite_fn := repeat srewrite_fn in
  try repeat_srewrite_fn;
    try apply_under_subgoal' drills_fn ltac:(repeat_srewrite_fn);
    finish_fn.

Ltac implement_Pick_DelegateToBag_AbsR :=
  match goal with
    [ H : DelegateToBag_AbsR ?r_o ?r_n
      |- context [ {r_n' |  DelegateToBag_AbsR ?r_o r_n'} ] ] =>
    setoid_rewrite (@refine_Pick_DelegateToBag_AbsR _ _ _ _ H)
  end.

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

Ltac implement_UpdateUnConstrRelationDeleteC find_search_term :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- refine (Bind (UpdateUnConstrRelationDeleteC ?r_o ?idx ?DeletedTuples) ?k) _ ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                    [ find_search_term qs_schema idx filter_dec search_term
                                    | let H' := fresh in
                                      pose proof (fun k' => @refine_BagADT_QSDelete' _ _ _ r_o r_n idx DeletedTuples k k' _ search_term eqv H) as H';
                                        fold_string_hyps_in H'; fold_heading_hyps_in H';
                                        eapply H'; clear H' eqv; set_evars])
  end.

Lemma hd_error_map:
  forall (A B: Type) (l : list A) (f : A -> B) ,
    hd_error (map f l) =
    match hd_error l with
    | Some a => Some (f a)
    | None => None
    end.
Proof.
  induction l; simpl; reflexivity.
Qed.

Ltac implement_insert' CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  first
    [simplify with monad laws; simpl
    | simpl; rewrite !map_app
    | simpl; rewrite !map_length
    | simpl; rewrite !app_nil_r
    | simpl; rewrite !map_map
    | simpl; rewrite !filter_map
    | simpl; rewrite !hd_error_map
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

Theorem SharpenedRosMaster :
  FullySharpened RosMasterSpec.
Proof.
  Unset Ltac Debug.
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
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny' ltac:(drop_constraints)
                  master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - simpl.
    GenerateIndexesForAll
      EqExpressionAttributeCounter
      ltac:(fun attrlist =>
              let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in make_simple_indexes attrlist'
                                                                                                                  ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                                                                                                         ltac:(LastCombineCase5 BuildLastEqualityIndex)).
    + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
           EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
      implement_nested_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                             EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
      doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
      implement_nested_Query EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                             EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
      doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
               ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
                      ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
        ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + doAny'
        ltac:(implement_insert'
                EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
                EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep)
               ltac:(master_implement_drill EqIndexUse createEarlyEqualityTerm createLastEqualityTerm)
               ltac:(repeat subst_refine_evar; try finish honing).
    + Finish_Master BuildEarlyBag BuildLastBag.
Time Defined.

Time Definition ROSMasterImpl : ComputationalADT.cADT _ :=
  Eval simpl in projT1 SharpenedRosMaster.

Print StringId7.

Print ROSMasterImpl.
