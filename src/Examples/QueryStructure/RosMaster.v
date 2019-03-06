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

Theorem SharpenedRosMaster :
  FullySharpened RosMasterSpec.
Proof.
  start sharpening ADT.
  start_honing_QueryStructure''.
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

Print ROSMasterImpl.
