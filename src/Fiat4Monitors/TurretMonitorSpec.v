Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements.

Section RADL_Definitions.

  Global Open Scope ADT_scope.
  Global Open Scope string_scope.
  Global Open Scope list_scope.
  Global Open Scope ADTSig_scope.

  Record RADL_Topic :=
    { Topic_Name : string;
      Topic_Type : Type }.

  Variable Topics : list RADL_Topic. (* List of Topics in the Network. *)
  Definition TopicID  := @BoundedString (map Topic_Name Topics).

  Record RADL_Node :=
    { (* Subscription + Publication info for this node *)
      RADL_Subscriptions : list TopicID;
      RADL_Publications : list TopicID
    }.

  Definition RADL_Init := "Init".
  Definition RADL_Step := "Step".

  Definition TopicTypes
             (topic : TopicID) : Type :=
    Topic_Type (nth_Bounded Topic_Name Topics topic).

  Definition Message topics :=
    ilist TopicTypes topics.

  Fixpoint SubTopic
           (topics : list TopicID)
           {struct topics}
  : Message topics ->
    forall (subtopic : BoundedIndex topics),
      TopicTypes (bindex subtopic).
  Proof.
    refine (match topics return
                  Message topics ->
                  forall (subtopic : BoundedIndex topics),
                    TopicTypes (bindex subtopic) with
              | nil => fun msg subtopic => BoundedIndex_nil _ subtopic
              | topic :: topics' =>  fun msg subtopic => _
            end).
    destruct subtopic as [idx [[ | n] nth_n]].
    simpl in *; injection nth_n; intros; subst.
    exact (ith_Bounded id msg {| bindex := _;
                                indexb := Build_IndexBound (idx :: (map id topics')) 0 nth_n|}).
    exact (SubTopic topics' (ilist_tl msg) {| bindex := idx;
                       indexb := {| ibound := n;
                                    boundi := nth_n |} |} ).
  Defined.

  Fixpoint SubMessage
             (topics : list TopicID)
             (subtopics : list (BoundedIndex  topics))
             (msg : Message topics)
  : Message (map (bindex (Bound := topics)) subtopics) :=
    match subtopics return Message (map (bindex (Bound := topics)) subtopics) with
      | nil => inil _
      | subtopic :: subtopics' =>
        icons _ (SubTopic msg subtopic )
              (SubMessage subtopics' msg)
    end.

  Definition RADL_ADTSig  (Node : RADL_Node)
  : ADTSig :=                         (* A RADL Node is modeled as an ADT with a  *)
    ADTsignature {                    (* single constructor and a step function. *)
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x Message (RADL_Subscriptions Node)
                                     -> rep x Message (RADL_Publications Node)
      }.

  Definition RADL_ADTSpec (Node : RADL_Node)
  : ADT (RADL_ADTSig Node) :=
    ADTRep unit (* Since RADL Nodes are untrusted, we'll treat their state as completely unknown *)
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : Message (RADL_Subscriptions Node)) : _ :=
               (* Again, since the RADL Node is untrusted code, we'll assume that it can publish
                  whatever the heck it wants. *)
               results <- {out_t : Message (RADL_Publications Node) | True };
             ret (tt, results) }.

  Definition RADLM_ADTSig
             (MonitorNode : RADL_Node)
             (InitDom : Type)
  : ADTSig :=
    ADTsignature {
        Constructor RADL_Init      : InitDom -> rep,
        Method      RADL_Step      : rep x unit * Message (RADL_Subscriptions MonitorNode)
                                     -> rep x unit * Message (RADL_Publications MonitorNode)
      }.

End RADL_Definitions.

Notation GetTopic il idx := (SubTopic il ``(``idx)).

Section Paintball.

  Require Bedrock.Platform.Facade.DFacade.

  Definition PaintballControlMode :=
    @BoundedString ["IDLE"; "SINGLE_SHOT"; "TRIPLE_SHOT"; "BURST"].

  (* This is the list of topics available in the system.*)
  Definition PaintballTopics :=
    [ {| Topic_Name := "TiltX"; Topic_Type := Memory.W |};
      {| Topic_Name := "TiltY"; Topic_Type := Memory.W |};
      {| Topic_Name := "Trigger"; Topic_Type := PaintballControlMode |};
      {| Topic_Name := "Fired"; Topic_Type := PaintballControlMode |}].

  (* Each RADL Node has a list of subscriptions and publications drawn
     from the list of available topics. *)
  Definition BarrelNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ``"Trigger"];
       RADL_Publications  := [ ``"Fired"] |}.
  Definition TurretNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [``"TiltX"; ``"TiltY"] |}.
  Definition TriggerNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [ ``"Trigger"] |}.

  (* Each RADL Node has a default implementation that nondeterministically
     selects a publication value (since the underlying RADL Nodes are
     untrusted code). *)
  Definition BarrelSpec : Core.ADT (RADL_ADTSig BarrelNode) :=
    RADL_ADTSpec BarrelNode.
  Definition TurretSpec : Core.ADT (RADL_ADTSig TurretNode) :=
    RADL_ADTSpec TurretNode.
  Definition TriggerSpec : Core.ADT (RADL_ADTSig TriggerNode) :=
    RADL_ADTSpec TriggerNode.

  Definition PaintballTopicIDs :=
    RADL_Publications TurretNode ++ RADL_Publications TriggerNode ++ RADL_Publications BarrelNode.

  (* Guard functions which check if the turret is pointed in a safe direction. *)
  Variables TiltXSafe TiltYSafe : Memory.W -> bool.

  (* The complete specification is an ADT that has a single constructor that initializes the
     RADL Nodes and a single step function that checks a global condition on each topic,
     calling the original step functions if it holds and does some error handling otherwise. *)
  Definition PaintballSpec :=
    ADTRep (Rep BarrelSpec * Rep TurretSpec * Rep TriggerSpec)
                   { Def Constructor RADL_Init (_ : unit) : rep :=
                       barrel <- callCons BarrelSpec RADL_Init tt;
                       turret <- callCons TurretSpec RADL_Init tt;
                       trigger <- callCons TriggerSpec RADL_Init tt;
                       ret (barrel, turret, trigger),

                     Def Method RADL_Step (r : rep, in_t : Message PaintballTopicIDs) :
                         (* Right now, we have a single, global guard that determines whether
                            to call the original step functions. *)
                       Message PaintballTopicIDs :=
                         if (TiltXSafe (GetTopic in_t "TiltX")
                                       && TiltYSafe (GetTopic in_t "TiltY")) then
                           (* Call the original step functions. *)
                           barrel <- callMeth BarrelSpec RADL_Step (fst (fst r)) (SubMessage [````"Trigger" ] in_t);
                           turret <- callMeth TurretSpec RADL_Step (snd (fst r)) (SubMessage [] in_t);
                           trigger <- callMeth TriggerSpec RADL_Step (snd r) (SubMessage [] in_t);
                           ret ((fst barrel, fst turret, fst trigger),
                                (ilist_app (snd turret) (ilist_app (snd trigger) (snd barrel))))
                         else
                           (* The failure case calls the trigger and turret step functions
                              and publishes "IDLE" for the barrel node. *)
                           trigger <- callMeth TriggerSpec RADL_Step (fst (fst r)) (SubMessage [] in_t);
                       turret <- callMeth TurretSpec RADL_Step (snd (fst r)) (SubMessage [] in_t);
                       ret ((tt, fst turret, fst trigger),
                            (ilist_app (snd turret) (ilist_app (snd trigger)
                                                               ((icons (B := @TopicTypes PaintballTopics)(``"Fired") ``("IDLE") (inil _))))))}.

  (* We now define the publication and subscription information for
     and the specs of the monitor nodes. *)
  Definition BarrelMonitorNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ``"Trigger"; ``"TiltX"; ``"TiltY"];
       RADL_Publications  := [ ``"Fired"] |}.

  Definition TurretMonitorNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [ ``"TiltX"; ``"TiltY"] |}.

  Definition TriggerMonitorNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [ ``"Trigger"] |}.

  (* The specs distribute the global monitor to each monitor node.
     In the case of the barrel, the monitor checks the turret position
     before calling the original step function. *)
  Definition BarrelMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig BarrelMonitorNode unit) :=
    ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : unit * Message (RADL_Subscriptions BarrelMonitorNode)) : _ :=
               if (TiltXSafe (GetTopic (snd in_t) "TiltX")
                             && TiltYSafe (GetTopic (snd in_t) "TiltY")) then
                 barrel <- callMeth BarrelSpec RADL_Step (fst in_t)
                         (SubMessage [````"Trigger" ] (snd in_t))
                 ;
                 ret (tt, barrel)
               else
                 ret (tt, (tt, (icons (B := @TopicTypes PaintballTopics)(``"Fired") ``("IDLE") (inil _))))
           }.

  (* The other two monitor nodes don't have to check anything to enforce the guard. *)
  Definition TurretMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig TurretNode unit) :=
    ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : unit * Message (RADL_Subscriptions TurretMonitorNode)) : _ :=
               turret <- callMeth TurretSpec RADL_Step (fst in_t) (snd in_t);
             ret (tt, turret)
           }.

  Definition TriggerMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig TriggerNode unit) :=
    ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : unit * Message (RADL_Subscriptions TriggerMonitorNode)) : _ :=
               turret <- callMeth TriggerSpec RADL_Step (fst in_t) (snd in_t);
             ret (tt, turret)
           }.

  (* After Refinement, we arrive at an implementation which simply calls the monitor functions,
     with each function enforcing the global guard locally. *)
  Definition PaintballImpl :
  ADTRep (Rep BarrelMonitorSpec * Rep TriggerMonitorSpec *
              Rep TurretMonitorSpec * Rep BarrelSpec *
              Rep TriggerSpec * Rep TurretSpec)
      { Def Constructor RADL_Init (_: ()) : rep :=
          barrel <- (callCons BarrelSpec RADL_Init) ();
          turret <- (callCons TurretSpec RADL_Init) ();
          trigger <- (callCons TriggerSpec RADL_Init) ();
          barrelmonitor <- (callCons BarrelMonitorSpec RADL_Init) ();
          turretmonitor <- (callCons TurretMonitorSpec RADL_Init) ();
          triggermonitor <- (callCons TriggerMonitorSpec RADL_Init) ();
          ret
            (barrelmonitor, turretmonitor, triggermonitor, barrel, turret,
            trigger) ,
        Def Method RADL_Step (r : rep, in_t : (Message PaintballTopicIDs)) :
        (Message PaintballTopicIDs) :=
          barrel <- (callMeth BarrelMonitorSpec RADL_Step)
                      (snd r)
                      ((),
                      SubMessage
                        [``(``("Trigger")); ``(``("TiltX")); ``(``("TiltY"))]
                        in_t);
          turret <- (callMeth TurretMonitorSpec RADL_Step)
                      (snd r) ((), SubMessage [] in_t);
          trigger <- (callMeth TriggerMonitorSpec RADL_Step)
                       (snd r) ((), SubMessage [] in_t);
          ret
            (fst barrel, fst turret, fst trigger, fst (snd barrel),
            fst (snd turret), fst (snd trigger),
            ilist_app (snd (snd turret))
              (ilist_app (snd (snd trigger)) (snd (snd barrel))))  })

  (* This implementation includes a list of monitor node specs from which we
     can derive Gallina implementations. Eventually (hopefully soon) we can
     then plug these into our pipeline to produce Bedrock implementations which
     can be integrated into the monitor framework. *)

  Definition PaintballImpl :
    MostlySharpened PaintballSpec.
  Proof.
    start sharpening ADT.
    hone representation using (fun (r_o : Rep PaintballSpec)
                                   (r_n :
                                      Rep BarrelMonitorSpec *
                                      Rep TriggerMonitorSpec *
                                      Rep TurretMonitorSpec *
                                      Rep BarrelSpec *
                                      Rep TriggerSpec *
                                      Rep TurretSpec)
                                        => True).
    { subst H.
      instantiate (1 := fun d => barrel <- (callCons BarrelSpec RADL_Init) ();
                   turret <- (callCons TurretSpec RADL_Init) ();
                   trigger <- (callCons TriggerSpec RADL_Init) ();
                   barrelmonitor <- (callCons BarrelMonitorSpec RADL_Init) ();
                   turretmonitor <- (callCons TurretMonitorSpec RADL_Init) ();
                   triggermonitor <- (callCons TriggerMonitorSpec RADL_Init) ();
                   ret (barrelmonitor, turretmonitor, triggermonitor, barrel, turret, trigger)).
      simplify with monad laws; refine pick val ( (), (), (), (), (), ()); eauto; simpl.
      intros v Comp_v; computes_to_inv; subst; eauto.
    }
    {
      subst H0; instantiate (1 := fun (r : Rep BarrelMonitorSpec *
                                      Rep TriggerMonitorSpec *
                                      Rep TurretMonitorSpec *
                                      Rep BarrelSpec *
                                      Rep TriggerSpec *
                                      Rep TurretSpec)  (in_t : Message PaintballTopicIDs) =>
              barrel <- callMeth BarrelMonitorSpec RADL_Step (snd r) (tt, (SubMessage [````"Trigger";
                                                                                         ````"TiltX";
                                                                                         ````"TiltY"] in_t));
        turret <- callMeth TurretMonitorSpec RADL_Step (snd r) (tt, SubMessage [] in_t);
        trigger <- callMeth TriggerMonitorSpec RADL_Step (snd r) (tt, SubMessage [] in_t);
        ret ((fst barrel, fst turret, fst trigger, fst (snd barrel), fst (snd turret), fst (snd trigger)),
             (ilist_app (snd (snd turret)) (ilist_app (snd (snd trigger)) (snd (snd barrel)))))).
      simpl.
      unfold eq_rect_r, eq_rect, eq_sym.
      simpl.
      admit.
    }

    simpl in H0.
      simpl in c.
      unfold methodType in H0.
      simpl in H0.
      unfold PaintballTopicIDs in H0.
      simpl in H0.
      eauto.
    simpl; rewrite <- refineEquiv_bind_unit.
    rewrite <- refineEquiv_bind_unit.
    simplify with monad laws.
    simpl in *.
    unfold PaintballSpec.


  econstructor.
    repeat econstructor.


    econstructor.
    simpl in *.
    simpl.



End Paintball.
