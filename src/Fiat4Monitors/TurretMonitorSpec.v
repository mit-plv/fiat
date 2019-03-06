Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Coq.Arith.Arith.
Require Import
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags
        Fiat.Fiat4Monitors.RADL_Nodes
        Fiat.Fiat4Monitors.RADLNodeADTs
        Fiat.Fiat4Monitors.LandsharkTopics
        Fiat.Fiat4Monitors.LandsharkNodes.

Require Import Bedrock.Platform.Facade.DFacade
        Bedrock.Platform.Facade.Notations
        Bedrock.Platform.Cito.ADT
        Bedrock.Platform.Cito.RepInv
        Bedrock.Platform.AutoSep.

Section Example.

  Require Bedrock.Platform.Facade.DFacade.

  Definition PaintballControlMode : Set :=
    @BoundedString ["IDLE"; "SINGLE_SHOT"; "TRIPLE_SHOT"; "BURST"].

  (* This is the list of topics available in the system.*)
  Definition PaintballTopics :=
    [ {| Topic_Name := "TiltX"; Topic_Type := Memory.W |};
      {| Topic_Name := "TiltY"; Topic_Type := Memory.W |};
      {| Topic_Name := "Trigger"; Topic_Type := PaintballControlMode |};
      {| Topic_Name := "Fired"; Topic_Type := PaintballControlMode |}].

  (* Each RADL Node has a list of subscriptions and publications drawn
     from the list of available topics. *)
  Definition PaintballNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ``"Trigger"];
       RADL_Publications  := [ ``"Fired"] |}.
  Definition TurretNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := ["TiltX"; "TiltY"] |}.
  Definition JoystickNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [ "Trigger"] |}.

  (* Each RADL Node has a default implementation that nondeterministically
     selects a publication value (since the underlying RADL Nodes are
     untrusted code). *)
  Definition PaintballSpec : Core.ADT (RADL_ADTSig PaintballNode) :=
    RADL_ADTSpec PaintballNode.
  Definition TurretSpec : Core.ADT (RADL_ADTSig TurretNode) :=
    RADL_ADTSpec TurretNode.
  Definition JoystickSpec : Core.ADT (RADL_ADTSig JoystickNode) :=
    RADL_ADTSpec JoystickNode.

  Definition PaintballTopicIDs :=
    RADL_Publications TurretNode ++ RADL_Publications JoystickNode ++ RADL_Publications PaintballNode.

  (* Guard functions which check if the turret is pointed in a safe direction. *)
  Variables TiltXSafe TiltYSafe : Memory.W -> bool.

  (* The complete specification is an ADT that has a single constructor that initializes the
     RADL Nodes and a single step function that checks a global condition on each topic,
     calling the original step functions if it holds and does some error handling otherwise. *)

  Open Scope ADTParsing_scope.
  Definition EveryMessage := Message PaintballTopicIDs.

  Definition ExampleSpec :=
    ADTRep (Rep PaintballSpec * Rep TurretSpec * Rep JoystickSpec)
     { Def Constructor RADL_Init (_ : unit) : rep :=
         barrel <- callCons PaintballSpec RADL_Init tt;
         turret <- callCons TurretSpec RADL_Init tt;
         trigger <- callCons JoystickSpec RADL_Init tt;
         ret (barrel, turret, trigger),
       Def Method RADL_Step (r' : rep, msg : EveryMessage) : EveryMessage  :=
           if (TiltXSafe (snd (msg ~~> "TiltX"))
                         && TiltYSafe (snd (msg ~~> "TiltY"))) then
             (* Call the original step functions. *)
             barrel <- callMeth PaintballSpec RADL_Step (fst (fst r')) (SubMessage ["Trigger" ] msg);
             turret <- callMeth TurretSpec RADL_Step (snd (fst r')) (SubMessage [] msg);
             trigger <- callMeth JoystickSpec RADL_Step (snd r') (SubMessage [] msg);
             ret ((fst barrel, fst turret, fst trigger),
                  (ilist_app (snd turret) (ilist_app (snd trigger) (snd barrel))))
           else
             (* The failure case calls the trigger and turret step functions
                              and publishes "IDLE" for the barrel node. *)
             trigger <- callMeth JoystickSpec RADL_Step (fst (fst r')) (SubMessage [] msg);
         turret <- callMeth TurretSpec RADL_Step (snd (fst r')) (SubMessage [] msg);
         ret ((tt, fst turret, fst trigger),
              (ilist_app (snd turret) (ilist_app (snd trigger)
                                                 ((icons (B := @TopicTypes PaintballTopics)(``"Fired") ``("IDLE") (inil _))))))}.

  (* We now define the publication and subscription information for
     and the specs of the monitor nodes. *)
  Definition PaintballMonitorNode : RADLM_Node PaintballTopics :=
    {| RADLM_Rep := unit;
       RADLM_MonitoredNode := PaintballNode;
       RADLM_Subscriptions := [ ``"TiltX"; ``"TiltY" ];
       RADLM_Publications  := [ ] |}.

  Definition TurretMonitorNode : RADLM_Node PaintballTopics :=
    {| RADLM_Rep := unit;
       RADLM_MonitoredNode := TurretNode;
       RADLM_Subscriptions := [ ];
       RADLM_Publications  := [ ] |}.

  Definition JoystickMonitorNode : RADLM_Node PaintballTopics :=
    {| RADLM_Rep := unit;
       RADLM_MonitoredNode := JoystickNode;
       RADLM_Subscriptions := [ ];
       RADLM_Publications  := [ ] |}.

  (* The specs distribute the global monitor to each monitor node.
     In the case of the barrel, the monitor checks the turret position
     before calling the original step function. Synthesizing the following
     specs during a derivation is our eventual goal. *)

  Definition PaintballMonitor_Output :=
    (unit * cRep (radlm_out_t PaintballMonitorNode) * cRep (radlm_monitor_out_t PaintballMonitorNode))%type.

  Definition PaintballMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig PaintballMonitorNode unit) :=
    ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, msg : unit * cRep (radlm_in_t PaintballMonitorNode) * cRep (radlm_monitor_in_t PaintballMonitorNode)) : PaintballMonitor_Output :=
               if (TiltXSafe (snd (snd msg ~~> "TiltX"))
                             && TiltYSafe (snd (snd msg ~~> "TiltY"))) then
                 barrel <- callMeth PaintballSpec RADL_Step (fst (fst msg))
                        (SubMessage ["Trigger" ] (snd (fst (msg))));
                 ret (tt, (barrel, inil _))
               else
                 ret (tt, (fst (fst msg), ConstructMessage (radlm_out_t PaintballMonitorNode)
                                                (``"IDLE", ()), inil _))
           }.

  (* The other two monitor nodes don't have to check anything to enforce the guard. *)
  Definition TurretMonitor_Output :=
    (unit * cRep (radlm_out_t TurretMonitorNode) * cRep (radlm_monitor_out_t TurretMonitorNode))%type.

  Definition TurretMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig TurretMonitorNode unit) :=
    ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, msg : unit * cRep (radlm_in_t TurretMonitorNode) * cRep (radlm_monitor_in_t TurretMonitorNode)) : TurretMonitor_Output :=
               turret <- callMeth TurretSpec RADL_Step (fst (fst msg)) (snd (fst msg));
             ret (tt, (turret, inil _ ))
           }.

  Definition JoystickMonitor_Output :=
    (unit * cRep (radlm_out_t JoystickMonitorNode) * cRep (radlm_monitor_out_t JoystickMonitorNode))%type.
  Definition JoystickMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig JoystickMonitorNode unit) :=
        ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, msg : unit * cRep (radlm_in_t JoystickMonitorNode) * cRep (radlm_monitor_in_t JoystickMonitorNode)) : JoystickMonitor_Output :=
               joystick <- callMeth JoystickSpec RADL_Step (fst (fst msg)) (snd (fst msg));
             ret (tt, (joystick, inil _ ))
           }.

  (* After Refinement, we arrive at an implementation which simply calls the monitor functions,
     with each function enforcing the global guard locally. *)

  (* This implementation includes a list of monitor node specs from which we
     can derive Gallina implementations. Eventually (hopefully soon) we can
     then plug these into our pipeline to produce Bedrock implementations which
     can be integrated into the monitor framework. *)

  Definition ExampleImpl :
    MostlySharpened ExampleSpec.
  Proof.
    start sharpening ADT.
    hone representation using (fun (r_o : Rep ExampleSpec)
                                   (r_n :
                                      Rep PaintballMonitorSpec *
                                      Rep JoystickMonitorSpec *
                                      Rep TurretMonitorSpec *
                                      Rep PaintballSpec *
                                      Rep JoystickSpec *
                                      Rep TurretSpec)
                                        => True).
    { subst H.
      instantiate (1 := fun d => barrel <- (callCons PaintballSpec RADL_Init) ();
                   turret <- (callCons TurretSpec RADL_Init) ();
                   trigger <- (callCons JoystickSpec RADL_Init) ();
                   barrelmonitor <- (callCons PaintballMonitorSpec RADL_Init) ();
                   turretmonitor <- (callCons TurretMonitorSpec RADL_Init) ();
                   triggermonitor <- (callCons JoystickMonitorSpec RADL_Init) ();
                   ret (barrelmonitor, turretmonitor, triggermonitor, barrel, turret, trigger)).
      simplify with monad laws; refine pick val ( (), (), (), (), (), ()); eauto; simpl.
      intros v Comp_v; computes_to_inv; subst; eauto.
    }
    { subst H0.
      instantiate (1 :=  fun (r : Rep PaintballMonitorSpec *
                                 Rep JoystickMonitorSpec *
                                 Rep TurretMonitorSpec *
                                 Rep PaintballSpec *
                                 Rep JoystickSpec *
                                 Rep TurretSpec)
                            (msg : Message PaintballTopicIDs) =>
       barrel <- callMeth PaintballMonitorSpec RADL_Step (snd r) (tt, SubMessage ["Trigger"] msg,
                                                                  SubMessage ["TiltX";
                                                                               "TiltY"] msg);
        turret <- callMeth TurretMonitorSpec RADL_Step (snd r) (tt, SubMessage [] msg, SubMessage [] msg);
        trigger <- callMeth JoystickMonitorSpec RADL_Step (snd r) (tt, SubMessage [] msg, SubMessage [] msg);
        ret ((fst barrel, fst turret, fst trigger, fst (fst (snd barrel)), fst (fst (snd turret)), fst (fst (snd trigger))),
             (ilist_app (snd (fst (snd turret))) (ilist_app (snd (fst (snd trigger))) (snd (fst (snd barrel))))))).
      admit.
    }
    (* This is essentially what the final goal should look like.*)
  Admitted.

End Example.
