Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADTNotation
        Fiat.ADTRefinement.

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

  Definition TopicTypes (topic : TopicID) : Type :=
    Topic_Type (nth_Bounded Topic_Name Topics topic).

  Definition Message topics := ilist TopicTypes topics.

  Fixpoint SubMessage
           (subtopics : list TopicID)
           topics
           (msg : Message topics)
  : ilist TopicTypes subtopics :=
    match subtopics return ilist TopicTypes subtopics with
      | topic :: subtopics' =>
        icons (B := TopicTypes) _ (ith_Bounded  msg topic) (SubMessage subtopics' msg)
      | nil => inil _
    end.

  Definition RADL_ADTSig  (Node : RADL_Node)
  : ADTSig :=                         (* A RADL Node is modeled as an ADT with a  *)
    ADTsignature {                    (* single constructor and a step function. *)
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x ilist TopicTypes (RADL_Subscriptions Node)
                                     -> rep x ilist TopicTypes (RADL_Publications Node)
      }.

  Definition RADL_ADTSpec (Node : RADL_Node)
  : ADT (RADL_ADTSig Node) :=
    ADTRep unit (* Since RADL Nodes are untrusted, we'll treat their state as completely unknown *)
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : ilist TopicTypes (RADL_Subscriptions Node)) : _ :=
               (* Again, since the RADL Node is untrusted code, we'll assume that it can publish
                  whatever the heck it wants. *)
               results <- {out_t : ilist TopicTypes (RADL_Publications Node) | True };
             ret (tt, results) }.

  Definition RADLM_ADTSig
             (Node MonitorNode : RADL_Node)
             (InitDom : Type)
  : ADTSig :=
    ADTsignature {
        Constructor RADL_Init      : InitDom -> rep,
        Method      RADL_Step      : rep x unit * ilist TopicTypes (RADL_Subscriptions MonitorNode)
                                     -> rep x unit * ilist TopicTypes (RADL_Publications MonitorNode)
      }.

End RADL_Definitions.

Section Paintball.

  Require Bedrock.Platform.Facade.DFacade.

  Definition PaintballControlMode :=
    @BoundedString ["IDLE"; "SINGLE_SHOT"; "TRIPLE_SHOT"; "BURST"].

  Definition PaintballTopics :=
    [ {| Topic_Name := "TiltX"; Topic_Type := Memory.W |};
      {| Topic_Name := "TiltY"; Topic_Type := Memory.W |};
      {| Topic_Name := "Trigger"; Topic_Type := PaintballControlMode |};
      {| Topic_Name := "Fired"; Topic_Type := PaintballControlMode |}].

  Definition BarrelNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ``"Trigger"];
       RADL_Publications  := [ ``"Fired"] |}.

  Definition BarrelSpec : Core.ADT (RADL_ADTSig BarrelNode) :=
    RADL_ADTSpec BarrelNode.

  Definition TurretNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [``"TiltX"; ``"TiltY"] |}.

  Definition TurretSpec : Core.ADT (RADL_ADTSig TurretNode) :=
    RADL_ADTSpec TurretNode.

  Definition TriggerNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [ ``"Trigger"] |}.

  Definition TriggerSpec : Core.ADT (RADL_ADTSig TriggerNode) :=
    RADL_ADTSpec TriggerNode.

  Definition PaintballSig :=
    ADTsignature {
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x ilist Topic_Type PaintballTopics
                                     -> rep x ilist (@TopicTypes PaintballTopics) [``"TiltX"; ``"TiltY"; ``"Trigger"; ``"Fired" ]
      }.

  Variables TiltXSafe TiltYSafe : Memory.W -> bool.

  Notation GetTopic il idx := (ith_Bounded Topic_Name il ``idx).

  Definition PaintballSpec : ADT PaintballSig :=
    Eval simpl in ADTRep (unit * unit)
                   { Def Constructor RADL_Init (_ : unit) : rep :=
                       barrel <- callCons BarrelSpec RADL_Init tt;
                       turret <- callCons TurretSpec RADL_Init tt;
                       trigger <- callCons TriggerSpec RADL_Init tt;
                       ret (turret, trigger),
                       Def Method RADL_Step (r : rep, in_t : ilist Topic_Type PaintballTopics) : _ :=
                         if (TiltXSafe (GetTopic in_t "TiltX")
                                       && TiltYSafe (GetTopic in_t "TiltY")) then
                           barrel <- callMeth BarrelSpec RADL_Step (snd r) (SubMessage (RADL_Subscriptions BarrelNode) in_t);
                           turret <- callMeth TurretSpec RADL_Step (fst r) (SubMessage (RADL_Subscriptions TurretNode) in_t);
                           trigger <- callMeth TriggerSpec RADL_Step (snd r) (SubMessage (RADL_Subscriptions TriggerNode) in_t);
                           ret ((fst turret, fst trigger) ,
                                (ilist_app (snd turret) (ilist_app (snd trigger) (snd barrel))))
                         else
                           barrel <- callMeth BarrelSpec RADL_Step (snd r) (SubMessage (RADL_Subscriptions BarrelNode) in_t);
                       turret <- callMeth TurretSpec RADL_Step (fst r) (SubMessage (RADL_Subscriptions TurretNode) in_t);
                       ret ((tt, tt), (ilist_app (snd turret) (ilist_app
                                                                 ((icons (B := @TopicTypes PaintballTopics)(``"Trigger") ``("IDLE") (inil _)))(snd barrel) )))}.

  Definition TriggerMonitorNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ``"Trigger"; ``"TiltX"; ``"TiltY"];
       RADL_Publications  := [ ] |}.

  Definition TurretMonitorNode : RADL_Node PaintballTopics :=
    {| RADL_Subscriptions := [ ];
       RADL_Publications  := [``"TiltX"; ``"TiltY"] |}.

  Definition TriggerMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig TriggerNode TriggerMonitorNode unit).
    refine (ADTRep unit
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : _) : _ := _}).
    simpl in *.
    refine (if (TiltXSafe (ilist_hd (ilist_tl (snd in_t)))
                          && TiltYSafe (ilist_hd (ilist_tl (snd in_t)))) then
              trigger <- callMeth TriggerSpec RADL_Step (fst in_t)
                      (SubMessage (RADL_Subscriptions TriggerNode) (snd in_t))
              ;
              ret (tt, _)
            else
              ret (tt, _)).
  Defined.

  Print TriggerMonitorSpec.

  Definition TurretMonitorSpec : Fiat.ADT.Core.ADT (RADLM_ADTSig TurretNode TurretMonitorNode).
    refine (ADTRep (RADL_Rep TurretMonitorNode)
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : _) : _ :=
               turret <- callMeth TurretSpec RADL_Step (fst in_t) (snd in_t);
              ret (tt , turret)

           }).

  Definition PaintballImpl :
    MostlySharpened PaintballSpec.
  Proof.
    start sharpening ADT.
    hone representation using (fun (r_o : RADL_Rep TurretNode *
                                           RADL_Rep TriggerNode)
                                      (r_n :
                                          (RADL_Rep TriggerMonitorNode *
                                           RADL_Rep TurretMonitorNode *
                                           RADL_Rep TriggerNode *
                                           RADL_Rep TurretNode))

                                        => True).
    simpl in *.
    unfold PaintballSpec.


  econstructor.
    repeat econstructor.


    econstructor.
    simpl in *.
    simpl.



End Paintball.
