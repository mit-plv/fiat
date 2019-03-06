Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Arith.Arith
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags.

Section RADL_ADT.

  Open Scope ADT_scope.
  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope ADTSig_scope.

  Definition RADL_Init := "Init".
  Definition RADL_Step := "Step".

  Context {n : nat}.
  Variable TopicTypes : Vector.t Type n. (* List of Topics in the Network. *)
  Variable TopicNames : Vector.t string n. (* List of Topics IDs in the Network. *)

  Record RADL_Node :=
    { (* Subscription + Publication info for this node *)
      RADL_NumSubscriptions : nat;
      RADL_Subscriptions : Vector.t (Fin.t n) RADL_NumSubscriptions;
      RADL_NumPublications : nat;
      RADL_Publications : Vector.t (Fin.t n) RADL_NumPublications;
      RADL_Defs : list string;
      RADL_Period : string;
      RADL_Path : string;
      RADL_CXX : list string
    }.

  Definition radl_in_t (Node : RADL_Node) :=
    MessageADT TopicTypes TopicNames (RADL_Subscriptions Node).
  Definition radl_in_flags_t (Node : RADL_Node) :=
    FlagsADT TopicNames (RADL_Subscriptions Node).
  Definition radl_out_t (Node : RADL_Node) :=
    MessageADT TopicTypes TopicNames (RADL_Publications Node).
  Definition radl_out_flags_t (Node : RADL_Node) :=
    FlagsADT TopicNames (RADL_Publications Node).

  Definition RADL_ADTSig  (Node : RADL_Node)
  : DecoratedADTSig :=                         (* A RADL Node is modeled as an ADT with a  *)
    ADTsignature {                    (* single constructor and a step function. *)
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x (prod (cRep (radl_in_t Node)) (cRep (radl_in_flags_t Node)))
                                     -> rep x (prod (cRep (radl_out_t Node)) (cRep (radl_out_flags_t Node)))
      }.

  (*Definition RADL_ADTSpec (Node : RADL_Node)
  : ADT (RADL_ADTSig Node) :=
    ADTRep unit (* Since RADL Nodes are untrusted, we'll treat their state as completely unknown *)
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : _) : _ :=
               (* Again, since the RADL Node is untrusted code, we'll assume that it can publish
                  whatever the heck it wants. *)
               results <- {out_t : cRep (radl_out_t Node) | True };
               result_flags <- {out_t : cRep (radl_out_flags_t Node) | True };
             ret (tt, (results, result_flags)) }. *)

  Record RADLM_Node :=
    { (* The monitored node*)
      RADLM_MonitoredNode : RADL_Node;
      (* Additional Subscription + Publication info *)
      RADLM_NumSubscriptions : nat;
      RADLM_Subscriptions : Vector.t (Fin.t n) RADLM_NumSubscriptions;
      RADLM_NumPublications : nat;
      RADLM_Publications : Vector.t (Fin.t n) RADLM_NumPublications
    }.

  Definition radlm_in_t (Node : RADLM_Node) :=
    MessageADT TopicTypes TopicNames (RADL_Subscriptions (RADLM_MonitoredNode Node)).
  Definition radlm_in_flags_t (Node : RADLM_Node) :=
    FlagsADT TopicNames (RADL_Subscriptions (RADLM_MonitoredNode Node)).

  Definition radlm_out_t (Node : RADLM_Node) :=
    MessageADT TopicTypes TopicNames (RADL_Publications (RADLM_MonitoredNode Node)).
  Definition radlm_out_flags_t (Node : RADLM_Node) :=
    FlagsADT TopicNames (RADL_Publications (RADLM_MonitoredNode Node)).

  Definition radlm_monitor_in_t (Node : RADLM_Node) :=
    MessageADT TopicTypes TopicNames (RADLM_Subscriptions Node).
  Definition radlm_monitor_out_t (Node : RADLM_Node) :=
    MessageADT TopicTypes TopicNames (RADLM_Publications Node).

  Definition RADL_Start_Step := "Start_Step".
  Definition RADL_Finish_Step := "Finish_Step".

  Record RADLM_start_msg_t (MonitorNode : RADLM_Node) :=
    { radlm_in : cRep (radlm_in_t MonitorNode);
      radlm_in_flags : cRep (radlm_in_flags_t MonitorNode);
      radlm_monitor_in : cRep (radlm_monitor_in_t MonitorNode) }.

  Record RADLM_finish_msg_t (MonitorNode : RADLM_Node) :=
    { radlm_out : cRep (radlm_out_t MonitorNode);
      radlm_out_flags : cRep (radlm_out_flags_t MonitorNode) }.

  Definition RADLM_ADTSig
             (MonitorNode : RADLM_Node)
             (InitDom : Type)
  : DecoratedADTSig :=
    ADTsignature {
        Constructor RADL_Init       : InitDom -> rep,
        (* Monitor Nodes have two methods which are used to guard the node's step function:
           1) an initial step function that examines the subscriptions and decides whether
           to pass them on (potentially modifying them) or to publish on its own. *)
        Method      RADL_Start_Step : rep x RADLM_start_msg_t MonitorNode
                                      -> rep x (cRep (radlm_in_t MonitorNode)
                                                * cRep (radlm_in_flags_t MonitorNode)),
        (* 2) A finish step function that examines the publications after a node's
         step function has been called, potentially modifying the publications and publishing
         its own topics. *)
        Method      RADL_Finish_Step : rep x RADLM_finish_msg_t MonitorNode
                                       -> rep x (cRep (radlm_out_t MonitorNode)
                                                 * cRep (radlm_out_flags_t MonitorNode)
                                                 * cRep (radlm_monitor_out_t MonitorNode))
      }.

End RADL_ADT.

Definition RADL_ADT {n} Topics Node :=
  DecoratedADT (@RADL_ADTSig n (Vector.map Topic_Type Topics)
                    (Vector.map Topic_Name Topics)
                    Node).

Definition RADLM_ADT {n} Topics MonitorNode InitDom :=
  DecoratedADT (@RADLM_ADTSig n (Vector.map Topic_Type Topics)
                     (Vector.map Topic_Name Topics)
                     MonitorNode InitDom).
