Set Implicit Arguments.

Require Import Coq.Lists.List
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
        Fiat.Fiat4Monitors.RADL_Nodes.

Require Import Bedrock.Platform.Facade.DFacade
        Bedrock.Platform.Facade.Notations
        Bedrock.Platform.Cito.ADT
        Bedrock.Platform.Cito.RepInv.

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros;
  repeat match goal with
           | [ H: exists t, _ |- _ ] => destruct H
         end; subst;
  intuition.

Section MonitorADTs.
(* Each of these structs is represented in Facade as a distinct ADT. *)
  Variable Topics : list RADL_Topic. (* List of Topics in the Network. *)
  Variable MonitorNode : RADLM_Node Topics. (* The Monitor Node we're modelling. *)

  (* The Specificaiton of Monitor Node we're modelling. *)
  Variable MonitorNodeSpec :
    Fiat.ADT.Core.ADT (RADLM_ADTSig MonitorNode unit).

  Inductive MonitorADTValues : Type :=
  | Message_In : cRep (radlm_in_t MonitorNode) -> MonitorADTValues
  | Message_Out : cRep (radlm_out_t MonitorNode) -> MonitorADTValues
  | Message_Monitor_In : cRep (radlm_monitor_in_t MonitorNode) -> MonitorADTValues
  | Message_Monitor_Out : cRep (radlm_monitor_out_t MonitorNode) -> MonitorADTValues
  | RADL_Monitored_Node : unit -> MonitorADTValues
  | RADLM_Node : Rep MonitorNodeSpec -> MonitorADTValues.

  (* Specs for getters and setters for each message type . *)
  Section Message_In_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Subscriptions (RADLM_MonitoredNode MonitorNode).
    Variable idx : BoundedIndex
                     (map (fun id : BoundedIndex topics => bindex id)
                          (LiftTopics (Topics := Topics) topics)).
    Variable Get_In_DomMap
    : unit -> fst (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx)) .
    Variable Get_In_CodMap
    : snd (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx))
      -> Memory.W.
    Definition Message_In_GetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_In msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_In msg),
                                 Some (Message_In msg)) ] /\
                        ret = SCA _
                                  (Get_In_CodMap (snd (CallMessageGetMethod msg idx (Get_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap
    : Memory.W -> fst
                    (MethodDomCod
                       (MessageADTSig topics)
                       (BuildSetMessageMethodID topics idx)).

    Definition Message_In_SetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_In msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_In msg),
                                   Some (Message_In (fst (CallMessageSetMethod msg idx (Set_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_In_Specs.

  Section Message_Out_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Publications (RADLM_MonitoredNode MonitorNode).
    Variable idx : BoundedIndex
                      (map (fun id : BoundedIndex topics => bindex id)
                           (LiftTopics (Topics := Topics) topics)).
    Variable Get_Out_DomMap
    : unit -> fst (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx)) .
    Variable Get_Out_CodMap
    : snd (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx))
      -> Memory.W.

    Definition Message_Out_GetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_Out msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_Out msg),
                                 Some (Message_Out msg)) ] /\
                        ret = SCA _
                                  (Get_Out_CodMap
                                                  (snd (CallMessageGetMethod msg idx (Get_Out_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_Out_CodMap
    : Memory.W -> fst
                      (MethodDomCod
                         (MessageADTSig topics)
                         (BuildSetMessageMethodID topics idx)).

    Definition Message_Out_SetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_Out msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_Out msg),
                                   Some (Message_Out (fst (CallMessageSetMethod msg idx (Set_Out_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_Out_Specs.

  Section Message_Monitor_In_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADLM_Subscriptions MonitorNode.
    Variable idx : BoundedIndex
                      (map (fun id : BoundedIndex topics => bindex id)
                           (LiftTopics (Topics := Topics) topics)).
    Variable Get_Monitor_In_DomMap
    : unit -> fst (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx)) .
    Variable Get_Monitor_In_CodMap
    : snd (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx))
      -> Memory.W.
    Definition Message_Monitor_In_GetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_Monitor_In msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_Monitor_In msg),
                                 Some (Message_Monitor_In msg)) ] /\
                        ret = SCA _
                                  (Get_Monitor_In_CodMap
                                                 (snd (CallMessageGetMethod msg idx (Get_Monitor_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_Monitor_In_CodMap
    : Memory.W -> fst
                      (MethodDomCod
                         (MessageADTSig topics)
                         (BuildSetMessageMethodID topics idx)).

    Definition Message_Monitor_In_SetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_Monitor_In msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_Monitor_In msg),
                                   Some (Message_Monitor_In (fst (CallMessageSetMethod msg idx (Set_Monitor_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_Monitor_In_Specs.

  Section Message_Monitor_Out_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADLM_Publications MonitorNode.
    Variable idx : BoundedIndex
                      (map (fun id : BoundedIndex topics => bindex id)
                           (LiftTopics (Topics := Topics) topics)).
    Variable Get_Monitor_Out_DomMap
    : unit -> fst (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx)) .
    Variable Get_Monitor_Out_CodMap
    : snd (MethodDomCod (MessageADTSig topics) (BuildGetMessageMethodID topics idx))
      -> Memory.W.
    Definition Message_Monitor_Out_GetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_Monitor_Out msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_Monitor_Out msg),
                                 Some (Message_Monitor_Out msg)) ] /\
                        ret = SCA _
                                  (Get_Monitor_Out_CodMap
                                                 (snd (CallMessageGetMethod msg idx (Get_Monitor_Out_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_Monitor_Out_CodMap
    : Memory.W -> fst
                      (MethodDomCod
                         (MessageADTSig topics)
                         (BuildSetMessageMethodID topics idx)).

    Definition Message_Monitor_Out_SetSpec
    : AxiomaticSpec MonitorADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_Monitor_Out msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_Monitor_Out msg),
                                   Some (Message_Monitor_Out (fst (CallMessageSetMethod msg idx (Set_Monitor_Out_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_Monitor_Out_Specs.

  Definition RADL_Monitored_Node_StepSpec
  : AxiomaticSpec MonitorADTValues.
    refine {|
        PreCond args :=
          exists node in_msg out_msg,
            args = [ADT (RADL_Monitored_Node node);
                     ADT (Message_In in_msg);
                     ADT (Message_Out out_msg) ];
        PostCond args ret :=
          exists node in_msg out_msg in_msg' out_msg',
            args = [(ADT (RADL_Monitored_Node node),
                     Some (RADL_Monitored_Node node));
                     (ADT (Message_In in_msg),
                      Some (Message_In in_msg'));
                     (ADT (Message_Out out_msg),
                      Some (Message_Out out_msg'))]
      |}; crush_types.
  Defined.

  (* The Monitor Node's constructor and step method
     both satisfy the Fiat specifications. *)
  Definition MonitorNode_InitSpec :
    AxiomaticSpec MonitorADTValues.
    refine {| PreCond args :=
                args = [];
              PostCond args ret :=
                exists monitor_node,
                  args = [ ]
                  /\ ret = ADT (RADLM_Node monitor_node)
                  /\ computes_to (callCons MonitorNodeSpec RADL_Init ())
                                 monitor_node |}; crush_types.
  Defined.

  Definition MonitorNode_StepSpec :
    AxiomaticSpec MonitorADTValues.
    refine {| PreCond args :=
                exists monitor_node node
                       in_msg out_msg
                       monitor_in_msg monitor_out_msg,
                  args = [
                    ADT (RADLM_Node monitor_node);
                    ADT (RADL_Monitored_Node node);
                    ADT (Message_In in_msg);
                    ADT (Message_Out out_msg);
                    ADT (Message_Monitor_In monitor_in_msg);
                    ADT (Message_Monitor_Out monitor_out_msg)
                  ];
              PostCond args ret :=
                exists monitor_node node
                       in_msg out_msg
                       monitor_in_msg monitor_out_msg
                       monitor_node'  node' out_msg' monitor_out_msg',
                  args = [(ADT (RADLM_Node monitor_node),
                           Some (RADLM_Node monitor_node'));
                           (ADT (RADL_Monitored_Node node),
                            Some (RADL_Monitored_Node node'));
                           (ADT (Message_In in_msg),
                            Some (Message_In in_msg));
                           (ADT (Message_Out out_msg),
                            Some (Message_Out out_msg'));
                           (ADT (Message_Monitor_In monitor_in_msg),
                            Some (Message_Monitor_In monitor_in_msg));
                           (ADT (Message_Monitor_Out monitor_out_msg),
                            Some (Message_Monitor_Out monitor_out_msg'))
                         ]
                  /\ computes_to (callMeth MonitorNodeSpec RADL_Step monitor_node (node, in_msg, monitor_in_msg))
                                 (monitor_node', (node', out_msg', monitor_out_msg'))
           |}; crush_types.
  Defined.

End MonitorADTs.
