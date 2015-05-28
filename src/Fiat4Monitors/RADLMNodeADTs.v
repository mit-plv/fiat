Set Implicit Arguments.

Require Import Coq.Lists.List
        Coq.Program.Program
        Coq.Arith.Arith
        Coq.Strings.String.
Require Import
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.Heading2
        Fiat.QueryStructure.Specification.Representation.Tuple2
        Fiat.QueryStructure.Specification.Representation.TupleADT2
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

Section RADLM_NodeADTs.

  Context {n : nat}.
  Variable TopicTypes : Vector.t Type n. (* List of Topics in the Network. *)
  Variable TopicNames : Vector.t string n. (* List of Topics IDs in the Network. *)
  Variable MNode : RADLM_Node (n := n). (* The monitor node we're modelling. *)

  Let Node := RADLM_MonitoredNode MNode. (* The node being monitored. *)

  Inductive RADLM_Node_ADTValues : Type :=
  | Message_In : cRep (radlm_in_t TopicTypes TopicNames MNode) -> RADLM_Node_ADTValues
  | Message_Out : cRep (radlm_out_t TopicTypes TopicNames MNode) -> RADLM_Node_ADTValues
  | Message_In_Flags :  cRep (radlm_in_flags_t TopicNames MNode) -> RADLM_Node_ADTValues
  | Message_Out_Flags : cRep (radlm_out_flags_t TopicNames MNode) -> RADLM_Node_ADTValues
  | Monitor_Message_In : cRep (radlm_monitor_in_t TopicTypes TopicNames MNode) -> RADLM_Node_ADTValues
  | Monitor_Message_Out : cRep (radlm_monitor_out_t TopicTypes TopicNames MNode) -> RADLM_Node_ADTValues
  | Flag : RADL_Flag -> RADLM_Node_ADTValues
  | Struct : forall {n} {attrs}, @DecTuple2 n attrs -> RADLM_Node_ADTValues
  | RADLM_Node : RADLM_Rep MNode -> RADLM_Node_ADTValues
  | RADL_Node : unit -> RADLM_Node_ADTValues.

  (* Specs for getters and setters for each message type . *)
  Section Message_In_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Subscriptions Node.
    Variable idx : Fin.t (RADL_NumSubscriptions Node).
    Variable Get_In_DomMap
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
    Variable Get_In_CodMap
      : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
        -> Memory.W.
    Definition Message_In_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_In msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_In msg),
                                 Some (Message_In msg)) ] /\
                        ret = SCA _
                                  (Get_In_CodMap (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap
      : Memory.W ->
        fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
    Definition Message_In_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_In msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_In msg),
                                   Some (Message_In (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_In_Specs.

    (* Specs for getters and setters for each message type . *)
  Section Monitor_Message_In_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADLM_Subscriptions MNode.
    Variable idx : Fin.t (RADLM_NumSubscriptions MNode).
    Variable Get_In_DomMap
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
    Variable Get_In_CodMap
      : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
        -> Memory.W.
    Definition Monitor_Message_In_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Monitor_Message_In msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Monitor_Message_In msg),
                                 Some (Monitor_Message_In msg)) ] /\
                        ret = SCA _
                                  (Get_In_CodMap (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap
      : Memory.W ->
        fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
    Definition Monitor_Message_In_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Monitor_Message_In msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Monitor_Message_In msg),
                                   Some (Monitor_Message_In (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Monitor_Message_In_Specs.

  Section Message_In_Flags_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Subscriptions Node.
    Variable idx : Fin.t (RADL_NumSubscriptions Node).
    Variable Get_In_DomMap
      : unit -> fst (MethodDomCod (FlagsADTSig TopicNames topics)
                                  (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx)))).
    Variable Get_In_CodMap
      : snd (MethodDomCod (FlagsADTSig TopicNames topics)
                          (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx))))
        -> Memory.W.

    Definition Message_In_Flags_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_In_Flags msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_In_Flags msg),
                                 Some (Message_In_Flags msg)) ] /\
                        ret = SCA _
                                  (Get_In_CodMap (snd (CallFlagsGetMethod _ msg idx (Get_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap
      : Memory.W -> fst
                      (MethodDomCod (FlagsADTSig TopicNames topics)
                                    (ibound (indexb (BuildSetFlagsMethodID TopicNames topics idx)))).

    Definition Message_In_Flags_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_In_Flags msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_In_Flags msg),
                                   Some (Message_In_Flags (fst (CallFlagsSetMethod _ msg idx (Set_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_In_Flags_Specs.

  Section Message_Out_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Publications Node.
    Variable idx : Fin.t (RADL_NumPublications Node).
    Variable Get_In_DomMap
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
    Variable Get_In_CodMap
      : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
        -> Memory.W.

    Definition Message_Out_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_Out msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_Out msg),
                                 Some (Message_Out msg)) ] /\
                        ret = SCA _
                                  (Get_In_CodMap (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap
      : Memory.W ->
        fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
    Definition Message_Out_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_Out msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_Out msg),
                                   Some (Message_Out (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_Out_Specs.

  Section Monitor_Message_Out_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADLM_Publications MNode.
    Variable idx : Fin.t (RADLM_NumPublications MNode).
    Variable Get_In_DomMap
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
    Variable Get_In_CodMap
      : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
        -> Memory.W.

    Definition Monitor_Message_Out_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Monitor_Message_Out msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Monitor_Message_Out msg),
                                 Some (Monitor_Message_Out msg)) ] /\
                        ret = SCA _
                                  (Get_In_CodMap (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap
      : Memory.W ->
        fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                          (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
    Definition Monitor_Message_Out_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Monitor_Message_Out msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Monitor_Message_Out msg),
                                   Some (Monitor_Message_Out (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Monitor_Message_Out_Specs.

  Section Message_Out_Flags_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Publications Node.
    Variable idx : Fin.t (RADL_NumPublications Node).
    Variable Get_Out_DomMap
      : unit -> fst (MethodDomCod (FlagsADTSig TopicNames topics)
                                  (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx)))).
    Variable Get_Out_CodMap
      : snd (MethodDomCod (FlagsADTSig TopicNames topics)
                          (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx))))
        -> Memory.W.

    Definition Message_Out_Flags_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg, args = [ADT (Message_Out_Flags msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Message_Out_Flags msg),
                                 Some (Message_Out_Flags msg)) ] /\
                        ret = SCA _
                                  (Get_Out_CodMap
                                                  (snd (CallFlagsGetMethod _ msg idx (Get_Out_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_Out_CodMap
      : Memory.W -> fst
                      (MethodDomCod (FlagsADTSig TopicNames topics)
                                    (ibound (indexb (BuildSetFlagsMethodID TopicNames topics idx)))).

    Definition Message_Out_Flags_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg w, args = [ADT (Message_Out_Flags msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Message_Out_Flags msg),
                                   Some (Message_Out_Flags (fst (CallFlagsSetMethod _ msg idx (Set_Out_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Message_Out_Flags_Specs.
  
  Section Struct_Specs.
    (* Coercions for getter domain and codomain values. *)
    Context {n' : nat}.
    Context {attrs : Vector.t Attribute2 n'}.
    
    Variable idx : Fin.t n'.
    Let heading := BuildHeading2 attrs.
    Let sig := Tuple2ADTSig heading.
    
    Variable Get_DomMap : unit -> fst (MethodDomCod sig
                                                    (ibound (indexb (BuildGetTuple2MethodID heading idx)))).
    Variable Get_CodMap
      : snd (MethodDomCod sig (ibound (indexb (BuildGetTuple2MethodID heading idx))))
        -> Memory.W.

    Definition Struct_GetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists msg : DecTuple2 attrs, args = [ADT (Struct msg)];
          PostCond args ret :=
            exists msg, args = [(ADT (Struct msg),
                                 Some (Struct msg)) ] /\
                        ret = SCA _
                                  (Get_CodMap
                                                  (snd (CallTuple2GetMethod _ msg idx (Get_DomMap tt))))
        |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_CodMap
      : Memory.W -> fst (MethodDomCod sig (ibound (indexb (BuildSetTuple2MethodID heading idx)))).

    Definition Struct_SetSpec
    : AxiomaticSpec RADLM_Node_ADTValues.
      refine {|
          PreCond args := exists (msg : DecTuple2 attrs) w, args = [ADT (Struct msg), SCA _ w];
          PostCond args ret :=
            exists msg w, args = [(ADT (Struct msg),
                                   Some (Struct (fst (CallTuple2SetMethod _ msg idx (Set_CodMap w))))),
                                  (SCA _ w, None)
                                 ]
        |}; crush_types.
    Defined.
  End Struct_Specs.

End RADLM_NodeADTs.
