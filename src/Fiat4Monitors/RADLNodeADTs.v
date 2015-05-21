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

Section RADL_NodeADTs.
  (* Each of these structs is represented in Facade as a distinct ADT. *)

  Context {n : nat}.
  Variable TopicTypes : Vector.t Type n. (* List of Topics in the Network. *)
  Variable TopicNames : Vector.t string n. (* List of Topics IDs in the Network. *)

  Context {n' : nat}.
  Variable subtopics : Vector.t (Fin.t n) n'. (* List of Topics in the Network. *)
  Variable Node : RADL_Node (n := n). (* The Node we're modelling. *)

  (* The mathematical model of the node's internal state. *)
  Variable Node_Rep : Type.

  Inductive RADL_Node_ADTValues : Type :=
  | Message_In : cRep (radl_in_t TopicTypes TopicNames Node) -> RADL_Node_ADTValues
  | Message_Out : cRep (radl_out_t TopicTypes TopicNames Node) -> RADL_Node_ADTValues
  | Message_In_Flags :  cRep (radl_in_flags_t TopicNames Node) -> RADL_Node_ADTValues
  | Message_Out_Flags : cRep (radl_out_flags_t TopicNames Node) -> RADL_Node_ADTValues
  | Flag : RADL_Flag -> RADL_Node_ADTValues
  | RADL_Node : Node_Rep -> RADL_Node_ADTValues.

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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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
    : AxiomaticSpec RADL_Node_ADTValues.
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

End RADL_NodeADTs.
