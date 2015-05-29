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
  Variable ADTSpec : DecoratedADT (RADLM_ADTSig TopicTypes TopicNames MNode unit).

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
  | RADLM_Node : Rep ADTSpec -> RADLM_Node_ADTValues
  | RADL_Node : unit -> RADLM_Node_ADTValues.

  (* Specs for getters and setters for each message type . *)
  Section Message_In_Specs.

    Let topics := RADL_Subscriptions Node.

    Variable idx' : BoundedIndex (RADL_Subscriptions Node).
    Let idx : Fin.t (RADL_NumSubscriptions Node) := ibound (indexb idx').

    Section Message_In_W.
      (* Coercions for getter domain and codomain values. *)
      Variable Get_In_DomMap_W
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
      Variable Get_In_CodMap_W
        : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
          -> Memory.W.
      Definition Message_In_Get_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg, args = [ADT (Message_In msg)];
                PostCond args ret :=
                  exists msg, args = [(ADT (Message_In msg),
                                       Some (Message_In msg)) ] /\
                              ret = SCA _
                                        (Get_In_CodMap_W (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap_W tt))))
              |}; crush_types.
      Defined.

      (* Coercions for setter domain and codomain values. *)
      Variable Set_In_CodMap_W
        : Memory.W ->
          fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
      Definition Message_In_Set_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg w, args = [ADT (Message_In msg), SCA _ w];
                PostCond args ret :=
                  exists msg w, args = [(ADT (Message_In msg),
                                         Some (Message_In (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap_W w))))),
                                        (SCA _ w, None)
                                       ]
              |}; crush_types.
      Defined.
    End Message_In_W.

    Section Message_In_Struct.
      Context {n' : nat}.
      Context {attrs : Vector.t Attribute2 n'}.

      (* Coercions for getter domain and codomain values. *)
      Variable Get_In_DomMap_Struct
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
      Variable Get_In_CodMap_Struct
        : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
          -> @DecTuple2 n' attrs.
      Definition Message_In_Get_Struct_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg, args = [ADT (Message_In msg)];
                PostCond args ret :=
                  exists msg, args = [(ADT (Message_In msg),
                                       Some (Message_In msg)) ] /\
                              ret = ADT (Struct
                                           (Get_In_CodMap_Struct (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap_Struct tt)))))
              |}; crush_types.
      Defined.

      (* Coercions for setter domain and codomain values. *)
      Variable Set_In_CodMap_Struct
        : @DecTuple2 n' attrs ->
          fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
      Definition Message_In_Set_Struct_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg (tup : DecTuple2 attrs),
                  args = [ADT (Message_In msg), ADT (Struct tup)];
                PostCond args ret :=
                  exists msg (tup : DecTuple2 attrs),
                    args = [(ADT (Message_In msg),
                             Some (Message_In (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap_Struct tup))))),
                            (ADT (Struct tup), Some (Struct tup))
                                       ]
              |}; crush_types.
      Defined.
    End Message_In_Struct.

  End Message_In_Specs.

  (* Specs for getters and setters for each message type . *)
  Section Monitor_Message_In_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADLM_Subscriptions MNode.

    Variable idx' : BoundedIndex (RADLM_Subscriptions MNode).
    Let idx : Fin.t (RADLM_NumSubscriptions MNode) := ibound (indexb idx').

    Section Monitor_Message_In_W.
      Variable Get_In_DomMap_W
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
      Variable Get_In_CodMap_W
        : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
          -> Memory.W.
      Definition Monitor_Message_In_Get_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg, args = [ADT (Monitor_Message_In msg)];
                PostCond args ret :=
                  exists msg, args = [(ADT (Monitor_Message_In msg),
                                       Some (Monitor_Message_In msg)) ] /\
                              ret = SCA _
                                        (Get_In_CodMap_W (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap_W tt))))
              |}; crush_types.
      Defined.

      (* Coercions for setter domain and codomain values. *)
      Variable Set_In_CodMap_W
        : Memory.W ->
          fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
      Definition Monitor_Message_In_Set_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg w, args = [ADT (Monitor_Message_In msg), SCA _ w];
                PostCond args ret :=
                  exists msg w, args = [(ADT (Monitor_Message_In msg),
                                         Some (Monitor_Message_In (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap_W w))))),
                                        (SCA _ w, None)
                                       ]
              |}; crush_types.
      Defined.
    End Monitor_Message_In_W.

    Section Monitor_Message_In_Struct.
      Context {n' : nat}.
      Context {attrs : Vector.t Attribute2 n'}.

      Variable Get_In_DomMap_Struct
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
      Variable Get_In_CodMap_Struct
        : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
          -> DecTuple2 attrs.
      Definition Monitor_Message_In_Get_Struct_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg, args = [ADT (Monitor_Message_In msg)];
                PostCond args ret :=
                  exists msg, args = [(ADT (Monitor_Message_In msg),
                                       Some (Monitor_Message_In msg)) ] /\
                              ret = ADT (Struct
                                           (Get_In_CodMap_Struct (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap_Struct tt)))))
              |}; crush_types.
      Defined.

      (* Coercions for setter domain and codomain values. *)
      Variable Set_In_CodMap_Struct
        : DecTuple2 attrs ->
          fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
      Definition Monitor_Message_In_Set_Struct_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg (tup : DecTuple2 attrs),
                  args = [ADT (Monitor_Message_In msg), ADT (Struct tup)];
                PostCond args ret :=
                  exists msg (tup : DecTuple2 attrs),
                    args = [(ADT (Monitor_Message_In msg),
                             Some (Monitor_Message_In (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap_Struct tup))))),
                            (ADT (Struct tup), Some (Struct tup))
                                       ]
              |}; crush_types.
      Defined.
    End Monitor_Message_In_Struct.

  End Monitor_Message_In_Specs.

  Section Message_In_Flags_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Subscriptions Node.

    Variable idx' : BoundedIndex (RADL_Subscriptions Node).
    Let idx : Fin.t (RADL_NumSubscriptions Node) := ibound (indexb idx').

    Variable Get_In_DomMap_W
      : unit -> fst (MethodDomCod (FlagsADTSig TopicNames topics)
                                  (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx)))).
    Variable Get_In_CodMap_W
      : snd (MethodDomCod (FlagsADTSig TopicNames topics)
                          (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx))))
        -> Memory.W.

    Definition Message_In_Flags_Get_W_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists msg, args = [ADT (Message_In_Flags msg)];
              PostCond args ret :=
                exists msg, args = [(ADT (Message_In_Flags msg),
                                     Some (Message_In_Flags msg)) ] /\
                            ret = SCA _
                                      (Get_In_CodMap_W (snd (CallFlagsGetMethod _ msg idx (Get_In_DomMap_W tt))))
            |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_In_CodMap_W
      : Memory.W -> fst
                      (MethodDomCod (FlagsADTSig TopicNames topics)
                                    (ibound (indexb (BuildSetFlagsMethodID TopicNames topics idx)))).

    Definition Message_In_Flags_Set_W_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists msg w, args = [ADT (Message_In_Flags msg), SCA _ w];
              PostCond args ret :=
                exists msg w, args = [(ADT (Message_In_Flags msg),
                                       Some (Message_In_Flags (fst (CallFlagsSetMethod _ msg idx (Set_In_CodMap_W w))))),
                                      (SCA _ w, None)
                                     ]
            |}; crush_types.
    Defined.
  End Message_In_Flags_Specs.

  Section Message_Out_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Publications Node.

    Variable idx' : BoundedIndex (RADL_Publications Node).
    Let idx : Fin.t (RADL_NumPublications Node) := ibound (indexb idx').

    Section Message_OutW.

      Variable Get_In_DomMap_W
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
      Variable Get_In_CodMap_W
        : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
          -> Memory.W.

      Definition Message_Out_Get_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg, args = [ADT (Message_Out msg)];
                PostCond args ret :=
                  exists msg, args = [(ADT (Message_Out msg),
                                       Some (Message_Out msg)) ] /\
                              ret = SCA _
                                        (Get_In_CodMap_W (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap_W tt))))
              |}; crush_types.
      Defined.

      (* Coercions for setter domain and codomain values. *)
      Variable Set_In_CodMap_W
        : Memory.W ->
          fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
      Definition Message_Out_Set_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg w, args = [ADT (Message_Out msg), SCA _ w];
                PostCond args ret :=
                  exists msg w, args = [(ADT (Message_Out msg),
                                         Some (Message_Out (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap_W w))))),
                                        (SCA _ w, None)
                                       ]
              |}; crush_types.
      Defined.

    End Message_OutW.

  End Message_Out_Specs.

  Section Monitor_Message_Out_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADLM_Publications MNode.

    Variable idx' : BoundedIndex (RADLM_Publications MNode).
    Let idx : Fin.t (RADLM_NumPublications MNode) := ibound (indexb idx').

    Section Monitor_Message_OutW.
      Variable Get_In_DomMap_W
      : unit -> fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                                  (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx)))).
      Variable Get_In_CodMap_W
        : snd (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildGetMessageMethodID TopicTypes TopicNames topics idx))))
          -> Memory.W.

      Definition Monitor_Message_Out_Get_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg, args = [ADT (Monitor_Message_Out msg)];
                PostCond args ret :=
                  exists msg, args = [(ADT (Monitor_Message_Out msg),
                                       Some (Monitor_Message_Out msg)) ] /\
                              ret = SCA _
                                        (Get_In_CodMap_W (snd (CallMessageGetMethod _ _ _ msg idx (Get_In_DomMap_W tt))))
              |}; crush_types.
      Defined.

      (* Coercions for setter domain and codomain values. *)
      Variable Set_In_CodMap_W
        : Memory.W ->
          fst (MethodDomCod (MessageADTSig TopicTypes TopicNames topics)
                            (ibound (indexb (BuildSetMessageMethodID TopicTypes TopicNames topics idx)))).
      Definition Monitor_Message_Out_Set_W_Spec
        : AxiomaticSpec RADLM_Node_ADTValues.
            refine {|
                PreCond args := exists msg w, args = [ADT (Monitor_Message_Out msg), SCA _ w];
                PostCond args ret :=
                  exists msg w, args = [(ADT (Monitor_Message_Out msg),
                                         Some (Monitor_Message_Out (fst (CallMessageSetMethod _ _ _ msg idx (Set_In_CodMap_W w))))),
                                        (SCA _ w, None)
                                       ]
              |}; crush_types.
      Defined.

    End Monitor_Message_OutW.
  End Monitor_Message_Out_Specs.

  Section Message_Out_Flags_Specs.
    (* Coercions for getter domain and codomain values. *)
    Let topics := RADL_Publications Node.
    Variable idx : Fin.t (RADL_NumPublications Node).
    Variable Get_Out_DomMap_W
      : unit -> fst (MethodDomCod (FlagsADTSig TopicNames topics)
                                  (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx)))).
    Variable Get_Out_CodMap_W
      : snd (MethodDomCod (FlagsADTSig TopicNames topics)
                          (ibound (indexb (BuildGetFlagsMethodID TopicNames topics idx))))
        -> Memory.W.

    Definition Message_Out_Flags_Get_W_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists msg, args = [ADT (Message_Out_Flags msg)];
              PostCond args ret :=
                exists msg, args = [(ADT (Message_Out_Flags msg),
                                     Some (Message_Out_Flags msg)) ] /\
                            ret = SCA _
                                      (Get_Out_CodMap_W
                                         (snd (CallFlagsGetMethod _ msg idx (Get_Out_DomMap_W tt))))
            |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)
    Variable Set_Out_CodMap_W
      : Memory.W -> fst
                      (MethodDomCod (FlagsADTSig TopicNames topics)
                                    (ibound (indexb (BuildSetFlagsMethodID TopicNames topics idx)))).

    Definition Message_Out_Flags_Set_W_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists msg w, args = [ADT (Message_Out_Flags msg), SCA _ w];
              PostCond args ret :=
                exists msg w, args = [(ADT (Message_Out_Flags msg),
                                       Some (Message_Out_Flags (fst (CallFlagsSetMethod _ msg idx (Set_Out_CodMap_W w))))),
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

    Definition Struct_Get_W_Spec
               {T}
               (_ : T -> DecTuple2 attrs)
               (Get_DomMap_W :
                  unit
                  -> fst (MethodDomCod sig
                                       (ibound (indexb (BuildGetTuple2MethodID heading idx)))))
               (Get_CodMap_W :
                  snd (MethodDomCod sig (ibound (indexb (BuildGetTuple2MethodID heading idx))))
                  -> Memory.W)
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists msg : DecTuple2 attrs, args = [ADT (Struct msg)];
              PostCond args ret :=
                exists msg, args = [(ADT (Struct msg),
                                     Some (Struct msg)) ] /\
                            ret = SCA _
                                      (Get_CodMap_W
                                         (snd (CallTuple2GetMethod _ msg idx (Get_DomMap_W tt))))
            |}; crush_types.
    Defined.

    (* Coercions for setter domain and codomain values. *)

    Definition Struct_Set_W_Spec
               {T}
               (_ : T -> DecTuple2 attrs)
               (Set_CodMap_W
                : Memory.W
                  -> fst (MethodDomCod sig (ibound (indexb (BuildSetTuple2MethodID heading idx)))))
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists (msg : DecTuple2 attrs) w, args = [ADT (Struct msg), SCA _ w];
              PostCond args ret :=
                exists msg w, args = [(ADT (Struct msg),
                                       Some (Struct (fst (CallTuple2SetMethod _ msg idx (Set_CodMap_W w))))),
                                      (SCA _ w, None)
                                     ]
            |}; crush_types.
    Defined.
  End Struct_Specs.

  Section Monitored_Node_Specs.

    Definition Monitored_Node_Init_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := args = [ ];
              PostCond args ret :=
                exists r,
                  computes_to (callCons ADTSpec RADL_Init ()) r
                  /\ args = [ ]
                  /\ ret = ADT (RADLM_Node r)
            |}; crush_types.
    Defined.

    Definition Monitored_Node_Start_Step_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists node in_ in_flags monitor_in,
                args = [ADT (RADLM_Node node),
                        ADT (Message_In in_),
                        ADT (Message_In_Flags in_flags),
                        ADT (Monitor_Message_In monitor_in)
                       ];
              PostCond args ret :=
                exists node node' in_ in_flags monitor_in in_' in_flags',
                  computes_to (callMeth ADTSpec RADL_Start_Step node {| radlm_in := in_;
                                                                        radlm_in_flags := in_flags;
                                                                        radlm_monitor_in := monitor_in |}) (node', (in_', in_flags'))
                  /\ args = [ (ADT (RADLM_Node node), Some (RADLM_Node node')),
                              (ADT (Message_In in_), Some (Message_In in_')),
                              (ADT (Message_In_Flags in_flags), Some (Message_In_Flags in_flags')),
                              (ADT (Monitor_Message_In monitor_in), Some (Monitor_Message_In monitor_in)) ]
            |}; crush_types.
    Defined.

    Definition Monitored_Node_Finish_Step_Spec
      : AxiomaticSpec RADLM_Node_ADTValues.
          refine {|
              PreCond args := exists node out_ out_flags,
                args = [ADT (RADLM_Node node),
                        ADT (Message_Out out_),
                        ADT (Message_Out_Flags out_flags)
                       ];
              PostCond args ret :=
                exists node node' out out_flags monitor_out out' out_flags',
                  computes_to (callMeth ADTSpec RADL_Finish_Step node {| radlm_out := out;
                                                                        radlm_out_flags := out_flags |}) (node', (out', out_flags', monitor_out))
                  /\ args = [ (ADT (RADLM_Node node), Some (RADLM_Node node')),
                              (ADT (Message_Out out), Some (Message_Out out')),
                              (ADT (Message_Out_Flags out_flags), Some (Message_Out_Flags out_flags')),
                              (ADT (Monitor_Message_Out monitor_out), Some (Monitor_Message_Out monitor_out)) ]
            |}; crush_types.
    Defined.

  End Monitored_Node_Specs.

End RADLM_NodeADTs.
