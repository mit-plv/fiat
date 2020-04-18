Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Arith.Arith
        Coq.Program.Program
        Fiat.Common.ilist2
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.TupleADT
        Fiat.QueryStructure.Specification.Representation.Heading2
        Fiat.QueryStructure.Specification.Representation.Tuple2
        Fiat.QueryStructure.Specification.Representation.TupleADT2
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags
        Fiat.Fiat4Monitors.RADL_Nodes.

Require Bedrock.Platform.Facade.DFacade.

Delimit Scope Field_scope with Field.
Delimit Scope Topic_scope with Topic.
Delimit Scope Node_scope with Node.
Delimit Scope Publication_scope with Publication.
Delimit Scope Subscription_scope with Subscription.

Definition float64 := Word.word 64.
Definition O_64 := IL.natToWord' 64 0.

Definition int64 := Word.word 64.

Definition float32 := Memory.W.
Definition O_32 := IL.natToWord' 32 0.

Definition uint8 := Memory.B.
Definition O_8 := IL.natToWord' 8 0.

Definition bool := Memory.B.
Definition false := IL.natToWord' 8 0.
Definition true := IL.natToWord' 8 1.

Reserved Notation "name '`:' type '`:=' init"
         (at level 60,
          arguments at next level).

Notation "name '`:' type '`:=' init" :=
  (existT attrType2 {| attrName2 := name;
                       attrType2 := type%Tuple2 |}
          init): Field_scope.

Notation "'topic' '{' 'FIELDS' topic1 ; .. ; topicn '}' " :=
  (@DecTuple2 _ (Vector.map (@projT1 _ _) (Vector.cons _ topic1%Field _ .. (Vector.cons _ topicn%Field _ (Vector.nil _)) ..))) (at level 70, arguments at level 60) : Topic_scope.

(* Notation to automatically inject subtopics into TopicIDs in SubMessage*)
Delimit Scope SubMessage_scope with SubMessage.

Notation "[ msg1 ; .. ; msgn ]" :=
  (cons (``(``(msg1%string))) .. (cons (``(``(msgn%string))) nil) ..) : SubMessage_scope.

Hint Extern 0 (IndexBound _ (map _ _)) =>
progress simpl; eauto with typeclass_instances : typeclass_instances.

(* All the landshark topics from topics.v . *)

Definition Struct := sigT (@Tuple2).

Delimit Scope Struct_scope with Struct.

Notation "name '`:' type '`:=' init" :=
  (existT attrType2 {| attrName2 := name;
                       attrType2 := type |} init)
  : Struct_scope.

Fixpoint BuildStruct
         {n}
         (attrs : Vector.t (sigT (fun attr => attrType2 attr)) n)
  : InitTuple2Dom (BuildHeading2 (Vector.map (@projT1 _  _) attrs)) :=
  match attrs return
        InitTuple2Dom (BuildHeading2 (Vector.map (@projT1 _  _) attrs)) with
  | Vector.nil => ()
  | Vector.cons attr _ attrs' =>
    icons2 (B := id) (projT2 attr) (BuildStruct attrs')
  end.

Notation "'struct' '{' 'FIELDS' topic1 ; .. ; topicn '}' " :=
  (existT InitTuple2Dom _ (BuildStruct (Vector.cons _ topic1%Struct _ .. (Vector.cons _ topicn%Struct _ (Vector.nil _)) ..))) (at level 70, arguments at level 60) : Struct_scope.

Notation "name '=' struc" :=
  (existT attrType2
          {| attrName2 := name;
             attrType2 := @DecTuple2 _ _ |}
          (ConstructTuple2 (projT1 struc) (projT2 struc)))
  : Field_scope.

Notation "name '{' 'TOPIC' type '}'" :=
  (Build_RADL_Topic name type) (at level 0, type at level 0)
  : Topic_scope.

Class NetworkTopicNamesHint {NumNetworkTopics} :=
  { NetworkTopicNames : Vector.t string NumNetworkTopics }.

Class NetworkTopicTypesHint {NumNetworkTopics} :=
  { NetworkTopicTypes : Vector.t Type NumNetworkTopics }.

Notation "[ msg1 ; .. ; msgn ]" :=
  (Vector.cons _ (ibound (indexb (Build_BoundedIndex _ NetworkTopicNames msg1%string _))) _ .. (Vector.cons _ (ibound (indexb (Build_BoundedIndex _ NetworkTopicNames msgn%string _))) _ (Vector.nil _)) ..) : Node_scope.

Notation "[]" := (Vector.nil _ ) : Node_scope.

Notation "'node' 'using' Topics '{' 'DEFS' definitions 'PUBLISHES' publications 'SUBSCRIBES' subscriptions 'PERIOD' period 'PATH' path 'CXX' '{' cstuff '}' '}'" :=
  (let _ : NetworkTopicNamesHint := {| NetworkTopicNames := Vector.map Topic_Name Topics |} in
   ({| RADL_Publications := publications%Topic%vector;
       RADL_Subscriptions := subscriptions%Topic%vector;
       RADL_Defs := definitions%list;
       RADL_Period := period;
       RADL_Path := path;
       RADL_CXX := cstuff |}))
    (Topics at level 0, at level 0) : Node_scope.

Notation "'monitor' 'node' 'for' Node 'using' Topics '{' 'PUBLISHES' publications 'SUBSCRIBES' subscriptions '}'" :=
  (let _ : NetworkTopicNamesHint := {| NetworkTopicNames := Vector.map Topic_Name Topics |} in
   ({| RADLM_MonitoredNode := Node;
       RADLM_Publications := publications%Topic%vector;
       RADLM_Subscriptions := subscriptions%Topic%vector |}))
    (Topics at level 0, at level 0) : Node_scope.

Notation GetMessageTopic r idx := (
                            let m := _ : Vector.t (Fin.t _) _ in
                            CallMessageGetMethod NetworkTopicTypes
                                                 NetworkTopicNames
                                                 m r
                                                 (ibound (indexb ((@Build_BoundedIndex (Fin.t _) _ m (ibound (indexb ((@Build_BoundedIndex string _ NetworkTopicNames idx%string _)))) (_ : IndexBound _ m)))))
                                                                                      tt).
Notation "r '~~>' idx" := (GetMessageTopic r idx)
                            (idx at level 0, at level 70) : Node_scope.

Notation GetMessageTopicS r idx R :=
  (let b := _ in
   let attrs := Vector.map (projT1 (P:=Heading2.attrType2)) b in
   let b' := Vector.map (fun attr' => Heading2.attrName2 (@projT1 _ _ attr')) b in
   snd (@CallDecTuple2GetMethod _ attrs (snd (GetMessageTopic r idx))
                                (ibound (indexb ((@Build_BoundedIndex _ _ b' R%string _)))) ())).

Notation UpdateMessageTopicS r idx idx' d :=
  (let m := _ : Vector.t (Fin.t _) _ in
   fst (CallMessageSetMethod NetworkTopicTypes
                             NetworkTopicNames
                             m r
                             (ibound (indexb ((@Build_BoundedIndex (Fin.t _) _ m (ibound (indexb ((@Build_BoundedIndex string _ NetworkTopicNames idx%string _)))) (_ : IndexBound _ m)))))
                             (Tuple2.SetAttribute2' (snd (GetMessageTopic r idx))
                                                    (@Build_BoundedIndex string _ _ idx' _) d))).
