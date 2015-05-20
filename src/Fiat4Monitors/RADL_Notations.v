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
  (existT attrType {| attrName := name;
                      attrType := type%Tuple2 |}
          init): Field_scope.

Notation "'topic' '{' 'FIELDS' topic1 ; .. ; topicn '}' " :=
  (@Tuple (Build_Heading (map (@projT1 _ _) (cons topic1%Field .. (cons topicn%Field nil) ..)))) (at level 70, arguments at level 60) : Topic_scope.

(* Notation to automatically inject subtopics into TopicIDs in SubMessage*)
Delimit Scope SubMessage_scope with SubMessage.

Notation "[ msg1 ; .. ; msgn ]" :=
  (cons (``(``(msg1%string))) .. (cons (``(``(msgn%string))) nil) ..) : SubMessage_scope.

Global Arguments SubMessage {Topics topics} subtopics%SubMessage msg.

Hint Extern 0 (IndexBound _ (map _ _)) =>
progress simpl; eauto with typeclass_instances : typeclass_instances.

(* All the landshark topics from topics.v . *)

Definition Struct := sigT (@Tuple2).

Delimit Scope Struct_scope with Struct.

Notation "name '`:' type '`:=' init" :=
  (existT attrType2 {| attrName2 := name;
                       attrType2 := type |} init)
  : Struct_scope.

Fixpoint BuildStruct (attrs : list (sigT (fun attr => attrType2 attr)))
: InitTupleDom2 (map (@projT1 _  _) attrs) :=
  match attrs return
        InitTupleDom2 (map (@projT1 _ _) attrs) with
    | [ ] => ()
    | attr :: attrs' =>
      (projT2 attr, BuildStruct attrs')
  end.

Notation "'struct' '{' 'FIELDS' topic1 ; .. ; topicn '}' " :=
  (existT InitTupleDom2 _ (BuildStruct (cons topic1%Struct .. (cons topicn%Struct nil) ..))) (at level 70, arguments at level 60) : Struct_scope.

Notation "name '=' struc" :=
  (existT attrType
          {| attrName := name;
             attrType := @Tuple2 (Build_Heading2 (projT1 struc)) |}
          (ConstructTuple2 (Build_Heading2 (projT1 struc)) (projT2 struc))
  )
  : Field_scope.

  Notation "name '{' 'TOPIC' type '}'" :=
    (Build_RADL_Topic name type) (at level 0, type at level 0)
    : Topic_scope.

  Notation "[ msg1 ; .. ; msgn ]" :=
  (cons (``(msg1%string)) .. (cons ``(msgn%string) nil) ..) : Node_scope.

  Notation "'node' '{' 'DEFS' definitions 'PUBLISHES' publications 'SUBSCRIBES' subscriptions 'PERIOD' period 'PATH' path 'CXX' '{' cstuff '}' '}'" :=
    {| RADL_Publications := publications%Topic;
       RADL_Subscriptions := subscriptions%Topic;
       RADL_Defs := definitions;
       RADL_Period := period;
       RADL_Path := path;
       RADL_CXX := cstuff |}
      (at level 0) : Node_scope.
