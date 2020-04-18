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
        Fiat.ADTRefinement.BuildADTRefinements.

Section Topics.

  Record RADL_Topic :=
    { Topic_Name : string;
      Topic_Type : Type }.

  Context {n : nat}.
  Variable TopicTypes : Vector.t Type n. (* List of Topics in the Network. *)
  Variable TopicNames : Vector.t string n. (* List of Topics IDs in the Network. *)
  Definition TopicID  := Fin.t n.

  Definition GetTopicName (topic : TopicID) : string := Vector.nth TopicNames topic.

  Definition GetTopicType (topic : TopicID) : Type := Vector.nth TopicTypes topic.

End Topics.
