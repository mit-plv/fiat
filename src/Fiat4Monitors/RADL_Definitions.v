Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements.

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

  Definition TopicTypes
             (topic : TopicID) : Type :=
    Topic_Type (nth_Bounded Topic_Name Topics topic).

  Definition Message topics :=
    ilist TopicTypes topics.

  Fixpoint SubTopic
           (topics : list TopicID)
           {struct topics}
  : Message topics ->
    forall (subtopic : BoundedIndex topics),
      TopicTypes (bindex subtopic).
  Proof.
    refine (match topics return
                  Message topics ->
                  forall (subtopic : BoundedIndex topics),
                    TopicTypes (bindex subtopic) with
              | nil => fun msg subtopic => BoundedIndex_nil _ subtopic
              | topic :: topics' =>  fun msg subtopic => _
            end).
    destruct subtopic as [idx [[ | n] nth_n]].
    simpl in *; injection nth_n; intros; subst.
    exact (ith_Bounded id msg {| bindex := _;
                                indexb := Build_IndexBound (idx :: (map id topics')) 0 nth_n|}).
    exact (SubTopic topics' (ilist_tl msg) {| bindex := idx;
                       indexb := {| ibound := n;
                                    boundi := nth_n |} |} ).
  Defined.

  Fixpoint SubMessage
             (topics : list TopicID)
             (subtopics : list (BoundedIndex  topics))
             (msg : Message topics)
  : Message (map (bindex (Bound := topics)) subtopics) :=
    match subtopics return Message (map (bindex (Bound := topics)) subtopics) with
      | nil => inil _
      | subtopic :: subtopics' =>
        icons _ (SubTopic msg subtopic )
              (SubMessage subtopics' msg)
    end.

  Definition RADL_ADTSig  (Node : RADL_Node)
  : ADTSig :=                         (* A RADL Node is modeled as an ADT with a  *)
    ADTsignature {                    (* single constructor and a step function. *)
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x Message (RADL_Subscriptions Node)
                                     -> rep x Message (RADL_Publications Node)
      }.

  Definition RADL_ADTSpec (Node : RADL_Node)
  : ADT (RADL_ADTSig Node) :=
    ADTRep unit (* Since RADL Nodes are untrusted, we'll treat their state as completely unknown *)
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : Message (RADL_Subscriptions Node)) : _ :=
               (* Again, since the RADL Node is untrusted code, we'll assume that it can publish
                  whatever the heck it wants. *)
               results <- {out_t : Message (RADL_Publications Node) | True };
             ret (tt, results) }.

  Definition RADLM_ADTSig
             (MonitorNode : RADL_Node)
             (InitDom : Type)
  : ADTSig :=
    ADTsignature {
        Constructor RADL_Init      : InitDom -> rep,
        Method      RADL_Step      : rep x unit * Message (RADL_Subscriptions MonitorNode)
                                     -> rep x unit * Message (RADL_Publications MonitorNode)
      }.

End RADL_Definitions.

Notation GetTopic il idx := (SubTopic il ``(``idx)).
