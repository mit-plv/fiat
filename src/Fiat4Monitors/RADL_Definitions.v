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

Section Messages.

  Global Open Scope ADT_scope.
  Global Open Scope string_scope.
  Global Open Scope list_scope.
  Global Open Scope ADTSig_scope.

  Record RADL_Topic :=
    { Topic_Name : string;
      Topic_Type : Type }.

  Variable Topics : list RADL_Topic. (* List of Topics in the Network. *)
  Definition TopicID  := @BoundedString (map Topic_Name Topics).

  Definition TopicNames
             (topic : TopicID) : string :=
    Topic_Name (nth_Bounded Topic_Name Topics topic).

  Definition TopicTypes
             (topic : TopicID) : Type :=
    Topic_Type (nth_Bounded Topic_Name Topics topic).

  Definition Message topics := ilist TopicTypes topics.

  Fixpoint GetTopic
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
              | [ ] => fun msg subtopic => BoundedIndex_nil _ subtopic
              | topic :: topics' =>  fun msg subtopic => _
            end).
    destruct subtopic as [idx [[ | n] nth_n]].
    simpl in *; injection nth_n; intros; subst.
    exact (ith_Bounded id msg {| bindex := _;
                                indexb := Build_IndexBound (idx :: (map id topics')) 0 nth_n|}).
    exact (GetTopic topics' (ilist_tl msg) {| bindex := idx;
                       indexb := {| ibound := n;
                                    boundi := nth_n |} |} ).
  Defined.

  Fixpoint SetTopic
           (topics : list TopicID)
           {struct topics}
  : Message topics ->
    forall (subtopic : BoundedIndex topics),
      TopicTypes (bindex subtopic) ->
      Message topics.
  Proof.
    refine (match topics return
                  Message topics ->
                  forall (subtopic : BoundedIndex topics),
                    TopicTypes (bindex subtopic) -> Message topics with
              | [ ] => fun msg subtopic val => inil _
              | topic :: topics' =>  fun msg subtopic val => _
            end).
    destruct subtopic as [idx [[ | n] nth_n]].
    - simpl in *; injection nth_n; intros; subst;
      exact (icons _ val (ilist_tl msg)).
    - exact (icons _ (ilist_hd msg) (SetTopic topics' (ilist_tl msg)
                                              {| bindex := idx;
                                                 indexb := {| ibound := n;
                                                              boundi := nth_n |} |}
                                              val)).
  Defined.

  Section RADL_MessageADT.

    Open Scope methSig.
    Open Scope consSig.
    Open Scope cMethDef.
    Open Scope cConsDef.

    (* Message Initialization *)
    Definition Message_Init := "Init".

    Fixpoint InitMessageDom (topics : list TopicID) :=
      match topics return Type with
        | [ ] => unit
        | topic :: topics' => prod (TopicTypes topic) (InitMessageDom topics')
      end.

    Definition InitMessageSig (topics : list TopicID) : consSig :=
      Constructor Message_Init : InitMessageDom topics -> rep.

    Fixpoint InitMessage (topics : list TopicID)
    : InitMessageDom topics -> Message topics :=
      match topics return
            InitMessageDom topics -> Message topics with
        | [ ] =>
          fun inits => inil _
        | topic :: topics' =>
          fun inits => icons _ (fst inits) (InitMessage topics' (snd inits))
      end.

    Definition InitMessageDef (topics : list TopicID) :=
      Def Constructor Message_Init (inits : InitMessageDom topics) : rep :=
      InitMessage topics inits.

    (* Getters and Setters for Messages *)
    Variable topics : list TopicID.

    Definition GetMessageSig (topic : BoundedIndex topics) :=
      Method ("Get" ++ TopicNames (bindex topic)) : rep x unit -> rep x TopicTypes (bindex topic).

    Definition SetMessageSig (topic : BoundedIndex topics) :=
      Method ("Set" ++ TopicNames (bindex topic)) : rep x TopicTypes (bindex topic) -> rep x unit.

    Fixpoint MessageSigs (subtopics : list (BoundedIndex topics)) : list methSig :=
      match subtopics with
        | [ ] => [ ]
        | topic :: topics' =>
          GetMessageSig topic :: SetMessageSig topic :: MessageSigs topics'
      end.

    Definition GetMessageDef (topic : BoundedIndex topics) :
      cMethDef (Rep := Message topics) (GetMessageSig topic) :=
      Def Method _ (msg : rep, _ : _) : TopicTypes (bindex topic) :=
      (msg, GetTopic msg topic).

    Definition SetMessageDef (topic : BoundedIndex topics) :
      cMethDef (Rep := Message topics) (SetMessageSig topic) :=
      Def Method _ (msg : rep, val : TopicTypes (bindex topic)) : unit :=
      (SetTopic msg _ val, tt).

    Fixpoint MessageDefs'
             (subtopics : list (BoundedIndex topics))
    : ilist (cMethDef (Rep := Message topics)) (MessageSigs subtopics) :=
      match subtopics return
            ilist (cMethDef (Rep := Message topics)) (MessageSigs subtopics) with
        | [ ] => inil _
        | topic :: subtopics' =>
          icons _ (GetMessageDef topic) (icons _ (SetMessageDef topic) (MessageDefs' subtopics'))
      end.

    Definition LiftTopics : list (BoundedIndex topics) :=
      (fix LiftTopics (topics : list TopicID) : list (BoundedIndex topics) :=
         match topics with
           | [ ] => [ ]
           | topic :: topics' =>
             {| bindex := _; indexb := IndexBound_head _ _ |}
               :: (map (fun idx : BoundedIndex topics' =>
                          {| bindex := bindex idx;
                             indexb := @IndexBound_tail _ _ topic _ (indexb idx) |})
                       (LiftTopics topics'))
         end) topics.

    Definition MessageDefs := MessageDefs' LiftTopics.

    (* Message ADT Definitions *)
    Definition MessageADTSig : ADTSig :=
      BuildADTSig [InitMessageSig topics] (MessageSigs LiftTopics).

    Definition MessageADT : cADT MessageADTSig :=
      BuildcADT (icons _ (InitMessageDef topics) (inil _)) MessageDefs.

    (* Support for building messages. *)

    Definition ConstructMessage (msg : cADT (MessageADTSig)) subtopics :=
      CallConstructor msg Message_Init subtopics.

    (* Support for calling message getters. *)
    Definition BuildGetMethodID'
               (subtopics : list (BoundedIndex topics))
               (idx : BoundedIndex (map (fun id => bindex id) subtopics))
    : @BoundedString (map methID (MessageSigs subtopics)).
      refine {| bindex := ("Get" ++ (bindex (bindex idx)))%string;
                indexb := {| ibound := 2 * ibound idx;
                             boundi := _ |}
             |}.
      destruct idx as [idx [n nth_n]].
      revert idx n nth_n; induction subtopics; intros.
      destruct n; simpl in *; discriminate.
      destruct n; simpl in *.
      - unfold value; repeat f_equal.
        destruct a as [b [m nth_m]]; simpl in *; subst.
        unfold TopicNames; injections.
        destruct idx as [topic [p nth_p]]; simpl in *.
        pose proof (nth_error_map _ _ _ nth_p).
        cut (exists topic'', nth_error Topics p = Some topic'' /\ Topic_Name topic'' = topic ).
        intros.
        eapply nth_Bounded_ind; intros.
        subst filtered_var program_branch_0 program_branch_1; simpl.
        destruct_ex; intuition.
        rewrite H1; eauto.
        revert H; clear.
        destruct (nth_error Topics p); intros;
        first [discriminate | injections; eauto].
      - rewrite plus_comm; simpl; rewrite plus_comm.
        eauto.
    Defined.

    Definition BuildGetMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftTopics))
    : @BoundedString (map methID (MessageSigs LiftTopics))
      := BuildGetMethodID' _ idx.

    Definition CallMessageGetMethod
               (r : Message topics)
               idx
      := cMethods MessageADT (BuildGetMethodID idx) r.

    (* Support for calling message setters. *)
    Definition BuildSetMethodID'
             (subtopics : list (BoundedIndex topics))
             (idx : BoundedIndex (map (fun id => bindex id) subtopics))
  : @BoundedString (map methID (MessageSigs subtopics)).
    Proof.
      refine {| bindex := ("Set" ++ (bindex (bindex idx)))%string;
                indexb := {| ibound := 2 * ibound idx + 1;
                             boundi := _ |}
             |}.
      destruct idx as [idx [n nth_n]].
      revert idx n nth_n; induction subtopics; intros.
      destruct n; simpl in *; discriminate.
      destruct n; simpl in *.
      - unfold value; repeat f_equal.
        destruct a as [b [m nth_m]]; simpl in *; subst.
        unfold TopicNames; injections.
        destruct idx as [topic [p nth_p]]; simpl in *.
        pose proof (nth_error_map _ _ _ nth_p).
        cut (exists topic'', nth_error Topics p = Some topic'' /\ Topic_Name topic'' = topic ).
        intros.
        eapply nth_Bounded_ind; intros.
        subst filtered_var program_branch_0 program_branch_1; simpl.
        destruct_ex; intuition.
        rewrite H1; eauto.
        revert H; clear.
        destruct (nth_error Topics p); intros;
        first [discriminate | injections; eauto].
      - rewrite plus_comm; simpl.
        rewrite <- (IHsubtopics idx n nth_n); f_equal.
        omega.
    Defined.

    Definition BuildSetMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftTopics))
    : @BoundedString (map methID (MessageSigs LiftTopics))
      := BuildSetMethodID' _ idx.

    Definition CallMessageSetMethod (r : Message topics) idx :=
      cMethods MessageADT (BuildSetMethodID idx) r.

  End RADL_MessageADT.

  (* Support for calling message constructors. *)

  Fixpoint SubMessageDom
           (topics : list TopicID)
           (subtopics : list (BoundedIndex topics))
           (msg : Message topics)
    : InitMessageDom (map (bindex (Bound := topics)) subtopics) :=
      match subtopics return InitMessageDom (map (bindex (Bound := topics)) subtopics) with
        | [ ] => ()
        | subtopic :: subtopics' =>
          (GetTopic msg subtopic, SubMessageDom subtopics' msg)
      end.

  Definition SubMessage
             (topics : list TopicID)
             (subtopics : list (BoundedIndex topics))
             (msg : Message topics)
  : cRep (MessageADT (map (bindex (Bound := topics)) subtopics)) :=
    cConstructors (MessageADT (map (bindex (Bound := topics)) subtopics))
                  ``Message_Init
                  (SubMessageDom subtopics msg).

  Section RADL_ADT.

  Definition RADL_Init := "Init".
  Definition RADL_Step := "Step".

  Record RADL_Node :=
    { (* Subscription + Publication info for this node *)
      RADL_Subscriptions : list TopicID;
      RADL_Publications : list TopicID
    }.

  Definition radl_in_t (Node : RADL_Node) := MessageADT (RADL_Subscriptions Node).
  Definition radl_out_t (Node : RADL_Node) := MessageADT (RADL_Publications Node).

  Definition RADL_ADTSig  (Node : RADL_Node)
  : ADTSig :=                         (* A RADL Node is modeled as an ADT with a  *)
    ADTsignature {                    (* single constructor and a step function. *)
        Constructor RADL_Init      : unit -> rep,
        Method      RADL_Step      : rep x cRep (radl_in_t Node)
                                     -> rep x cRep (radl_out_t Node)
      }.

    Definition RADL_ADTSpec (Node : RADL_Node)
  : ADT (RADL_ADTSig Node) :=
    ADTRep unit (* Since RADL Nodes are untrusted, we'll treat their state as completely unknown *)
           { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
             Def Method RADL_Step (r : rep, in_t : cRep (radl_in_t Node)) : _ :=
               (* Again, since the RADL Node is untrusted code, we'll assume that it can publish
                  whatever the heck it wants. *)
               results <- {out_t : cRep (radl_out_t Node) | True };
             ret (tt, results) }.

  Record RADLM_Node :=
    { (* The model of the monitor's internal state *)
      RADLM_Rep : Type;
      (* The monitored node*)
      RADLM_MonitoredNode : RADL_Node;
      (* Additional Subscription + Publication info *)
      RADLM_Subscriptions : list TopicID;
      RADLM_Publications : list TopicID
    }.

  Definition radlm_in_t (Node : RADLM_Node) :=
    MessageADT (RADL_Subscriptions (RADLM_MonitoredNode Node)).
  Definition radlm_out_t (Node : RADLM_Node) :=
    MessageADT (RADL_Publications (RADLM_MonitoredNode Node)).
  Definition radlm_monitor_in_t (Node : RADLM_Node) :=
    MessageADT (RADLM_Subscriptions Node).
  Definition radlm_monitor_out_t (Node : RADLM_Node) :=
    MessageADT (RADLM_Publications Node).

  Definition RADLM_ADTSig
             (MonitorNode : RADLM_Node)
             (InitDom : Type)
  : ADTSig :=
    ADTsignature {
        Constructor RADL_Init      : InitDom -> rep,
        Method      RADL_Step      : rep x unit * cRep (radlm_in_t MonitorNode) * cRep (radlm_monitor_in_t MonitorNode)
                                     -> rep x unit
                                        * cRep (radlm_out_t MonitorNode)
                                        * cRep (radlm_monitor_out_t MonitorNode)
      }.

  End RADL_ADT.
End Messages.

Notation "r '~~>' idx " := (CallMessageGetMethod r {|bindex := ``idx; indexb := _ |} tt)
                              (idx at level 0, at level 70).

(* Notation to automatically inject subtopics into TopicIDs in SubMessage*)
Delimit Scope SubMessage_scope with SubMessage.

Notation "[ msg1 ; .. ; msgn ]" :=
  (cons (``(``(msg1%string))) .. (cons (``(``(msgn%string))) nil) ..) : SubMessage_scope.

Global Arguments SubMessage {Topics topics} subtopics%SubMessage msg.

Hint Extern 0 (IndexBound _ (map _ _)) =>
progress simpl; eauto with typeclass_instances : typeclass_instances.
