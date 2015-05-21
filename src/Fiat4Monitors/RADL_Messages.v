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
        Fiat.Fiat4Monitors.RADL_Topics.

Section Messages.

  Global Open Scope ADT_scope.
  Global Open Scope string_scope.
  Global Open Scope list_scope.
  Global Open Scope ADTSig_scope.

  Context {n : nat}.
  Variable TopicTypes : Vector.t Type n. (* List of Topics in the Network. *)
  Variable TopicNames : Vector.t string n. (* List of Topics IDs in the Network. *)
  Let TopicID := @TopicID n.

  Context {n' : nat}.
  Variable subtopics : Vector.t (Fin.t n) n'.

  Fixpoint SubTopicTypes {n''} (subtopics' : Vector.t (Fin.t n) n'')
    : Vector.t Type n'' :=
    match subtopics' in Vector.t _ n''
          return Vector.t Type n'' with
    | Vector.nil => Vector.nil _
    | Vector.cons k n'' subtopics' =>
      Vector.cons _ (Vector.nth TopicTypes k) n'' (SubTopicTypes subtopics')
    end.

  Definition Message' {n''} (subtopics' : Vector.t (Fin.t n) n'') :=
    ilist2 (B := id) (SubTopicTypes subtopics').
  Definition Message := Message' subtopics.

  Fixpoint CastTopic_1'
             {n''}
             (subtopics' : Vector.t (Fin.t n) n'')
             (n''' : Fin.t n'')
             {struct n'''}
    : Vector.nth (SubTopicTypes subtopics') n''' ->
      Vector.nth TopicTypes (Vector.nth subtopics' n''').
        refine (match subtopics' in Vector.t _ n'' return
                      forall (n''' : Fin.t n''),
                       Vector.nth (SubTopicTypes subtopics') n''' ->
                       Vector.nth TopicTypes (Vector.nth subtopics' n''')
               with
               | Vector.nil => fun n''' il => _
               | Vector.cons SubTopic k subTopicNames' => _
               end n'''); simpl in *.
        - inversion n'''0.
        - intro; revert subtopics' subTopicNames'.
          pattern k, n'''0.
          match goal with
            |- ?P k n'''0 => simpl; apply (Fin.rectS P); simpl; intros;
                              eauto
          end.
  Defined.

  Definition GetTopic'
             {n''}
             (subtopics' : Vector.t (Fin.t n) n'')
             (msg : Message' subtopics')
             (subtopic : Fin.t n'')
    : Vector.nth TopicTypes (Vector.nth subtopics' subtopic).
  Proof.
    generalize (ith2 msg subtopic); apply CastTopic_1'.
  Defined.

  Definition GetTopic
             (msg : Message)
             (subtopic : Fin.t n')
    : Vector.nth TopicTypes (Vector.nth subtopics subtopic) :=
    GetTopic' _  msg subtopic.

  Fixpoint CastTopic_2'
           {n''}
           (subtopics' : Vector.t (Fin.t n) n'')
           (n''' : Fin.t n'')
           {struct n'''}
    : Vector.nth TopicTypes (Vector.nth subtopics' n''') ->
      Vector.nth (SubTopicTypes subtopics') n'''.
  Proof.
    refine (match subtopics' in Vector.t _ n'' return
                  forall (n''' : Fin.t n''),
                    Vector.nth TopicTypes (Vector.nth subtopics' n''') ->
                    Vector.nth (SubTopicTypes subtopics') n'''
            with
            | Vector.nil => fun n''' il => _
            | Vector.cons SubTopic k subTopicNames' => _
            end n'''); simpl in *.
    - inversion n'''0.
    - intro; revert subtopics' subTopicNames'.
      pattern k, n'''0.
      match goal with
        |- ?P k n'''0 => simpl; apply (Fin.rectS P); simpl; intros;
                         eauto
      end.
  Defined.

  Definition SetTopic'
             {n''}
             (subtopics' : Vector.t (Fin.t n) n'')
             (msg : Message' subtopics')
             (subtopic : Fin.t n'')
             (new_topic : Vector.nth TopicTypes (Vector.nth subtopics' subtopic))
    : Message' subtopics'.
  Proof.
    apply (replace_Index2 _ msg subtopic); revert new_topic; apply CastTopic_2'.
  Defined.

  Definition SetTopic
             (msg : Message)
             (subtopic : Fin.t n')
             (new_topic : Vector.nth TopicTypes (Vector.nth subtopics subtopic))
    : Message :=
    SetTopic' _ msg subtopic new_topic.

  Section RADL_MessageADT.

    Open Scope methSig.
    Open Scope consSig.
    Open Scope cMethDef.
    Open Scope cConsDef.

    (* Message Initialization *)
    Definition Message_Init := "Init".

    Definition InitMessageDom := Message.

    Definition InitMessageSig : consSig :=
      Constructor Message_Init : InitMessageDom -> rep.

    Definition InitMessage : InitMessageDom -> Message := id.

    Definition InitMessageDef :=
      Def Constructor Message_Init (inits : InitMessageDom) : rep :=
      InitMessage inits.

    (* Getters and Setters for Messages *)

    Definition GetMessageSig (topic : Fin.t n) :=
      Method ("Get" ++ (Vector.nth TopicNames topic))
      : rep x unit -> rep x (Vector.nth TopicTypes topic).

    Definition SetMessageSig (topic : Fin.t n) :=
      Method ("Set" ++ (Vector.nth TopicNames topic))
      : rep x (Vector.nth TopicTypes topic) -> rep x unit.

    Fixpoint MessageSigs'
             {n''}
             (subtopics' : Vector.t (Fin.t n) n'')
      : Vector.t methSig (n'' * 2) :=
      match subtopics' in Vector.t _ n''
            return Vector.t methSig (n'' * 2) with
        | Vector.nil => Vector.nil _
        | Vector.cons topic _ topics' =>
          Vector.cons _ (GetMessageSig topic) _
                      (Vector.cons _ (SetMessageSig topic) _ (MessageSigs' topics'))
      end.

    Definition MessageSigs := MessageSigs' subtopics.

    Definition GetMessageDef
               {n''}
               (subtopics' : Vector.t (Fin.t n) n'')
               (topic : Fin.t n'') :
      cMethDef (Rep := Message' subtopics') (GetMessageSig (Vector.nth subtopics' topic)) :=
      Def Method _ (msg : rep, g : unit)
      : (Vector.nth TopicTypes (Vector.nth subtopics' topic)) :=
        (msg, GetTopic' _ msg topic).

    Definition SetMessageDef
               {n''}
               (subtopics' : Vector.t (Fin.t n) n'')
               (topic : Fin.t n'') :
      cMethDef (Rep := Message' subtopics') (SetMessageSig (Vector.nth subtopics' topic)) :=
      Def Method _ (msg : rep, val : Vector.nth TopicTypes (Vector.nth subtopics' topic)) : unit :=
      (SetTopic' _ msg topic val, tt).

    Fixpoint MessageDefs'
             {m}
             (subtopics'' : Vector.t (Fin.t n) m)
             {n''}
             (subtopics' : Vector.t (Fin.t n) n'')
      : (forall (topic : Fin.t n''),
            cMethDef (Rep := Message' subtopics'')
                     (GetMessageSig (Vector.nth subtopics' topic)))
        -> (forall (topic : Fin.t n''),
               cMethDef
                 (Rep := Message' subtopics'')
                 (SetMessageSig (Vector.nth subtopics' topic)))
        -> ilist (B := cMethDef (Rep := Message' subtopics''))
              (MessageSigs' subtopics')
        :=
          match subtopics' in Vector.t _ n'' return
                (forall (topic : Fin.t n''),
                    cMethDef (Rep := Message' subtopics'')
                             (GetMessageSig (Vector.nth subtopics' topic)))
                -> (forall (topic : Fin.t n''),
                       cMethDef
                     (Rep := Message' subtopics'')
                     (SetMessageSig (Vector.nth subtopics' topic)))
                -> ilist (B := cMethDef (Rep := Message' subtopics''))
                         (MessageSigs' subtopics') with
          | Vector.nil => fun _ _ => tt
          | Vector.cons _ n0 subtopics' =>
            fun GetMessageDef SetMessageDef =>
              Build_prim_prod (GetMessageDef Fin.F1)
                              (Build_prim_prod (SetMessageDef Fin.F1)
                                               (@MessageDefs' _ subtopics'' _ subtopics'
                                                              (fun t => GetMessageDef (Fin.FS t))
                                                              (fun t => SetMessageDef (Fin.FS t))))
          end.

    Definition MessageDefs
               {n''}
               (subtopics' : Vector.t (Fin.t n) n'') :=
      MessageDefs' subtopics'
                   _ 
                   (GetMessageDef subtopics')
                   (SetMessageDef subtopics').

    (* Message ADT Definitions *)
    Definition MessageADTSig : ADTSig :=
      BuildADTSig (Vector.cons _ InitMessageSig _ (Vector.nil _))
                  MessageSigs.
    
    Definition MessageADT : cADT MessageADTSig :=
      BuildcADT (icons InitMessageDef inil)
                (MessageDefs subtopics).

    (* TODO: Everything from here down. *)
    (* Support for building messages. *)
    
    Notation CallConstructor CompADT idx :=
      (cConstructors CompADT (ibound (indexb (Build_BoundedIndex (Bound := {| bindex := idx; indexb := _ |})))
    Print cConstructors.

    
    Definition ConstructMessage (msg : cADT (MessageADTSig)) subtopics :=
      CallConstructor msg Message_Init subtopics.

    (* Support for calling message getters. *)
    Definition BuildGetMessageMethodID'
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

    Definition BuildGetMessageMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftTopics))
    : @BoundedString (map methID (MessageSigs LiftTopics))
      := BuildGetMessageMethodID' _ idx.

    Definition CallMessageGetMethod
               (r : Message topics)
               idx
      := cMethods MessageADT (BuildGetMessageMethodID idx) r.

    (* Support for calling message setters. *)
    Definition BuildSetMessageMethodID'
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

    Definition BuildSetMessageMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftTopics))
    : @BoundedString (map methID (MessageSigs LiftTopics))
      := BuildSetMessageMethodID' _ idx.

    Definition CallMessageSetMethod (r : Message topics) idx :=
      cMethods MessageADT (BuildSetMessageMethodID idx) r.

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
