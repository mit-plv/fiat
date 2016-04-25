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

    Open Scope methSig_scope.
    Open Scope consSig_scope.
    Open Scope cMethDef_scope.
    Open Scope cConsDef_scope.

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

    (* Support for building messages. *)

    Definition ConstructMessage subtopics :=
      CallConstructor MessageADT Message_Init subtopics.

    (* Support for calling message getters. *)
        Lemma BuildGetMessageMethodID_ibound
      {n''}
      (subtopics' : Vector.t (Fin.t n) n'')
      : forall (idx : Fin.t n''),
        Vector.nth (Vector.map methID (MessageSigs' subtopics'))
                   (Fin.depair idx Fin.F1) =
        ("Get" ++ Vector.nth TopicNames (Vector.nth subtopics' idx))%string.
    Proof.
      induction subtopics'.
      - intro; inversion idx.
      - intro; revert subtopics' IHsubtopics'; pattern n0, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildGetMessageMethodID'
               {n''}
               (subtopics' : Vector.t (Fin.t n) n'')
               (idx : Fin.t n'')
    : BoundedString (Vector.map methID (MessageSigs' subtopics')) :=
      {| bindex := ("Get" ++ (Vector.nth TopicNames (Vector.nth subtopics' idx)))%string;
         indexb := {| ibound := Fin.depair idx (@Fin.F1 1);
                      boundi := BuildGetMessageMethodID_ibound subtopics' idx |}
      |}.

    Definition BuildGetMessageMethodID
               (idx : Fin.t n')
      : BoundedString (Vector.map methID MessageSigs)
      := BuildGetMessageMethodID' _ idx.

    Definition CallMessageGetMethod
               (r : Message)
               idx
      := cMethods MessageADT (ibound (indexb (BuildGetMessageMethodID idx))) r.

    (* Support for calling message setters. *)
    Lemma BuildSetMessageMethodID_ibound
      {n''}
      (subtopics' : Vector.t (Fin.t n) n'')
      : forall (idx : Fin.t n''),
        Vector.nth (Vector.map methID (MessageSigs' subtopics'))
                   (Fin.depair idx (Fin.FS Fin.F1)) =
        ("Set" ++ Vector.nth TopicNames (Vector.nth subtopics' idx))%string.
    Proof.
      induction subtopics'.
      - intro; inversion idx.
      - intro; revert subtopics' IHsubtopics'; pattern n0, idx.
        eapply Fin.rectS; simpl; intros; eauto.
    Qed.

    Definition BuildSetMessageMethodID'
               {n''}
               (subtopics' : Vector.t (Fin.t n) n'')
               (idx : Fin.t n'')
    : BoundedString (Vector.map methID (MessageSigs' subtopics')) :=
      {| bindex := ("Set" ++ (Vector.nth TopicNames (Vector.nth subtopics' idx)))%string;
         indexb := {| ibound := Fin.depair idx (Fin.FS Fin.F1);
                      boundi := BuildSetMessageMethodID_ibound subtopics' idx |}
      |}.

    Definition BuildSetMessageMethodID
               (idx : Fin.t n')
      : BoundedString (Vector.map methID MessageSigs)
      := BuildSetMessageMethodID' _ idx.

    Definition CallMessageSetMethod
               (r : Message)
               idx
      := cMethods MessageADT (ibound (indexb (BuildSetMessageMethodID idx))) r.

  End RADL_MessageADT.

  (* Support for calling message constructors.

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
                  (SubMessageDom subtopics msg). *)
End Messages.

(* Notation to automatically inject subtopics into TopicIDs in SubMessage*)
Delimit Scope SubMessage_scope with SubMessage.

Notation "[ msg1 ; .. ; msgn ]" :=
  (cons (``(``(msg1%string))) .. (cons (``(``(msgn%string))) nil) ..) : SubMessage_scope.

(*Global Arguments SubMessage {Topics topics} subtopics%SubMessage msg.*)

(*Hint Extern 0 (IndexBound _ (map _ _)) =>
progress simpl; eauto with typeclass_instances : typeclass_instances. *)
