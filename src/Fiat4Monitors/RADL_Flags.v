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
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics.
Require Import Bedrock.Memory.

Section Flags.

  Open Scope ADT_scope.
  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope ADTSig_scope.

  Variable Topics : list RADL_Topic. (* List of Topics in the Network. *)
  Let TopicID  := TopicID Topics.

  Definition Flag (topics : list TopicID)
    := ilist (fun _ => Memory.W) topics.

  Fixpoint GetFlag
           (topics : list TopicID)
           {struct topics}
  : Flag topics ->
    forall (subtopic : BoundedIndex topics),
      Memory.W.
  Proof.
    refine (match topics return
                  Flag topics ->
                  forall (subtopic : BoundedIndex topics), Memory.W  with
              | [ ] => fun msg subtopic => BoundedIndex_nil _ subtopic
              | topic :: topics' =>  fun msg subtopic => _
            end).
    destruct subtopic as [idx [[ | n] nth_n]].
    simpl in *; injection nth_n; intros; subst.
    exact (ith_Bounded id msg {| bindex := _;
                                indexb := Build_IndexBound (idx :: (map id topics')) 0 nth_n|}).
    exact (GetFlag topics' (ilist_tl msg) {| bindex := idx;
                                             indexb := {| ibound := n;
                                                          boundi := nth_n |} |} ).
  Defined.

  Fixpoint SetFlag
           (topics : list TopicID)
           {struct topics}
  : Flag topics ->
    forall (subtopic : BoundedIndex topics),
      Memory.W -> Flag topics.
  Proof.
    refine (match topics return
                  Flag topics ->
                  forall (subtopic : BoundedIndex topics),
                    Memory.W -> Flag topics with
              | [ ] => fun msg subtopic val => inil _
              | topic :: topics' =>  fun msg subtopic val => _
            end).
    destruct subtopic as [idx [[ | n] nth_n]].
    - simpl in *; injection nth_n; intros; subst;
      exact (icons _ val (ilist_tl msg)).
    - exact (icons _ (ilist_hd msg) (SetFlag topics' (ilist_tl msg)
                                              {| bindex := idx;
                                                 indexb := {| ibound := n;
                                                              boundi := nth_n |} |}
                                              val)).
  Defined.

  Section RADL_FlagADT.

    Open Scope methSig.
    Open Scope consSig.
    Open Scope cMethDef.
    Open Scope cConsDef.

    (* Message Initialization *)
    Definition Flag_Init := "Init".

    Fixpoint InitFlagDom (topics : list TopicID) :=
      match topics return Type with
        | [ ] => unit
        | topic :: topics' => prod Memory.W (InitFlagDom topics')
      end.

    Definition InitFlagSig (topics : list TopicID) : consSig :=
      Constructor Flag_Init : InitFlagDom topics -> rep.

    Fixpoint InitFlag (topics : list TopicID)
    : InitFlagDom topics -> Flag topics :=
      match topics return
            InitFlagDom topics -> Flag topics with
        | [ ] =>
          fun inits => inil _
        | topic :: topics' =>
          fun inits => icons _ (fst inits) (InitFlag topics' (snd inits))
      end.

    Definition InitFlagDef (topics : list TopicID) :=
      Def Constructor Flag_Init (inits : InitFlagDom topics) : rep :=
      InitFlag topics inits.

    (* Getters and Setters for Flags *)
    Variable topics : list TopicID.

    Definition GetFlagSig (topic : BoundedIndex topics) :=
      Method ("Get" ++ TopicNames (bindex topic)) : rep x unit -> rep x Memory.W.

    Definition SetFlagSig (topic : BoundedIndex topics) :=
      Method ("Set" ++ TopicNames (bindex topic)) : rep x Memory.W -> rep x unit.

    Fixpoint FlagSigs (subtopics : list (BoundedIndex topics)) : list methSig :=
      match subtopics with
        | [ ] => [ ]
        | topic :: topics' =>
          GetFlagSig topic :: SetFlagSig topic :: FlagSigs topics'
      end.

    Definition GetFlagDef (topic : BoundedIndex topics) :
      cMethDef (Rep := Flag topics) (GetFlagSig topic) :=
      Def Method _ (msg : rep, _ : _) : Memory.W :=
      (msg, GetFlag msg topic).

    Definition SetFlagDef (topic : BoundedIndex topics) :
      cMethDef (Rep := Flag topics) (SetFlagSig topic) :=
      Def Method _ (msg : rep, val : Memory.W) : unit :=
      (SetFlag msg topic val, tt).

    Fixpoint FlagDefs'
             (subtopics : list (BoundedIndex topics))
    : ilist (cMethDef (Rep := Flag topics)) (FlagSigs subtopics) :=
      match subtopics return
            ilist (cMethDef (Rep := Flag topics)) (FlagSigs subtopics) with
        | [ ] => inil _
        | topic :: subtopics' =>
          icons _ (GetFlagDef topic) (icons _ (SetFlagDef topic) (FlagDefs' subtopics'))
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

    Definition FlagDefs := FlagDefs' LiftTopics.

    (* Flag ADT Definitions *)
    Definition FlagADTSig : ADTSig :=
      BuildADTSig [InitFlagSig topics] (FlagSigs LiftTopics).

    Definition FlagADT : cADT FlagADTSig :=
      BuildcADT (icons _ (InitFlagDef topics) (inil _)) FlagDefs.

    (* Support for building messages. *)

    Definition ConstructFlag (msg : cADT (FlagADTSig)) subtopics :=
      CallConstructor msg Flag_Init subtopics.

    (* Support for calling message getters. *)
    Definition BuildGetFlagMethodID'
               (subtopics : list (BoundedIndex topics))
               (idx : BoundedIndex (map (fun id => bindex id) subtopics))
    : @BoundedString (map methID (FlagSigs subtopics)).
      refine {| bindex := ("Get" ++ (bindex (bindex idx)))%string;
                indexb := {| ibound := ibound idx * 2;
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
      - eauto.
    Defined.

    Definition BuildGetFlagMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftTopics))
    : @BoundedString (map methID (FlagSigs LiftTopics))
      := BuildGetFlagMethodID' _ idx.

    Definition CallFlagGetMethod
               (r : Flag topics)
               idx
      := cMethods FlagADT (BuildGetFlagMethodID idx) r.

    Lemma CallFlagMethodType :
      forall idx,
        snd (MethodDomCod FlagADTSig (BuildGetFlagMethodID idx)) = Memory.W.
    Proof.
      unfold FlagADTSig, BuildGetFlagMethodID, BuildGetFlagMethodID'; simpl.
      unfold FlagSigs.
      intro. eapply nth_Bounded_ind; simpl.
      refine (match idx with
                {| bindex := idx;
                   indexb := {| ibound := n;
                                boundi := nth_n |} |} => _
              end); simpl.
      revert indexb n nth_n.
      induction LiftTopics; intros; destruct n; simpl; eauto.
      eapply IHl; eauto.
      repeat econstructor; simpl in *; eauto.
      repeat econstructor; simpl in *; eauto.
    Defined.

    Definition CallFlagGetMethodAsWord
               (r : Flag topics)
               idx
               (t : fst (MethodDomCod FlagADTSig (BuildGetFlagMethodID idx)))
      : cRep FlagADT * Memory.W.
      rewrite <- (CallFlagMethodType idx).
      apply (cMethods FlagADT (BuildGetFlagMethodID idx) r t).
    Defined.

    (* Support for calling message setters. *)
    Definition BuildSetFlagMethodID'
             (subtopics : list (BoundedIndex topics))
             (idx : BoundedIndex (map (fun id => bindex id) subtopics))
  : @BoundedString (map methID (FlagSigs subtopics)).
    Proof.
      refine {| bindex := ("Set" ++ (bindex (bindex idx)))%string;
                indexb := {| ibound := (ibound idx * 2) + 1;
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
      - eauto.
    Defined.

    Definition BuildSetFlagMethodID
               (idx : BoundedIndex (map (fun id => bindex id) LiftTopics))
    : @BoundedString (map methID (FlagSigs LiftTopics))
      := BuildSetFlagMethodID' _ idx.

    Definition CallFlagSetMethod (r : Flag topics) idx :=
      cMethods FlagADT (BuildSetFlagMethodID idx) r.

  End RADL_FlagADT.

  Definition radl_i2f := Word.natToWord 32.

  Definition radl_OPERATIONAL_FLAGS := Eval simpl in radl_i2f 15.
  Definition radl_STALE_VALUE := Eval simpl in radl_i2f 1.
  Definition radl_STALE_MBOX :=    Eval simpl in radl_i2f 2.
  Definition radl_STALE := Eval simpl in radl_i2f 3.
  Definition radl_OPERATIONAL_1 := Eval simpl in radl_i2f 4.
  Definition radl_OPERATIONAL_2 := Eval simpl in radl_i2f 8.

  Definition radl_FAILURE_FLAGS := Eval simpl in Word.wneg radl_OPERATIONAL_FLAGS.

  Definition radl_TIMEOUT_VALUE := Eval simpl in radl_i2f 16.
  Definition radl_TIMEOUT_MBOX := Eval simpl in radl_i2f 32.
  Definition radl_TIMEOUT := Eval simpl in radl_i2f 48.
  
  Definition radl_FAILURE_1 := Eval simpl in radl_i2f 64.
  Definition radl_FAILURE_2 := Eval simpl in radl_i2f 128.

  Definition radl_is_stale (f : Memory.W) :=
    Word.weqb (Word.wand f radl_STALE) radl_STALE.

  Definition radl_is_value_stale (f : Memory.W) :=
    Word.weqb (Word.wand f radl_STALE_VALUE) radl_STALE_VALUE.
  Definition radl_is_mbox_stale (f : Memory.W) :=
    Word.weqb (Word.wand f radl_STALE_MBOX) radl_STALE_MBOX.
  Definition radl_is_failing (f : Memory.W) :=
    Word.weqb (Word.wand f radl_FAILURE_FLAGS) radl_FAILURE_FLAGS.         
  Definition radl_is_timeout (f : Memory.W) :=
    Word.weqb (Word.wand f radl_TIMEOUT) radl_TIMEOUT.
          
  Definition radl_is_value_timeout (f : Memory.W) :=
    Word.weqb (Word.wand f radl_TIMEOUT_VALUE) radl_TIMEOUT_VALUE.
  Definition radl_is_mbox_timeout (f : Memory.W) :=
    Word.weqb (Word.wand f radl_TIMEOUT_MBOX) radl_TIMEOUT_MBOX.
  
End Flags.
