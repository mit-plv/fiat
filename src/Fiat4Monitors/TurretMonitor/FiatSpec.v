Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Coq.Arith.Arith.
Require Import
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags
        Fiat.Fiat4Monitors.RADL_Nodes
        Fiat.Fiat4Monitors.RADLNodeADTs
        Fiat.Fiat4Monitors.LandsharkTopics
        Fiat.Fiat4Monitors.LandsharkNodes
        Fiat.Fiat4Monitors.RADL_Notations.

Open Scope Node_scope.
Definition PaintballMonitorNode :=
  monitor node for landshark_paintball using Landshark_Topics {
      MODELED unit
      PUBLISHES []
      SUBSCRIBES [turret_pan; turret_tilt] }.

Definition LandsharkTopicNames := Eval simpl in Vector.map Topic_Name Landshark_Topics.
Definition LandsharkTopicTypes := Eval simpl in Vector.map Topic_Type Landshark_Topics.

Definition PaintballMonitorSpec : RADLM_ADT Landshark_Topics PaintballMonitorNode unit :=
  let _ := {| NetworkTopicNames := Vector.map Topic_Name Landshark_Topics |} in
  let _ := {| NetworkTopicTypes := Vector.map Topic_Type Landshark_Topics |} in
  ADTRep unit
    { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
      Def Method RADL_Start_Step (r : rep, msg : RADLM_start_msg_t _ _ PaintballMonitorNode) : _ :=
        msg' <- { msg' |
                  (Word.wordToNat (GetMessageTopicS (radlm_monitor_in msg) turret_tilt "data") < 45
                   -> msg' = (UpdateMessageTopicS (radlm_in msg) trigger "data" O_8, radlm_in_flags msg))
                  /\ (~ (Word.wordToNat (GetMessageTopicS (radlm_monitor_in msg) turret_tilt "data") < 45) -> msg' = (radlm_in msg, radlm_in_flags msg)) };
      ret (r, msg'),
      Def Method RADL_Finish_Step (r : rep, msg : _) : _ := ret (r, (radlm_out msg, radlm_out_flags msg, ConstructMessage _ _ [] (ilist2.inil2)))}.

Definition PaintballMonitorImpl :
  FullySharpened PaintballMonitorSpec.
Proof.
  start sharpening ADT.
  { unfold PaintballMonitorSpec; fold LandsharkTopicTypes; fold LandsharkTopicNames; simpl.
    repeat match goal with
             |- context [Vector.cons ?A ?a ?n ?V] =>
             let H := fresh "V" in
             set (H := Vector.cons A a n V) in *
           end.
    fold LandsharkTopicTypes in V.
    assert (V = LandsharkTopicTypes) by reflexivity.
    subst.
    rewrite H.
    hone method RADL_Start_Step.
    { simpl in *.
      etransitivity.
      rewrite refine_pick_decides_branches; [ reflexivity | intros | intros ].
      apply refineEquiv_pick_eq.
      apply refineEquiv_pick_eq.
      refine pick val
             (if (lt_dec (Word.wordToNat
                            (prim_fst
                               (GetTopic' V V3 (radlm_monitor_in n)
                                          (Fin.FS Fin.F1)))) 45) then Datatypes.true else Datatypes.false).
      simplify with monad laws.
      rewrite refine_If_Then_Else_Bind.
      rewrite !refineEquiv_bind_unit.
      higher_order_reflexivity.
      find_if_inside; simpl; eauto.
    }
    FullySharpenEachMethodWithoutDelegation.
  }
  simpl.
  instantiate (1 := fun idx : Fin.t 0 => Vector.nth (Vector.nil _) idx).
  instantiate (2 := fun idx : Fin.t 0 => Vector.nth (Vector.nil Type) idx).
  eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type.
  econstructor.
  simpl; apply reflexivityT.
Defined.

Definition PaintballMonitorImpl' := Eval simpl in projT1 PaintballMonitorImpl.
