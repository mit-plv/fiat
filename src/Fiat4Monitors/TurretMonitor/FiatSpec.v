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

Definition PaintballMonitorNode :=
  monitor node for landshark_paintball using Landshark_Topics {
      PUBLISHES []
      SUBSCRIBES [turret_pan; turret_tilt] }%Node.

Definition LandsharkTopicNames := Eval simpl in Vector.map Topic_Name Landshark_Topics.
Definition LandsharkTopicTypes := Eval simpl in Vector.map Topic_Type Landshark_Topics.

Definition PaintballMonitorSpec : RADLM_ADT Landshark_Topics PaintballMonitorNode unit :=
  let _ := {| NetworkTopicNames := LandsharkTopicNames |} in
  let _ := {| NetworkTopicTypes := LandsharkTopicTypes |} in
  ADTRep unit
    { Def Constructor RADL_Init (_ : unit) : rep := ret tt,
      Def Method RADL_Start_Step (r : rep, msg : RADLM_start_msg_t NetworkTopicTypes NetworkTopicNames PaintballMonitorNode) : _ :=
        msg' <- { msg' |
                  IF Word.wlt (GetMessageTopicS (radlm_monitor_in msg) turret_tilt "data") (Word.natToWord _ 45)
                   then msg' = (UpdateMessageTopicS (radlm_in msg) trigger "data" O_8, radlm_in_flags msg)
                   else msg' = (radlm_in msg, radlm_in_flags msg) };
      ret (r, msg'),
      Def Method RADL_Finish_Step (r : rep, msg : RADLM_finish_msg_t NetworkTopicTypes NetworkTopicNames PaintballMonitorNode) : _ := ret (r, (radlm_out msg, radlm_out_flags msg, ConstructMessage NetworkTopicTypes NetworkTopicNames (Vector.nil _) (ilist2.inil2)))}.

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
    hone method RADL_Start_Step.
    { simpl in *.
      etransitivity.
      rewrite refine_pick_decides_branches; [ reflexivity | intros | intros ].
      apply refineEquiv_pick_eq.
      apply refineEquiv_pick_eq.
      refine pick val
             (if (Word.wlt_dec
                            (prim_fst
                               (GetTopic' _ _ (radlm_monitor_in n)
                                          (Fin.FS Fin.F1))) (Word.natToWord _ 45)) then Datatypes.true else Datatypes.false).
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
