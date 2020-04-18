Require Import Coq.Lists.List Coq.Program.Program Coq.Arith.Arith.
Require Import Fiat.Fiat4Monitors.RADL_Definitions
        Fiat.Fiat4Monitors.TurretMonitorSpec
        Fiat.Fiat4Monitors.MonitorADTs
        Fiat.Fiat4Monitors.MonitorRepInv
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements.
Require Import Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Facade.Notations.
Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Definition GetTiltXSpec :=
  Message_Monitor_In_SetSpec (PaintballMonitorSpec (fun _ => true)
                                                   (fun _ => true))
                                                   ````"TiltX" id id.
Definition GetTiltYSpec :=
  Message_Monitor_In_SetSpec (PaintballMonitorSpec (fun _ => true)
                                                   (fun _ => true))
                             ````"TiltY" id id.
Definition Monitored_Node_StepSpec :=
  RADL_Monitored_Node_StepSpec (PaintballMonitorSpec (fun _ => true)
                                                     (fun _ => true)).
Definition Monitor_Init_Spec := 
  MonitorNode_InitSpec (PaintballMonitorSpec (fun _ => true)
                                             (fun _ => true)).
Definition Monitor_Step_Spec := 
  MonitorNode_StepSpec (PaintballMonitorSpec (fun _ => true)
                                             (fun _ => true)).

  Import Bedrock.Platform.Facade.Notations.OpenScopes.

Definition paintball_monitor :=
  module
  import {
      "ADT"!"GetTiltX" ====> GetTiltXSpec;
      "ADT"!"GetTiltY" ====> GetTiltYSpec;
      "ADT"!"Node_Step" ====> Monitored_Node_StepSpec
    }
    define {
      def "init" = func() {"ret" <-- call_ "ADT"!"BuildUnit" () };
      
      def "step" = func("node", "in", "out", "monitor_in", "monitor_out") {
        "tilt_x" <-- call_ "ADT"!"GetTiltX"("monitor_in");
        "tilt_y" <-- call_ "ADT"!"GetTiltY"("monitor_in");
        if_ ("tilt_x" < 10) {
              if_ ("tilt_y" < 20) {
                    "ret" <-- call_ "ADT"!"Node_Step" ("node", "in", "out")
                  }
                  { "ret" <-- call_ "ADT"!"Node_Step" ("node", "in", "out") } }
            { "ret" <-- call_ "ADT"!"Node_Step" ("node", "in", "out") }
            } }.
Require Import Bedrock.Platform.Facade.CompileUnit2.

Definition paintball_monitor_exports :=
  StringMap.StringMap.add "init"  Monitor_Init_Spec
                          (StringMap.StringMap.add "step"  Monitor_Step_Spec (StringMap.StringMap.empty _)).

Definition paintball_monitor_module
: CompileUnit paintball_monitor_exports.
  eapply (@Build_CompileUnit _ paintball_monitor_exports (paintball_monitor eq_refl) "paintball_monitor_ax" "paintball_monitor"); eauto.
Defined.

Require Import Bedrock.Platform.Facade.CompileDFModule.
Require Import Bedrock.Platform.Facade.DFacadeToBedrock2.

Module Import M := DFacadeToBedrock2.Make MonitorADTs.Adt MonitorRepInv.Ri .

Definition output := compile paintball_monitor_module.
Definition m1 := CompileOut2.bedrock_module output.
Definition m1_ok := CompileOut2.bedrock_module_ok output.
Definition m2 := CompileOut2.bedrock_module_impl output.
Definition m2_ok := CompileOut2.bedrock_module_impl_ok output.
Definition all1 := link m1 m2.

(* I don't have enough memory to test this linking :( *)
Lemma all1_ok : moduleOk all1.
    link m1_ok m2_ok.
Qed.

