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
        Fiat.Fiat4Monitors.LandsharkNodes.



Require Import Bedrock.Platform.Facade.DFacade
        Bedrock.Platform.Facade.Notations
        Bedrock.Platform.Cito.ADT
        Bedrock.Platform.Cito.RepInv
        Bedrock.Platform.AutoSep.

Section HealthMonitors.
  (* An example specification of the health monitor. *)

  Definition Get_base_report_Spec : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_GetSpec health_monitor unit ````landshark_base_report id (fun tup => Tuple.GetAttribute tup ``"flag").

  Definition Get_paintball_report_Spec : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_GetSpec health_monitor unit ````landshark_paintball_report
                       id (fun tup => Tuple.GetAttribute tup ``"flag").

  Definition Get_turret_report_Spec  : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_GetSpec health_monitor unit ````landshark_turret_report
                       id (fun tup => Tuple.GetAttribute tup ``"flag").

  Definition Get_ocu_teleop_report_Spec  : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_GetSpec health_monitor unit ````ocu_teleop_report
                       id (fun tup => Tuple.GetAttribute tup ``"flag").

  Definition Get_base_flag_report_Spec  : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_Flags_GetSpec health_monitor unit ````landshark_base_report id id.

  Definition Get_paintball_flag_report_Spec  : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_Flags_GetSpec health_monitor unit ````landshark_paintball_report id id.

  Definition Get_turret_flag_report_Spec  : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_Flags_GetSpec health_monitor unit ````landshark_turret_report id id.

  Definition Get_ocu_teleop_flag_report_Spec  : AxiomaticSpec (RADL_Node_ADTValues health_monitor unit) :=
    Message_In_Flags_GetSpec health_monitor unit ````ocu_teleop_report id id.

  Import Bedrock.Platform.Facade.Notations.OpenScopes.



  Definition health_monitor :=
    module
    import {
        "ADT"!"Get_base_report" ====> Get_base_report_Spec;
        "ADT"!"Get_paintball_report" ====> Get_paintball_report_Spec;
        "ADT"!"Get_turret_report" ====> Get_turret_report_Spec;
        "ADT"!"Get_ocu_teleop_repor" ====> Get_ocu_teleop_report_Spec;
        "ADT"!"Get_base_flag_report" ====> Get_base_flag_report_Spec;
        "ADT"!"Get_paintball_flag_repor" ====> Get_paintball_flag_report_Spec;
        "ADT"!"Get_turret_flag_repor" ====> Get_turret_flag_report_Spec;
        "ADT"!"Get_ocu_teleop_flag_report" ====> Get_ocu_teleop_flag_report_Spec
      }
    define {
      def "step" = func("node", "in", "in_flags", "out", "out_flags") {
        "base_report" <-- call_ "ADT"!"Get_base_report"("in");
        "base_report_flag" <-- call_ "ADT"!"Get_base_flag_report"("in");
        "paintball_report" <-- call_ "ADT"!"Get_paintball_report"("in");
        "paintball_report_flag" <-- call_ "ADT"!"Get_paintball_flag_report"("in");
        "turret_report" <-- call_ "ADT"!"Get_turret_report"("in");
        "turret_report_flag" <-- call_ "ADT"!"Get_turret_flag_report"("in");
        "ocu_teleop_report" <-- call_ "ADT"!"Get_teleop_report"("in");
        "ocu_teleop_report_flag" <-- call_ "ADT"!"Get_teleop_flag_report"("in");
        if_ ("in" < 10) {
              if_ ("in" < 20) {
                    "ret" <~ 0
                  }
                  { "ret" <~ 0 } }
            { "ret" <~0 }
    } }.

Require Import Bedrock.Platform.Facade.CompileUnit2.

Definition paintball_monitor_exports :=
  StringMap.StringMap.add "step"  Monitor_Step_Spec (StringMap.StringMap.empty _).

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
