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
        Fiat.Fiat4Monitors.RADL_Notations
        Fiat.Fiat4Monitors.RADLMNodeADTs.

Require Import Fiat.Fiat4Monitors.TurretMonitor.FiatSpec.

Definition Get_turret_tilt_Spec :=
  Monitor_Message_In_Get_Struct_Spec PaintballMonitorSpec ``(ibound (indexb  (@Build_BoundedIndex _ _ LandsharkTopicNames turret_tilt _))) id id.

Definition Get_turret_pan_Spec :=
  Monitor_Message_In_Get_Struct_Spec PaintballMonitorSpec ``(ibound (indexb  (@Build_BoundedIndex _ _ LandsharkTopicNames turret_pan _))) id id.

Definition Paintball_Init_Spec := Monitored_Node_Init_Spec PaintballMonitorSpec.

Definition Paintball_Start_Step_Spec := Monitored_Node_Start_Step_Spec PaintballMonitorSpec.

Definition Paintball_Finish_Step_Spec := Monitored_Node_Finish_Step_Spec PaintballMonitorSpec.

Import Bedrock.Platform.Facade.Notations.OpenScopes.

Definition paintball_monitor :=
  module
  import {
      "ADT"!"Get_turret_tilt" ====> Get_turret_tilt_Spec;
      "ADT"!"Get_turret_pan" ====> Get_turret_pan_Spec
    }
    define {

      def "start_step" = func("node", "in", "in_flags", "monitor_in") {
        "tilt'" <-- call_ "ADT"!"Get_turret_tilt"("monitor_in");
        "tilt" <-- call_ "ADT"!"Get_tilt_data"("tilt'");
        "pan'" <-- call_ "ADT"!"Get_turret_pan"("monitor_in");
        "pan" <-- call_ "ADT"!"Get_tilt_data"("pan'");
        if_ ("tilt_x" < 10) {
              if_ ("tilt_y" < 20) {
                    "ret" <-- call_ "ADT"!"Node_Step" ("node", "in", "out")
                  }
                  { "ret" <-- call_ "ADT"!"Node_Step" ("node", "in", "out") } }
            { "ret" <-- call_ "ADT"!"Node_Step" ("node", "in", "out") }
            } }.
