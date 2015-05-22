Require Import
        Coq.Strings.String
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Program.Program
        Fiat.ADT
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation
        Fiat.ADTRefinement
        Fiat.ADTRefinement.BuildADTRefinements
        Fiat.Fiat4Monitors.RADL_Topics
        Fiat.Fiat4Monitors.RADL_Messages
        Fiat.Fiat4Monitors.RADL_Flags
        Fiat.Fiat4Monitors.RADL_Nodes
        Fiat.Fiat4Monitors.LandsharkTopics.

Section Nodes.

  (* Five example node definitions. *)
  Import Fiat.Fiat4Monitors.RADL_Notations.
  Open Scope Node_scope.

  Definition landshark_base : RADL_Node :=
    node using Landshark_Topics { DEFS ["serial_number: uint64 64976"]
           PUBLISHES [battery; encoder; actuator; status; landshark_base_report]
           SUBSCRIBES [base; estop]
           PERIOD "global.joystick_base"
           PATH "src/landshark_base"
           CXX { ["LIB"; "usb4_lib"; "PATH"; "src"; "HEADER"; "LandsharkBase.h"; "CLASS"; "LandsharkBase"; "FILENAME"; "LandsharkBase.cpp"; "usdigital.c"; "LIB"; "boostlib"] } }.

  Definition landshark_ocu : RADL_Node :=
    node using Landshark_Topics { DEFS ["XBOX_WIRED: uint8 1";
                  "XBOX_WIRELESS: uint8 2";
                  "device: string '/dev/xbox_wired/js0'";
                  "jstype = XBOX_WIRED";
                  "deadzone: float32 0.20";
                  "heartbeat_timeout: duration 1000msec"]
           PUBLISHES [base; estop; over_ride; turret_pan;
                      turret_tilt; moog_pan; moog_tilt; moog_zoom;
                      trigger; ocu_teleop_report]
           SUBSCRIBES []
           PERIOD "global.joystick_period"
           PATH "src/debug/landshark_teleop_step"
           CXX { ["LIB"; "boostlib"; "PATH"; "src"; "HEADER"; "LandsharkJoystick.h"; "CLASS"; "LandsharkJoystick"; "FILENAME"; "LandsharkJoystick.cpp"] } }.

  Definition landshark_paintball : RADL_Node :=
    node using Landshark_Topics {
        DEFS ["ip_address: string '192.168.15.78'";
               "ip_port: uint16 23"]
        PUBLISHES [landshark_paintball_report]
        SUBSCRIBES [trigger]
        PERIOD "global.trigger_period"
        PATH "src/landshark_paintball"
        CXX { ["PATH"; "src"; "HEADER"; "LandsharkPaintball.h"; "CLASS"; "LandsharkPaintball"; "FILENAME"; "LandsharkPaintball.cpp"; "LIB"; "boostlib"] } }.

  Definition landshark_turret : RADL_Node :=
    node using Landshark_Topics {
        DEFS ["ip_address: string '192.168.15.77'"]
        PUBLISHES [status_pan; status_tilt;
                   landshark_turret_report]
        SUBSCRIBES [pan; tilt]
        PERIOD "global.joint_period"
        PATH "src/landshark_turret"
        CXX { ["PATH"; "src"; "HEADER"; "LandsharkTurret.h"; "CLASS";
              "LandsharkTurret"; "FILENAME"; "LandsharkTurret.cpp";
              "LIB"; "dmclnxlib"; "boostlib"]} }.

  Definition health_monitor : RADL_Node :=
    node using Landshark_Topics {
        DEFS [ ]
        PUBLISHES []
        SUBSCRIBES [landshark_base_report; landshark_paintball_report;
                    landshark_turret_report; ocu_teleop_report]
        PERIOD "1sec"
        PATH "src/health_monitor"
        CXX { ["HEADER"; "HealthMonitor.h"; "CLASS"; "HealthMonitor";
               "FILENAME"; "HealthMonitor.cpp"] } }.

End Nodes.
