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
        Fiat.Fiat4Monitors.RADL_Notations.

Section Topics.
  (* All the landshark topics from topics.v . *)

  Open Scope Struct_scope.
  Open Scope Topic_scope.

  (* BEN: I can't find the definition of this struct. *)
  Definition start_time := float64.
  (* BEN: Or this type. What is time anyways :)? *)
  Definition time := uint8.

  Definition m__vector3 :=
    struct { FIELDS "x" `: float64 `:= O_64;
             "y" `: float64 `:= O_64;
             "z" `: float64 `:= O_64}.

  Definition t__base := topic { FIELDS
                                  "stamp" `: start_time `:= O_64;
                                ("linear" = m__vector3) } .

  Definition t__teleop_base := t__base.

  Definition t__teleop_over_ride := topic { FIELDS "data" `: bool `:= false }.
  Definition t__teleop_estop := topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__teleop_deadman := topic { FIELDS "data" `: bool `:= false }.
  Definition t__teleop_turret_pan := topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__teleop_turret_tilt := topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__teleop_moog_pan := topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__teleop_moog_tilt := topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__teleop_moog_zoom := topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__teleop_paintball_trigger := topic { FIELDS "data" `: uint8 `:= O_8 }.

  (* Base Topics *)
  Definition t__base_wheel_encoder :=
    topic { FIELDS
              "stamp" `: start_time `:= O_64;
            "left" `: int64 `:= O_64;
            "right" `: int64 `:= O_64
          }.
  Definition t__base_battery_status :=
    topic { FIELDS "data" `: float32 `:= O_32 }.

  Definition t__base_status :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.

  Definition t__base_actuator_input :=
    topic { FIELDS
              "stamp" `: start_time `:= O_64;
            "left" `: float64 `:= O_64;
            "right" `: float64 `:= O_64}.

  (* fsm topics *)
  Definition t__fsm_ccc_request :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__fsm_pp_request :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__estop :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__controller_select :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__controller_status :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.

  (* ccc topics*)
  Definition t__ccc_status :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__ccc_base := t__base.
  Definition t__ccc_speed :=
    topic { FIELDS "data" `: float32 `:= O_32 }.

  (* # pp topics *)
  Definition t__pp_status :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.
  Definition t__pp_base := t__base.

  (*# monitor topics *)
  Definition t__monitor_estop :=
    topic { FIELDS "data" `: uint8 `:= O_8 }.

  (*# gps topics *)
  (* BEN: Punting on this until I define arrays
t__gps_navsatfix : topic { FIELDS
  stamp = radl.start_time
  latitude: float64 0
  longitude: float64 0
  altitude: float64 0
  position_covariance = arrays.zeros_9_float64
  position_covariance_type: uint8 0
  status: struct { FIELDS
    status: int8 0
    service: uint16 0
  }
} *)

  Definition t__gps_velocity :=
    topic { FIELDS
              "stamp" `: start_time `:= O_64;
            "linear" = struct { FIELDS "x" `: float64 `:= O_64;
                                "y" `: float64 `:= O_64;
                                "z" `: float64 `:= O_64 };
            "angular" = struct { FIELDS "x" `: float64 `:= O_64;
                                 "y" `: float64 `:= O_64;
                                 "z" `: float64 `:= O_64 } }.

  Definition t__gps_timeref :=
    topic { FIELDS
              "stamp" `: start_time `:= O_64;
            "time_ref" `: time `:= O_8
          }.

  (* # imu topics *)
  (* BEN: Punting on imu until I define arrays.
t__imu_front_imu : topic { FIELDS
  stamp = radl.start_time
  orientation: struct { FIELDS x: float64 0  y: float64 0 z: float64 0 w: float64 0 }
  orientation_covariance = arrays.zeros_9_float64
  angular_velocity: struct { FIELDS x: float64 0  y: float64 0 z: float64 0 }
  angular_velocity_covariance = arrays.zeros_9_float64
  linear_acceleration: struct { FIELDS x: float64 0  y: float64 0 z: float64 0 }
  linear_acceleration_covariance = arrays.zeros_9_float64
}

t__imu_front_magnetometer : topic { FIELDS
  stamp = radl.start_time
  vector: struct { FIELDS x: float64 0  y: float64 0 z: float64 0 }
}

t__imu_rear_imu = t__imu_front_imu
t__imu_rear_magnetometer = t__imu_front_magnetometer
   *)

  (*# turret *)
  Definition t__turret_status_pan :=
    topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__turret_status_tilt :=
    topic { FIELDS "data" `: float64 `:= O_64 }.

  (*# moog *)
  Definition t__moog_status_pan :=
    topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__moog_status_tilt :=
    topic { FIELDS "data" `: float64 `:= O_64 }.
  Definition t__moog_status_zoom :=
    topic { FIELDS "data" `: float64 `:= O_64 }.


  (*# laser *)
  (* BEN: Punting again because of arrays
t__laser_scan_front : topic { FIELDS
  stamp = radl.start_time
  angle_min: float32 0
  angle_max: float32 0
  angle_increment: float32 0
  time_increment: float32 0
  scan_time: float32 0
  range_min: float32 0
  range_max: float32 0
  ranges = arrays.hokuyo_range_array
  intensities = arrays.hokuyo_range_array
}

t__laser_scan_rear = t__laser_scan_front



# This is an array of 16 points
t__map : topic { FIELDS
  data: bool false
  points = arrays.map_points
}

# This is the goal for the object in GPS coordinates
t__goal : topic { FIELDS
  latitude: float32 0
  longitude: float32 0
  altitude: float32 0
}*)

  (* Topics for health monitoring *)
  Definition t__landshark_fsm_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_base_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_gps_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_imu_front_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_imu_rear_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_paintball_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_turret_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_moog_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_hokuyo_front_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_hokuyo_rear_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_ccc_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__landshark_pp_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  Definition t__ocu_teleop_health :=
    topic { FIELDS "flag" `: float32 `:= O_32 }.

  (* Partial listing of the available topics. *)
  Open Scope string_scope.

  Definition battery := "battery".
  Definition encoder := "encoder".
  Definition actuator := "actuator".
  Definition status := "status".
  Definition landshark_base_report := "landshark_base_report".

  (* telop topics *)
  Definition base := "base".
  Definition estop := "estop".
  Definition over_ride := "over_ride".
  Definition turret_pan := "turret_pan".
  Definition turret_tilt := "turret_tilt".
  Definition moog_pan := "moog_pan".
  Definition moog_tilt := "moog_tilt".
  Definition moog_zoom := "moog_zoom".
  Definition trigger := "trigger".
  Definition ocu_teleop_report := "ocu_teleop_report".
  Definition landshark_paintball_report := "landshark_paintball_report".

  (* paintball topics *)
  Definition status_pan := "status_pan".
  Definition status_tilt := "status_tilt".
  Definition landshark_turret_report := "landshark_turret_report".

      (* two moog topics to which paintball subscribes *)
  Definition pan := "pan".
  Definition tilt := "tilt".

  Import Vectors.VectorDef.VectorNotations.

  Definition Landshark_Topics :=
    [ (* base topics *)
      battery { TOPIC t__base_battery_status };
      encoder { TOPIC t__base_wheel_encoder };
      actuator { TOPIC t__base_actuator_input };
      status { TOPIC t__base_status };
      landshark_base_report { TOPIC t__landshark_base_health (* PERIOD 1sec *) };

      (* telop topics *)
      base { TOPIC t__teleop_base };
      estop { TOPIC t__teleop_estop };
      over_ride { TOPIC t__teleop_over_ride };
      turret_pan { TOPIC t__teleop_turret_pan };
      turret_tilt { TOPIC t__teleop_turret_tilt };
      moog_pan { TOPIC t__teleop_moog_pan };
      moog_tilt { TOPIC t__teleop_moog_tilt };
      moog_zoom { TOPIC t__teleop_moog_zoom };
      trigger { TOPIC t__teleop_paintball_trigger };
      ocu_teleop_report { TOPIC t__ocu_teleop_health (*MAXLATENCY 100msec *) };

      (* turret topics *)
      landshark_paintball_report { TOPIC t__landshark_paintball_health (*PERIOD 1sec *)};

      (* paintball topics *)
      status_pan { TOPIC t__turret_status_pan };
      status_tilt { TOPIC t__turret_status_tilt };
      landshark_turret_report { TOPIC t__landshark_turret_health (* PERIOD 1sec *)};

      (* two moog topics to which paintball subscribes *)
      pan { TOPIC t__teleop_moog_pan (*MAXLATENCY 10msec*)};
      tilt { TOPIC t__teleop_moog_tilt (*MAXLATENCY 10msec*)}
    ]%vector.

End Topics.
