Set Implicit Arguments.

Require Import Coq.Lists.List Coq.Program.Program.
Require Import Bedrock.Platform.Facade.DFacade.
Require Import Bedrock.Platform.Facade.Notations.
Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

(* From a RADL description, SRI generates structs aggregating
   incoming and outgoing messages for each node. These records are
   used to model those structs as ADTs. *)

(* Incoming messages to paintball node. (Subscribes to the trigger.)  *)
Record radl_in_t :=
  { trigger : Memory.B (* uint8 *) }.

(* Not sure what these flags represent. *)
Record radl_in_flag_t :=
  { radl_flags : Memory.B (* uint8 *) }.

(* Outgoing messages to paintball node. (Doesn't publish anything.)  *)
Record radl_out_t := { }.
Record radl_out_flag_t := { }.

(* Incoming messages to paintball monitor node. (Subscribes to the turret's
   tilt sensor.)  *)
Record monitor_in_t :=
  { tilt : Memory.W  * Memory.W (* float64 *) }.

Record monitor_out_t :=
  {  }.

(* Each of these structs is represented in Facade as a distinct ADT. *)
Inductive PaintballADTValues :=
| RADL_In : radl_in_t -> PaintballADTValues
| RADL_In_Flags : radl_in_flag_t -> PaintballADTValues
| RADL_Out : radl_out_t -> PaintballADTValues
| RADL_Out_Flags : radl_out_flag_t -> PaintballADTValues
| Monitor_In : monitor_in_t -> PaintballADTValues
| Monitor_In_Flags : monitor_in_flag_t -> PaintballADTValues.

Module Adt <: ADT.
  Definition ADTValue := PaintballADTValues.
End Adt.

Ltac crush_types :=
  unfold type_conforming, same_types, same_type; intros;
  repeat match goal with
           | [ H: exists t, _ |- _ ] => destruct H
         end; subst;
  intuition.

(* Specs for getters for our ADTValues. *)
Definition monitor_in_tilt1Spec : AxiomaticSpec PaintballADTValues.
  refine {|
      PreCond args := exists w w', args = [ADT (Monitor_In {| tilt := (w, w') |})];
      PostCond args ret :=
        exists w w', args = [(ADT (Monitor_In {| tilt := (w, w') |}),
                              Some (Monitor_In {| tilt := (w, w') |})) ] /\
                     ret = SCA _ w
    |}; crush_types.
Defined.

Definition monitor_in_tilt2Spec : AxiomaticSpec PaintballADTValues.
  refine {|
    PreCond args := exists w w', args = [ADT (Monitor_In {| tilt := (w, w') |})];
    PostCond args ret :=
      exists w w', args = [(ADT (Monitor_In {| tilt := (w, w') |}),
                            Some (Monitor_In {| tilt := (w, w') |})) ] /\
                   ret = SCA _ w'
  |}; crush_types.
Defined.

Definition radl_in_triggerSpec : AxiomaticSpec PaintballADTValues.
  refine {|
      PreCond args :=
        exists w w',
          args = [ADT (RADL_In {| trigger := w |});
                   ADT (RADL_In_Flags {| radl_flags := w' |});
                   ADT (RADL_Out Build_radl_out_t);
                   ADT (RADL_Out_Flags Build_radl_out_flag_t )];
      PostCond args ret :=
        exists w w', args = [(ADT (RADL_In {| trigger := w |}),
                              Some (RADL_In {| trigger := w |}));
                              (ADT (RADL_In_Flags {| radl_flags := w' |}),
                               Some (RADL_In_Flags {| radl_flags := w |}));
                              (ADT (RADL_Out Build_radl_out_t),
                               Some (RADL_Out Build_radl_out_t));
                              (ADT (RADL_Out_Flags Build_radl_out_flag_t ),
                               Some (RADL_Out_Flags Build_radl_out_flag_t ))

                            ] /\
                     ret = SCA _ w
    |}; crush_types.
Defined.

Definition paintball_monitor_step_spec : AxiomaticSpec PaintballADTValues.
  refine {|
      PreCond args :=
        exists w w' tilt_x tilt_y w'',
          args = [ ADT (RADL_In {| trigger := w |});
                   ADT (RADL_In_Flags {| radl_flags := w' |});
                   ADT (RADL_Out Build_radl_out_t);
                   ADT (RADL_Out_Flags Build_radl_out_flag_t );
                   ADT (Monitor_In {| tilt := (tilt_x, tilt_y) |});
                   ADT (Monitor_In_Flags {| monitor_flags := w'' |}) ];
      PostCond args ret :=
        exists w w', args = [(ADT (RADL_In {| trigger := w |}),
                              Some (RADL_In {| trigger := w |}));
                              (ADT (RADL_In_Flags {| radl_flags := w' |}),
                               Some (RADL_In_Flags {| radl_flags := w |}));
                              (ADT (RADL_Out Build_radl_out_t),
                               Some (RADL_Out Build_radl_out_t));
                              (ADT (RADL_Out_Flags Build_radl_out_flag_t ),
                               Some (RADL_Out_Flags Build_radl_out_flag_t ))

                                     ] /\
                                 ret = SCA _ w
    |}. crush_types.
Defined.

Import Bedrock.Platform.Facade.Notations.OpenScopes.

Definition paintball_monitor :=
  module
  import {
      "ADT"!"RADL_In_Trigger" ==> radl_in_triggerSpec;
      "ADT"!"Monitor_In_Tilt1" ==> monitor_in_tilt1Spec;
      "ADT"!"Monitor_In_Tilt2" ==> monitor_in_tilt2Spec
    }
    define {
      def "step" = func("in", "in_flags", "out", "out_flags", "monitor_in", "monitor_out") {
        "tilt_x" <-- call_ "ADT"!"Monitor_In_Tilt1"("monitor_in");
        "tilt_y" <-- call_ "ADT"!"Monitor_In_Tilt2"("monitor_in");
        if_ ("tilt_x" < 10) {
           if_ ("tilt_y" < 20) {
                 "ret" <-- call_ "ADT"!"RADL_In_Trigger" ("in", "in_flags", "out", "out_flags")
           } { "ret" <- 0 } } { "ret" <- 0 } }
    }.

  Require Import Bedrock.Platform.Facade.CompileDFModule.

  Definition gmodule
    := compile_to_gmodule (paintball_monitor eq_refl) "paintball_monitor" eq_refl.

  (* test executability *)
  Require Import Bedrock.Platform.Cito.GoodModuleDec.
  Require Import Bedrock.Platform.Cito.IsGoodModule.

  Goal is_good_module gmodule = true. Proof. exact eq_refl. Qed.

  Require Import Bedrock.Platform.Facade.CompileUnit2.

  Definition paintball_monitor_exports :
    StringMap.StringMap.t (AxiomaticSpec PaintballADTValues).

    refine (StringMap.StringMap.add "step" _ (StringMap.StringMap.empty _)).
    Print AxiomaticSpec.


  Definition paintball_monitor_compileUnit :
    CompileUnit PaintballADTValues.

End ADTValue.
