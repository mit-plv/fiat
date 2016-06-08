Require Import Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List
        Coq.Structures.OrderedType.

Require Import
        Fiat.BinEncoders.Env.BinLib.Core
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Common.Compose
        Fiat.BinEncoders.Env.Common.ComposeOpt
        Fiat.BinEncoders.Env.Automation.Solver
        Fiat.BinEncoders.Env.Lib2.WordOpt
        Fiat.BinEncoders.Env.Lib2.NatOpt
        Fiat.BinEncoders.Env.Lib2.StringOpt
        Fiat.BinEncoders.Env.Lib2.EnumOpt
        Fiat.BinEncoders.Env.Lib2.FixListOpt
        Fiat.BinEncoders.Env.Lib2.SumTypeOpt.

Require Import
        Fiat.Common.SumType
        Fiat.Examples.Tutorial.Tutorial
        Fiat.Examples.DnsServer.DecomposeEnumField
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.MasterPlan
        Fiat.Examples.HACMSDemo.DuplicateFree
        Fiat.Examples.HACMSDemo.HACMSDemo
        Fiat.Examples.HACMSDemo.WheelSensor.

(* We first synthesize an implementation of our encoder. *)
Lemma Sharpened_encode_SensorData_Impl
  : { encode_SensorData_Impl : _ &
      forall ce (val : SensorType),
        refine (encode_SensorData_Spec val ce)
               (ret (encode_SensorData_Impl val ce))}.
Proof.
  eexists; intros; set_evars.
  unfold encode_SensorData_Spec.
  unfold compose, Bind2.
  setoid_rewrite refine_encode_enum; simplify with monad laws.
  setoid_rewrite (@refine_encode_SumType
          bin
          _
          2
          ([nat : Type; nat : Type])
          _
          (icons _
                 (icons _ (inil (A := Type))))).
  simplify with monad laws.
  simpl; rewrite app_nil_r.
  finish honing.
  simpl; f_equiv.
  simpl; repeat apply Build_prim_and; eauto;
    intros; rewrite refine_encode_nat; finish honing.
Defined.

(* Extract the synthesized encoder. *)
Definition encode_SensorData_Impl :=
  Eval simpl in projT1 Sharpened_encode_SensorData_Impl.

(* Extract its proof of correctness for good measure. *)
Lemma refine_encode_SensorData_Impl
  : forall ce (val : SensorType),
        refine (encode_SensorData_Spec val ce)
               (ret (encode_SensorData_Impl val ce)).
Proof.
  exact (projT2 Sharpened_encode_SensorData_Impl).
Qed.

Opaque encode_SensorData_Spec.

Theorem SharpenedWheelSensor :
    FullySharpened WheelSensorSpec.
Proof.
  start sharpening ADT.
  start_honing_QueryStructure'.
  (* We first insert checks for the DuplicateFree constraints.  *)
  hone method "AddSpeedSubscriber". { dropDuplicateFree. }
  hone method "AddTirePressureSubscriber". { dropDuplicateFree. }
  (* Break down the suscribers 'table' into one for each topic.  *)
  decompose_EnumField "subscribers" "topic".
  (* Select the kinds of searches each 'table' should support. *)
  chooseIndexes.
  (* Implement each method using the chosen search operations. *)
  initializer.
  insertOne.
  insertOne.
  rewrite refine_encode_SensorData_Impl; planOne.
  rewrite refine_encode_SensorData_Impl; planOne.
  (* Cleanup the synthesized methods. *)
  final_optimizations.
  (* Ensure the implementation is executable. *)
  determinize.
  (* Select concrete data structures for each table.  *)
  choose_data_structures.
  (* Some final cleanup. *)
  final_simplification.
  (* And we're done! *)
  use_this_one.
Defined.

(* We can now extract the implementation derived above. *)
Definition WheelSensorImpl := Eval simpl in projT1 SharpenedWheelSensor.
Print WheelSensorImpl.
