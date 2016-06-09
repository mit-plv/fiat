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
        Fiat.Examples.HACMSDemo.WheelSensor
        Fiat.Examples.HACMSDemo.WheelSensorDecoder
        Fiat.Examples.HACMSDemo.WheelSensorEncoder.

Require Import Bedrock.Word.

Require Import Coq.extraction.ExtrOcamlBasic Coq.extraction.ExtrOcamlNatInt Coq.extraction.ExtrOcamlZInt Coq.extraction.ExtrOcamlString.

Extract Inductive bool => bool [ true false ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inlined Constant negb => not.
Extract Inlined Constant List.length => "List.length".
Extract Inlined Constant app => "( @ )".
Extract Constant word_as_OT.eq_dec  => "(=)".
Extract Constant word_as_OT.compare => "fun a b -> let comp = compare a b in
                                          if comp = 0 then EQ else if comp < 0 then LT else GT".

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive reflect            => bool [ true false ].
Extract Inlined Constant iff_reflect => "".
Extract Inductive prod => "(*)"  [ "(,)" ].

Open Scope string_scope.
Definition InitS := "Init".
Definition  AddSpeedSubscriberS := "AddSpeedSubscriber".
Definition  AddTirePressureSubscriberS := "AddTirePressureSubscriber".
Definition  PublishSpeedS := "PublishSpeed".
Definition  PublishTirePressureS := "PublishTirePressure".

Arguments WheelSensorImpl /.
Arguments callcADTConstructor / .
Arguments ComputationalADT.cConstructors / .
Arguments ComputationalADT.pcConstructors / .
Arguments callcADTMethod / .
Arguments ComputationalADT.cMethods / .
Arguments ComputationalADT.pcMethods / .

Definition InitSensor : ComputationalADT.cRep WheelSensorImpl :=
  Eval simpl in (CallConstructor WheelSensorImpl InitS).

Definition AddSpeedSubscriber
           (addr : IPAddress)
           (r : ComputationalADT.cRep WheelSensorImpl)
  : ComputationalADT.cRep WheelSensorImpl * bool :=
  Eval simpl in CallMethod WheelSensorImpl AddSpeedSubscriberS r addr.

Definition AddTirePressureSubscriber
           (addr : IPAddress)
           (r : ComputationalADT.cRep WheelSensorImpl)
  : ComputationalADT.cRep WheelSensorImpl * bool :=
  Eval simpl in CallMethod WheelSensorImpl AddTirePressureSubscriberS r addr.

Definition PublishSpeed
           (val : nat)
           (r : ComputationalADT.cRep WheelSensorImpl)
  : ComputationalADT.cRep WheelSensorImpl * (list (IPAddress * bin))  :=
  Eval simpl in CallMethod WheelSensorImpl PublishSpeedS r val.

Definition PublishTirePressure
           (val : nat)
           (r : ComputationalADT.cRep WheelSensorImpl)
  : ComputationalADT.cRep WheelSensorImpl * (list (IPAddress * bin))  :=
  Eval simpl in CallMethod WheelSensorImpl PublishTirePressureS r val.

Definition DecodeMessage (b : bin) : option SensorType :=
  Eval simpl in (match (fst packet_decoder b Empty)
                 with
                 | Some v => Some (fst (fst v))
                 | _ => None
                 end).

Extraction "wheelSensorEncoder.ml" InitSensor PublishTirePressure PublishSpeed AddTirePressureSubscriber AddSpeedSubscriber.

(* Initialize the subscriber database with some random values.*)
Definition LoadUpSubscribers :=
  let r := InitSensor in
  let (r, _) := AddSpeedSubscriber (WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~1) r in
  let (r, _) := AddTirePressureSubscriber (WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~0~0~0~0~0~0~0~1~0~0~0~0~0~0~0~1) r in
  let (r, _) := AddSpeedSubscriber (WO~1~1~0~1~0~0~0~0~0~0~0~0~1~0~1~1~0~0~0~0~0~0~0~1~0~0~1~0~0~0~0~1) r in
    let (r, _) := AddSpeedSubscriber (WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~0~0~1~0~1~0~0~1~0~0~0~1~1~0~0~1) r in
  let (r, _) := AddTirePressureSubscriber (WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~0~0~0~0~1~0~1~1~1~1~1~0~1) r in
  let (r, _) := AddSpeedSubscriber (WO~1~1~0~1~0~0~0~1~1~1~0~0~1~0~1~1~0~0~0~0~0~1~0~1~0~0~1~0~0~0~0~1) r in r.

(* We can call the ADT's methods to publish data: *)
Eval vm_compute in (map snd (snd (PublishTirePressure 105 LoadUpSubscribers))).
Eval vm_compute in (map snd (snd (PublishSpeed 256 LoadUpSubscribers))).

(* Using our synthesized decoder maps the encoded *)
(* data to the original values. (Note that the data is tagged). *)
Eval vm_compute in (map (fun v => (fst v, DecodeMessage (snd v))) (snd (PublishTirePressure 105 LoadUpSubscribers))).
Eval vm_compute in (map (fun v => (fst v, DecodeMessage (snd v))) (snd (PublishSpeed 47 LoadUpSubscribers))).

(* If we try to add an existing subscriber, the database is unchanged. *)
Goal (fst (AddSpeedSubscriber (WO~1~1~0~1~0~0~0~1~1~1~0~0~1~0~1~1~0~0~0~0~0~1~0~1~0~0~1~0~0~0~0~1) LoadUpSubscribers) = LoadUpSubscribers /\
      snd (AddSpeedSubscriber (WO~1~1~0~1~0~0~0~1~1~1~0~0~1~0~1~1~0~0~0~0~0~1~0~1~0~0~1~0~0~0~0~1) LoadUpSubscribers) = false).
  split.
  vm_compute; reflexivity.
  vm_compute; reflexivity.
Qed.
