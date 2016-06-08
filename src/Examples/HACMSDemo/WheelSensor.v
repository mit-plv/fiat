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
        Fiat.Examples.HACMSDemo.HACMSDemo.

Require Import
        Bedrock.Word
        Bedrock.Memory.

Import Coq.Vectors.Vector
       Coq.Strings.Ascii
       Coq.Bool.Bool
       Coq.Bool.Bvector
       Coq.Lists.List.

Open Scope vector.
(* The two sensors on our wheel. *)
Definition SensorIDs := ["Speed"; "TirePressure"].
Definition SensorID := BoundedString SensorIDs.

(* The data types for the two sensors. *)
Definition SensorTypes := [nat : Type; nat : Type].
Definition SensorType := SumType SensorTypes.

Definition IPAddress := word 32.

Definition SensorTypeCode : Vector.t (word 4) 2
  := [ natToWord 4 3; natToWord 4 0].

Lemma IPAddress_decideable
  : forall (addr addr' : IPAddress),
    (addr = addr') \/ (addr <> addr').
Proof.
  intros; destruct (weq addr addr'); intuition.
Qed.

Lemma SensorID_decideable
  : forall (id1 id2 : SensorID),
    (id1 = id2) \/ (id1 <> id2).
Proof.
  intros; destruct (BoundedIndex_eq_dec id1 id2); intuition.
Qed.

Hint Resolve IPAddress_decideable.
Hint Resolve SensorID_decideable.

Variable cache : Cache.
Variable cacheAddNat : CacheAdd cache nat.
Definition transformer : Transformer bin := btransformer.
Variable transformerUnit : TransformerUnitOpt transformer bool.
Variable Empty : CacheEncode.

Definition encode_SensorData_Spec (val : SensorType) :=
       encode_enum_Spec SensorTypeCode {| bindex := SensorIDs[@SumType_index _ val];
                                          indexb := {| ibound := SumType_index _ val;
                                                       boundi := @eq_refl _ _ |} |}
  Then encode_SumType_Spec (B := bin) (cache := cache) SensorTypes
  (icons (encode_nat_Spec 8) (* Wheel Speed *)
  (icons (encode_nat_Spec 8) (* Tire Pressure *)
         inil)) val
  Done.

Definition encode_SensorData_Impl (val : SensorType) ce :=
  let (bin', ce') := encode_enum_Impl SensorTypeCode {| bindex := SensorIDs[@SumType_index _ val];
                                                        indexb := {| ibound := SumType_index _ val;
                                                                     boundi := @eq_refl _ _ |} |} ce in
  let (bin'', ce'') := (encode_SumType_Impl (B := bin) (cache := cache) SensorTypes
                (icons (encode_nat_Impl 8) (* Wheel Speed *)
                       (icons (encode_nat_Impl 8) (* Tire Pressure *)
                              inil)) val ce') in
  (app bin' bin'', ce'').

Lemma refine_encode_SensorData_Impl
  : forall ce (val : SensorType),
    refine (encode_SensorData_Spec val ce)
           (ret (encode_SensorData_Impl val ce)).
Proof.
  intros.
  unfold encode_SensorData_Spec, encode_SensorData_Impl.
  unfold compose, Bind2.
  setoid_rewrite refine_encode_enum; simplify with monad laws.
  rewrite (@refine_encode_SumType
          bin
          _
          2
          ([nat : Type; nat : Type])
          _
          (icons (B := (fun T : Type =>
                          T -> @CacheEncode cache -> bin * @CacheEncode cache)) (encode_nat_Impl 8)
                 (icons (B := (fun T : Type =>
                                 T -> @CacheEncode cache -> bin * @CacheEncode cache))
                        (encode_nat_Impl 8) (inil (A := Type))))).
  simplify with monad laws.
  simpl; rewrite app_nil_r.
  unfold SensorTypes.
  destruct (encode_SumType_Impl [nat : Type; nat : Type]
                                (icons (encode_nat_Impl 8) (icons (encode_nat_Impl 8) inil)) val
                                (addE ce 4)).
  simpl; f_equiv.
  simpl; repeat apply Build_prim_and; eauto;
    intros; eapply refine_encode_nat.
Qed.

Opaque encode_SensorData_Spec.

(* The 'schema' (in the SQL sense) of our database of subscribers. *)
Definition WheelSensorSchema :=
  Query Structure Schema
    [ relation "subscribers" has
               schema <"topic" :: SensorID, "address" :: IPAddress>
      where DuplicateFree
    ] enforcing [ ].

(* Aliases for the subscriber tuples. *)
Definition Subscriber := TupleDef WheelSensorSchema "subscribers".

(* Our sensor has two mutators:
   - [AddSpeedSubscriber] : Add a subscriber to the speed topic
   - [AddTirePressureSubscriber] : Add a subscriber to the tire pressure topic

   Our sensor has two observers:
   - [PublishSpeed] : Builds a list of encoded speed data to send out on the wire
   - [PublishTirePressure] : Builds a list of encoded tire pressure data to send out on the wire
 *)

(* So, first let's give the type signatures of the methods. *)
Definition WheelSensorSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : rep,
      Method "AddSpeedSubscriber" : rep * IPAddress -> rep * bool,
      Method "AddTirePressureSubscriber" : rep * IPAddress -> rep * bool,
      Method "PublishSpeed" : rep * nat -> rep * (list (IPAddress * bin)),
      Method "PublishTirePressure" : rep * nat -> rep * (list (IPAddress * bin))
    }.

(* Now we write what the methods should actually do. *)

Local Notation "Bnd [@ idx ]" :=
  (ibound (indexb (@Build_BoundedIndex _ _ Bnd idx _))).

Definition WheelSensorSpec : ADT WheelSensorSig :=
  Eval simpl in
    Def ADT {
      rep := QueryStructure WheelSensorSchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "AddSpeedSubscriber" (r : rep) (addr : IPAddress) : rep * bool :=
        Insert <"topic" :: ``"Speed", "address" :: addr> into r!"subscribers",

    Def Method1 "AddTirePressureSubscriber" (r : rep) (addr : IPAddress) : rep * bool :=
        Insert <"topic" :: ``"TirePressure", "address" :: addr> into r!"subscribers",

    Def Method1 "PublishSpeed" (r : rep) (n : nat) : rep * (list (IPAddress* bin)) :=
          `(msg, _) <- encode_SensorData_Spec (inj_SumType SensorTypes SensorIDs[@"Speed"] n) Empty;
          subs <- For (sub in r!"subscribers")
                  Where (sub!"topic" = ``"Speed")
                  Return (sub!"address", msg);
          ret (r, subs),

    Def Method1 "PublishTirePressure" (r : rep) (n : nat) : rep * (list (IPAddress * bin)) :=
          `(msg, _) <- encode_SensorData_Spec (inj_SumType SensorTypes SensorIDs[@"TirePressure"] n) Empty;
          subs <- For (sub in r!"subscribers")
                  Where (sub!"topic" = ``"TirePressure")
                  Return (sub!"address", msg);
          ret (r, subs)
  }%methDefParsing.


Theorem SharpenedWheelSensor :
    FullySharpened WheelSensorSpec.
Proof.
  start sharpening ADT.
  start_honing_QueryStructure'.
  (* We first insert checks for the DuplicateFree constraints.  *)
  hone method "AddSpeedSubscriber". { dropDuplicateFree. }
  hone method "AddTirePressureSubscriber". { dropDuplicateFree. }
  let AbsR' := constr:(@DecomposeRawQueryStructureSchema_AbsR' 2 WheelSensorSchema ``"subscribers" ``"topic" id (fun i => ibound (indexb i))
                                                (fun val =>
                                                   {| bindex := _;
                                                      indexb := {| ibound := val;
                                                                   boundi := @eq_refl _ _ |} |})) in hone representation using AbsR'.
  {
    simplify with monad laws.
    apply refine_pick_val.
    apply DecomposeRawQueryStructureSchema_empty_AbsR.
  }
  { doAny ltac:(implement_DecomposeRawQueryStructure)
                 rewrite_drill ltac:(finish honing). }
  { doAny ltac:(implement_DecomposeRawQueryStructure)
                 rewrite_drill ltac:(finish honing). }
  { doAny ltac:(implement_DecomposeRawQueryStructure)
                 rewrite_drill ltac:(simpl; finish honing). }
  { doAny ltac:(implement_DecomposeRawQueryStructure)
                 rewrite_drill ltac:(simpl; finish honing). }
  simpl; hone representation using (fun r_o r_n => snd r_o = r_n).
  { simplify with monad laws; apply refine_pick_val; reflexivity. }
  { doAny ltac:(implement_DecomposeRawQueryStructure' H0)
                 ltac:(rewrite_drill; simpl)
                        ltac:(finish honing). }
  { doAny ltac:(implement_DecomposeRawQueryStructure' H0)
                 ltac:(rewrite_drill; simpl)
                        ltac:(finish honing). }
  { doAny ltac:(implement_DecomposeRawQueryStructure' H0)
                 ltac:(rewrite_drill; simpl)
                        ltac:(finish honing). }
  { doAny ltac:(implement_DecomposeRawQueryStructure' H0)
                 ltac:(rewrite_drill; simpl)
                        ltac:(finish honing). }
  unfold DecomposeRawQueryStructureSchema, DecomposeSchema; simpl.
  chooseIndexes.
  initializer.
  insertOne.
  insertOne.
  rewrite refine_encode_SensorData_Impl; planOne.
  rewrite refine_encode_SensorData_Impl; planOne.
  final_optimizations.
  determinize.
  choose_data_structures.
  final_simplification.
  use_this_one.
Defined.

Definition WheelSensorImpl := Eval simpl in projT1 SharpenedWheelSensor.
Print WheelSensorImpl.
