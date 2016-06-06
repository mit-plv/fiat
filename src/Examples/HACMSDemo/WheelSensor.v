Require Import Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List.

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
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms.

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

Definition DuplicateFree {heading} (tup1 tup2 : @RawTuple heading) := tup1 <> tup2.
Definition IPAddress := word 32.

Definition SensorTypeCode : Vector.t (word 4) 2
  := [ natToWord 4 3; natToWord 4 0].

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

(* The 'schema' (in the SQL sense) of our database of subscribers. *)
Definition WheelSensorSchema :=
  Query Structure Schema
    [ relation "subscribers" has
               schema <"address" :: IPAddress, "topic" :: SensorID>
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
      Method "PublishSpeed" : rep * nat -> rep * (list bin),
      Method "PublishTirePressure" : rep * nat -> rep * (list bin)
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
        Insert <"address" :: addr, "topic" :: ``"Speed"> into r!"subscribers",

    Def Method1 "AddTirePressureSubscriber" (r : rep) (addr : IPAddress) : rep * bool :=
        Insert <"address" :: addr, "topic" :: ``"TirePressure"> into r!"subscribers",

    Def Method1 "PublishSpeed" (r : rep) (n : nat) : rep * (list bin) :=
          subs <- For (sub in r!"subscribers")
                    Where (sub!"topic" = ``"Speed")
                    (l <- encode_SensorData_Spec (inj_SumType SensorTypes SensorIDs[@"Speed"] n) Empty;
                     Return (fst l));
          ret (r, subs),

    Def Method1 "PublishTirePressure" (r : rep) (n : nat) : rep * (list bin) :=
          subs <- For (sub in r!"subscribers")
                    Where (sub!"topic" = ``"TirePressure")
                    (l <- encode_SensorData_Spec (inj_SumType SensorTypes SensorIDs[@"TirePressure"] n)
 Empty;
                     Return (fst l));
          ret (r, subs)
  }%methDefParsing.
