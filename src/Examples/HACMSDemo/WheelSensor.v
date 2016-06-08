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
        Fiat.Examples.DnsServer.DecomposeEnumField
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.Examples.HACMSDemo.DuplicateFree.

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

Lemma refineEquiv_Query_Where_And
      {ResultT}
  : forall P P' bod,
    (P \/ ~ P)
    -> refineEquiv (@Query_Where ResultT (P /\ P') bod)
                (Query_Where P (Query_Where P' bod)).
Proof.
  split; unfold refine, Query_Where; intros;
    computes_to_inv; computes_to_econstructor;
      intuition.
  - computes_to_inv; intuition.
  - computes_to_inv; intuition.
  - computes_to_econstructor; intuition.
Qed.

Corollary refineEquiv_For_Query_Where_And
          {ResultT}
          {qs_schema}
  : forall (r : UnConstrQueryStructure qs_schema) idx P P' bod,
    (forall tup, P tup \/ ~ P tup)
    -> refine (For (UnConstrQuery_In
                      r idx
                      (fun tup => @Query_Where ResultT (P tup /\ P' tup) (bod tup))))
              (For (UnConstrQuery_In
                      r idx
                      (fun tup => Where (P tup) (Where (P' tup) (bod tup))))).
Proof.
  intros; apply refine_refine_For_Proper.
  apply refine_UnConstrQuery_In_Proper.
  intro; apply refineEquiv_Query_Where_And; eauto.
Qed.

Lemma refine_If_IfOpt {A B}
  : forall (a_opt : option A) (t e : Comp B),
    refine (If_Then_Else (If_Opt_Then_Else a_opt (fun _ => false) true)
                         t e)
           (If_Opt_Then_Else a_opt (fun _ => e) t).
Proof.
  destruct a_opt; simpl; intros; reflexivity.
Qed.

Global Arguments icons2 _ _ _ _ _ _ _ / .
Global Arguments GetAttributeRaw _ !tup !attr / .
Global Arguments ilist2_tl _ _ _ _ !il / .
Global Arguments ilist2_hd _ _ _ _ !il / .

Theorem SharpenedWheelSensor :
  FullySharpened WheelSensorSpec.
Proof.
  start sharpening ADT.
  start_honing_QueryStructure'.
  hone method "AddSpeedSubscriber".
  {
    dropDuplicateFree.
  }
  hone method "AddTirePressureSubscriber".
  {
    dropDuplicateFree.
  }
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
  {
    simplify with monad laws.
    etransitivity.
    apply refine_under_bind_both; intros.
    apply (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0 Fin.F1).
    apply refine_under_bind_both; intros.
    etransitivity.
    eapply (refineEquiv_For_Query_Where_And r_o Fin.F1).
    intros; eapply SensorID_decideable.
    simpl.
    setoid_rewrite (@refine_QueryIn_Where _ WheelSensorSchema Fin.F1 _ _ _ _ _ H0 _ _ _ ).
    unfold Tuple_DecomposeRawQueryStructure_inj; simpl.
    reflexivity.
    rewrite refine_If_IfOpt.
    etransitivity.
    eapply refine_If_Opt_Then_Else_Bind; simpl.
    apply refine_If_Opt_Then_Else; unfold pointwise_relation; intros.
    simplify with monad laws.
    rewrite_drill.
    apply refine_pick_val.
    apply H0.
    simpl; finish honing.
    simplify with monad laws; simpl.
    rewrite_drill.
    apply refine_pick_val.
    apply (DecomposeRawQueryStructureSchema_Insert_AbsR_eq H0).
    finish honing.
    simpl; finish honing.
  }
  {
    simplify with monad laws.
    etransitivity.
    apply refine_under_bind_both; intros.
    apply (refine_UnConstrFreshIdx_DecomposeRawQueryStructureSchema_AbsR_Equiv H0 Fin.F1).
    apply refine_under_bind_both; intros.
    etransitivity.
    eapply (refineEquiv_For_Query_Where_And r_o Fin.F1).
    intros; eapply SensorID_decideable.
    simpl.
    setoid_rewrite (@refine_QueryIn_Where _ WheelSensorSchema Fin.F1 _ _ _ _ _ H0 _ _ _ ).
    unfold Tuple_DecomposeRawQueryStructure_inj; simpl.
    reflexivity.
    rewrite refine_If_IfOpt.
    etransitivity.
    eapply refine_If_Opt_Then_Else_Bind; simpl.
    apply refine_If_Opt_Then_Else; unfold pointwise_relation; intros.
    simplify with monad laws.
    rewrite_drill.
    apply refine_pick_val.
    apply H0.
    simpl; finish honing.
    simplify with monad laws; simpl.
    rewrite_drill.
    apply refine_pick_val.
    apply (DecomposeRawQueryStructureSchema_Insert_AbsR_eq H0).
    finish honing.
    simpl; finish honing.
  }
  {
    simplify with monad laws.
    rewrite_drill.
    setoid_rewrite (@refine_QueryIn_Where _ WheelSensorSchema Fin.F1 _ _ _ _ _ H0 _ _ _ ).
    unfold Tuple_DecomposeRawQueryStructure_inj; simpl.
    finish honing.
    rewrite_drill.
    apply refine_pick_val; eassumption.
    simpl.
    finish honing.
  }
  { simplify with monad laws.
    rewrite_drill.
    setoid_rewrite (@refine_QueryIn_Where _ WheelSensorSchema Fin.F1 _ _ _ _ _ H0 _ _ _ ).
    unfold Tuple_DecomposeRawQueryStructure_inj; simpl.
    finish honing.
    rewrite_drill.
    apply refine_pick_val; eassumption.
    simpl.
    finish honing.
  }
  hone representation using (fun r_o r_n => snd r_o = r_n).
  { simplify with monad laws.
    apply refine_pick_val.
    reflexivity.
  }
  { simplify with monad laws.
    rewrite H0.
    rewrite_drill; try (clear r_o H0; finish honing).
    rewrite_drill; try (clear r_o H0; finish honing).
    etransitivity.
    apply refine_If_Opt_Then_Else_Bind.
    unfold H2; eapply refine_If_Opt_Then_Else.
    intro; simplify with monad laws.
    etransitivity.
    apply refine_bind.
    rewrite refine_pick_val; eauto.
    finish honing.
    intro; simpl; finish honing.
    simplify with monad laws.
    finish honing.
    simplify with monad laws.
    etransitivity.
    simpl; apply refine_bind.
    rewrite refine_pick_val; eauto.
    finish honing.
    intro; simpl; finish honing.
    simplify with monad laws.
    finish honing.
  }
  { simplify with monad laws.
    rewrite H0.
    rewrite_drill; try (clear r_o H0; finish honing).
    rewrite_drill; try (clear r_o H0; finish honing).
    etransitivity.
    apply refine_If_Opt_Then_Else_Bind.
    unfold H2; eapply refine_If_Opt_Then_Else.
    intro; simplify with monad laws.
    etransitivity.
    apply refine_bind.
    rewrite refine_pick_val; eauto.
    finish honing.
    intro; simpl; finish honing.
    simplify with monad laws.
    finish honing.
    simplify with monad laws.
    etransitivity.
    simpl; apply refine_bind.
    rewrite refine_pick_val; eauto.
    finish honing.
    intro; simpl; finish honing.
    simplify with monad laws.
    finish honing.
  }
  { simplify with monad laws.
    rewrite H0.
    etransitivity.
    apply refine_under_bind; intros.
    simpl; apply refine_bind.
    apply refine_pick_val; eauto.
    intro; simpl; finish honing.
    simplify with monad laws; simpl.
    finish honing.
  }
  { simplify with monad laws.
    rewrite H0.
    etransitivity.
    apply refine_under_bind; intros.
    simpl; apply refine_bind.
    apply refine_pick_val; eauto.
    intro; simpl; finish honing.
    simplify with monad laws; simpl.
    finish honing.
  }
  unfold Tuple_DecomposeRawQueryStructure_proj; simpl.
  unfold DecomposeRawQueryStructureSchema, DecomposeSchema; simpl.
  let makeIndex attrlist :=
      make_simple_indexes attrlist
        ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
        ltac:(LastCombineCase5 BuildLastEqualityIndex) in
  GenerateIndexesForAll EqExpressionAttributeCounter ltac:(fun attrlist =>
                                                             let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in makeIndex attrlist').
  Require Import Fiat.Examples.Tutorial.Tutorial.
  simplify with monad laws.
  initializer.
  - implement_insert CreateTerm EarlyIndex LastIndex
                     makeClause_dep EarlyIndex_dep LastIndex_dep.
    simplify with monad laws.
