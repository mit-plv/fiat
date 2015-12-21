Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition VALUE := "VALUE".
Definition MEASUREMENT_TYPE := "MEASUREMENT_TYPE".
Definition TIME := "TIME".
Definition CELL_ID := "CELL_ID".

Definition STATE := "STATE".
Definition AREA_CODE := "AREA_CODE".
Definition DETAILS := "DETAILS".
Definition DAY := "DAY".

Definition WIND := 0.
Definition HUMIDITY := 1.
Definition TEMPERATURE := 2.
Definition PRESSURE := 3.

Definition MEASUREMENTS := "MEASUREMENTS".
Definition CELLS := "CELLS".

Definition MeasurementType := nat.
Definition AreaCode        := nat.
Definition State           := string.

Definition WeatherSchema :=
  Query Structure Schema
    [ relation CELLS has
              schema <CELL_ID :: nat,
                      STATE :: State,
                      AREA_CODE :: nat,
                      DETAILS :: string>
              where attributes [STATE] depend on [AREA_CODE]; (* second clause? *)
      relation MEASUREMENTS has
              schema <CELL_ID :: nat,
                      VALUE :: Z,
                      MEASUREMENT_TYPE :: MeasurementType,
                      DAY :: nat,
                      TIME :: nat> ]
    enforcing [attribute CELL_ID for MEASUREMENTS references CELLS].

(* Try with three tables (distribution of areas per state) *)

Definition Init := "Init".
Definition AddCell := "AddCell".
Definition AddMeasurement := "AddMeasurement".
Definition CountCells := "CountCells".
Definition LocalMax := "LocalMax".

Definition WeatherSig : ADTSig :=
  ADTsignature {
      Constructor Init      : rep,
      Method AddCell        : rep * (WeatherSchema#CELLS)        -> rep * bool,
      Method AddMeasurement : rep * (WeatherSchema#MEASUREMENTS) -> rep * bool,
      Method CountCells     : rep * AreaCode                        -> rep * nat,
      Method LocalMax       : rep * AreaCode * MeasurementType    -> rep * (option Z)
    }.

Definition WeatherSpec : ADT WeatherSig :=
  Eval simpl in
    QueryADTRep WeatherSchema {
    Def Constructor0 Init : rep := empty,

    Def Method1 AddCell (r : rep) (cell : WeatherSchema#CELLS) : rep * bool :=
      Insert cell into r!CELLS,

    Def Method1 AddMeasurement (r : rep) (measurement : WeatherSchema#MEASUREMENTS) : rep * bool :=
      Insert measurement into r!MEASUREMENTS,

    Def Method1 CountCells (r : rep) (area : AreaCode) : rep * nat :=
      cnt <- Count (For (cell in r!CELLS)
                        Where (area = cell!AREA_CODE)
                        Return 1);
    ret (r, cnt),

    Def Method2 LocalMax (r : rep) (areaC : AreaCode) (measType : MeasurementType) : rep * (option Z) :=
      max <- MaxZ (For (cell in r!CELLS) (measurement in r!MEASUREMENTS)
            Where (cell!AREA_CODE = areaC)
            Where (measurement!MEASUREMENT_TYPE = measType)
            Where (cell!CELL_ID = measurement!CELL_ID)
            Return measurement!VALUE);
    ret (r, max)
}%methDefParsing.

Definition SharpenedWeatherStation :
  FullySharpened WeatherSpec.
Proof.

  start sharpening ADT.
  pose_string_hyps.
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl | ]
                          ])]
    end | ].
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone representation using (@FiniteTables_AbsR WeatherSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + simpl.
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; finish honing).
      repeat simplify_queries.
      unfold QueryResultComp.
      setoid_rewrite refine_IndexedEnsemble_Intersection_Intersection.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; finish honing).
repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; finish honing).
      doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
      Unset Ltac Debug.


Unset Ltac Debug.
      doAny simplify_queries
             ltac:(Finite_AbsR_rewrite_drill) ltac:(repeat subst_refine_evar; finish honing).
      doAny' simplify_queries
             ltac:(set_evars; Finite_AbsR_rewrite_drill) ltac:(repeat subst_refine_evar; finish honing).


repeat simplify_queries.

      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      Finite_AbsR_rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).

      repeat simplify_queries.
      simplify_queries.
      Focus 2.
      decide equality.
      eapply A_eq_dec.
      | rewrite (@refine_Where_Intersection _ _ _ _ _ _)
      simplify_queries.


      simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      repeat simplify_queries.
      rewrite_drill || (repeat subst_refine_evar; try finish honing).
      rewrite_drill.

      doAny' simplify_queries
             rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + simpl.

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan EqIndexTactics. *)
  master_plan EqIndexTactics.

Time Defined.

Time Definition WeatherStationImpl : ComputationalADT.cADT WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation.
Print WeatherStationImpl.
