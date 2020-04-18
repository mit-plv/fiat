Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.
Opaque Word.natToWord.
Opaque Word.wlt_dec.
Definition WordMax (w w' : W) :=
  if Word.wlt_dec w w' then w' else w.
Definition MaxW (rows : Comp (list W)) : Comp (option W) :=
  FoldAggregateOption WordMax rows.

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

Definition MeasurementType := W.

Definition WeatherSchema :=
  Query Structure Schema
    [ relation CELLS has
              schema <CELL_ID :: W,
                      AREA_CODE :: W,
                      DETAILS :: W>;
      relation MEASUREMENTS has
              schema <CELL_ID :: W,
                      VALUE :: W,
                      MEASUREMENT_TYPE :: MeasurementType,
                      DAY :: W,
                      TIME :: W> ]
    enforcing [attribute CELL_ID for MEASUREMENTS references CELLS].

(* Try with three tables (distribution of areas per state) *)

Definition Init := "Init".
Definition AddCell := "AddCell".
Definition AddMeasurement := "AddMeasurement".
Definition CountCells := "CountCells".
Definition LocalMax := "LocalMax".

Definition WeatherSpec : ADT _ :=
  Eval simpl in
    Def ADT {
      rep := QueryStructure WeatherSchema,
    Def Constructor0 Init : rep := empty,,

    Def Method1 AddCell (r : rep) (cell : WeatherSchema#CELLS) : rep * bool :=
      Insert cell into r!CELLS,

    Def Method1 AddMeasurement (r : rep) (measurement : WeatherSchema#MEASUREMENTS) : rep * bool :=
      Insert measurement into r!MEASUREMENTS,

    Def Method1 CountCells (r : rep) (area : W) : rep * nat :=
      cnt <- Count (For (cell in r!CELLS)
                        Where (area = cell!AREA_CODE)
                        Return 1);
    ret (r, cnt),

    Def Method2 LocalMax (r : rep) (areaC : W) (measType : MeasurementType) : rep * (option W) :=
      max <- MaxW (For (cell in r!CELLS) (measurement in r!MEASUREMENTS)
            Where (cell!AREA_CODE = areaC)
            Where (measurement!MEASUREMENT_TYPE = measType)
            Where (cell!CELL_ID = measurement!CELL_ID)
            Return measurement!VALUE);
    ret (r, max)
}%methDefParsing.

Definition SharpenedWeatherStation :
  MostlySharpened WeatherSpec.
Proof.
  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  GenerateIndexesForAll EqExpressionAttributeCounter
  ltac:(fun attrlist =>
          let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in
              make_simple_indexes attrlist'
                                  ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
                                         ltac:(LastCombineCase5 BuildLastEqualityIndex)).
  + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + setoid_rewrite refine_For_rev; simplify with monad laws.
    plan EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
         EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
  + hone method "AddMeasurement".
    { simpl in *; subst.
      setoid_rewrite refine_Count; simplify with monad laws.
      setoid_rewrite app_nil_r;
        setoid_rewrite map_map; simpl.
      unfold ilist2_hd at 1; simpl.
      setoid_rewrite rev_length.
      setoid_rewrite map_length.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      repeat setoid_rewrite refine_If_Then_Else_Bind.
      repeat setoid_rewrite refineEquiv_bind_bind.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      unfold H1.
      eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      finish honing.
    }
    hone method "CountCells".
    { simpl in *; subst; simplify with monad laws.
      setoid_rewrite refine_Count; simplify with monad laws.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      rewrite rev_length.
      rewrite !map_length.
      rewrite app_nil_r; simpl.
      rewrite map_length.
      finish honing.
    }
    hone method "LocalMax".
    { simpl in *; subst; simplify with monad laws.
      unfold H1; eapply refine_under_bind; intros; set_evars.
      rewrite (CallBagFind_fst H0); simpl.
      etransitivity.
      eapply refine_under_bind_both.
      eapply (@Join_Comp_Lists_eq WeatherSchema Index (Fin.FS Fin.F1)).
      intros; finish honing.
      simplify with monad laws.
      unfold H2; apply refine_under_bind; set_evars.
      intros.
      apply Join_Comp_Lists_eq' in H4; rewrite H4.
      setoid_rewrite refine_pick_eq'; simplify with monad laws.
      simpl.
      finish honing.
    }
    simpl.

    simpl; eapply reflexivityT.
  + unfold CallBagFind, CallBagInsert.
    pose_headings_all.
    match goal with
    | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
      FullySharpenQueryStructure Schema Indexes
    end.

Time Defined.

Time Definition WeatherStationImpl :=
  Eval simpl in (fst (projT1 SharpenedWeatherStation)).
Print WeatherStationImpl.
