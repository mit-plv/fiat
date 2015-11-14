Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Bedrock.Memory.

Instance : Query_eq (Word.word n) :=
  { A_eq_dec := @Word.weq n }.
Opaque Word.weq.
Opaque Word.natToWord.

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
  MostlySharpened WeatherSpec.
Proof.

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan EqIndexTactics. *)
  master_plan EqIndexTactics.

Time Defined.

Time Definition WeatherStationImpl : ComputationalADT.cADT WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation.
Print WeatherStationImpl.
