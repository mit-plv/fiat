Require Import  ADTSynthesis.QueryStructure.Automation.AutoDB.

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
      Constructor Init           : unit                               -> rep,
      Method AddCell        : rep x (WeatherSchema#CELLS)        -> rep x bool,
      Method AddMeasurement : rep x (WeatherSchema#MEASUREMENTS) -> rep x bool,
      Method CountCells     : rep x AreaCode                        -> rep x nat,
      Method LocalMax       : rep x (AreaCode * MeasurementType)    -> rep x option Z
    }.

Definition WeatherSpec : ADT WeatherSig :=
  QueryADTRep WeatherSchema {
    Def Constructor Init (_ : unit) : rep := empty,

    update AddCell (cell : WeatherSchema#CELLS) : bool :=
      Insert cell into CELLS,

    update AddMeasurement (measurement : WeatherSchema#MEASUREMENTS) : bool :=
      Insert measurement into MEASUREMENTS,

    query CountCells (area : AreaCode) : nat :=
      Count (For (cell in CELLS)
             Where (area = cell!AREA_CODE)
             Return 1),

    query LocalMax (params: AreaCode * MeasurementType) : option Z :=
      MaxZ (For (cell in CELLS) (measurement in MEASUREMENTS)
            Where (cell!AREA_CODE = fst params)
            Where (measurement!MEASUREMENT_TYPE = snd params)
            Where (cell!CELL_ID = measurement!CELL_ID)
            Return measurement!VALUE)
}.

Definition SharpenedWeatherStation :
  MostlySharpened WeatherSpec.
Proof.
  simple_master_plan.
  Time Defined.
  (* <95 seconds for master_plan.
     <100 seconds for Defined.
      500 seconds after switch.
   *)

Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation.

Print WeatherStationImpl'.

(* This still takes forever. Maybe try w/o zeta?
Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval vm_compute in projT1 SharpenedWeatherStation. *)
