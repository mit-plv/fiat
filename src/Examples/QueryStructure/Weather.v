Require Import Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.QSImplementation.

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
  Eval simpl in
    QueryADTRep WeatherSchema {
    Def Constructor Init (_ : unit) : rep := empty,

    update AddCell (r : rep, cell : WeatherSchema#CELLS) : bool :=
      Insert cell into r!CELLS,

    update AddMeasurement (r : rep, measurement : WeatherSchema#MEASUREMENTS) : bool :=
      Insert measurement into r!MEASUREMENTS,

    query CountCells (r : rep, area : AreaCode) : nat :=
      Count (For (cell in r!CELLS)
             Where (area = cell!AREA_CODE)
             Return 1),

    query LocalMax (r : rep, params: AreaCode * MeasurementType) : option Z :=
      MaxZ (For (cell in r!CELLS) (measurement in r!MEASUREMENTS)
            Where (cell!AREA_CODE = fst params)
            Where (measurement!MEASUREMENT_TYPE = snd params)
            Where (cell!CELL_ID = measurement!CELL_ID)
            Return measurement!VALUE)
}.

Definition SharpenedWeatherStation :
  FullySharpened WeatherSpec.
Proof.

  start_honing_QueryStructure.
  { GenerateIndexesForAll
      ltac:(fun _ _ => fail)
             ltac:(fun attrList =>
                     make_simple_indexes
                       attrList
                       ltac:(CombineCase6 BuildEarlyEqualityIndex
                                          ltac:(fun _ _ _ _ _ _ => fail))
                              ltac:(CombineCase5 BuildLastEqualityIndex
                                                 ltac:(fun _ _ _ _ _ => fail))).
     initializer.
     insertion EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
               EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
     insertion EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
               EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
     observer EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
              EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
     observer EqIndexUse createEarlyEqualityTerm createLastEqualityTerm
              EqIndexUse_dep createEarlyEqualityTerm_dep createLastEqualityTerm_dep.
     pose_headings_all.

     match goal with
     | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
       FullySharpenQueryStructure Schema Indexes
     end.
  }

  { simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms.
    BuildQSIndexedBags' BuildEarlyEqualityBag BuildLastEqualityBag. }
  higher_order_reflexivityT.

Time Defined.

Time Definition WeatherStationImpl' : ComputationalADT.cADT WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation.

Print WeatherStationImpl'.
