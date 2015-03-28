Require Import ADTSynthesis.QueryStructure.Automation.IndexSelection
        ADTSynthesis.QueryStructure.Automation.AutoDB.

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

Definition WeatherSig : ADTSig :=
  ADTsignature {
      Constructor "Init"           : unit                               -> rep,
      (* Method "AddCell"        : rep x (WeatherSchema#CELLS)        -> rep x bool,
      Method "AddMeasurement" : rep x (WeatherSchema#MEASUREMENTS) -> rep x bool, *)
      Method "CountCells"     : rep x AreaCode                        -> rep x nat
      (* Method "LocalMax"       : rep x (AreaCode * MeasurementType)    -> rep x option Z *)
    }.

Definition WeatherSpec : ADT WeatherSig :=
  QueryADTRep WeatherSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    (*update "AddCell" (cell : WeatherSchema#CELLS) : bool :=
        Insert cell into CELLS,

    update "AddMeasurement" (measurement : WeatherSchema#MEASUREMENTS) : bool :=
        Insert measurement into MEASUREMENTS, *)

    query "CountCells" (area : AreaCode) : nat :=
      Count (For (cell in CELLS)
             Where (area = cell!AREA_CODE)
             Return 1)

     (*query "LocalMax" (params: AreaCode * MeasurementType) : option Z :=
        MaxZ (For (cell in CELLS) (measurement in MEASUREMENTS)
              Where (cell!AREA_CODE = fst params)
              Where (measurement!MEASUREMENT_TYPE = snd params)
              Where (cell!CELL_ID = measurement!CELL_ID)
              Return measurement!VALUE) *)
}.

Ltac CombineUse x y :=
  fun a c =>
    match goal with
      | _ => x a c
      | _ => y a c
    end.

Definition SharpenedWeatherStation :
  Sharpened WeatherSpec.
Proof.
  unfold WeatherSpec.

  Start Profiling.

  start honing QueryStructure.

  (* Old, explicit index selection*)
  (* make simple indexes using [[AREA_CODE]; [MEASUREMENT_TYPE; CELL_ID]]. *)
  make indexes using matchInclusionIndex.

  plan
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
           ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
                   match goal with
                     | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                     | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
                   end)
                  ltac:(fun f fds tail fs kind s k =>
                          match goal with
                            | _ => createLastInclusionTerm f fds tail fs kind s k
                            | _ => createLastRangeTerm f fds tail fs kind s k
                          end)
                         ltac:(fun SC F indexed_attrs visited_attrs f T k =>
                                 match goal with
                                   | _ => InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                   | _ => RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k
                                 end)
                                randomCrab
                                ltac:(fun dom f fds tail fs kind rest s k =>
                                        match goal with
                                          | _ => createLastInclusionTerm_dep dom f fds tail fs kind rest s k
                                          | _ => createLastRangeTerm_dep dom f fds tail fs kind rest s k
                                        end).
  Show Profile.

  Time FullySharpenQueryStructure WeatherSchema Index.
    implement_bag_methods.
    Show Profile.
Time Defined.
Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation. (* 28 *)


(* Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval lazy zeta iota beta delta [projT1 SharpenedWeatherStation]
  in projT1 SharpenedWeatherStation. (* 1473 *) *)


(* Time Definition WeatherStationImpl : SharpenedUnderDelegates WeatherSig :=
  Eval cbv zeta iota beta delta [projT1 SharpenedWeatherStation]
  in projT1 SharpenedWeatherStation. (* 881 *)*)
