Require Import  ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Automation.QSImplementation.

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
  partial_master_plan EqIndexTactics.

  FullySharpenQueryStructure WeatherSchema Index.
Time Defined.

Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation.

Print WeatherStationImpl'.

(*  partial_master_plan

Definition SharpenedWeatherStation :
  FullySharpened WeatherSpec.
Proof.

  start honing QueryStructure.
  GenerateIndexesForAll
    matchIndex
    ltac:(fun attrlist => make simple indexes using attrlist;
          match goal with
            | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
            | |- _ => (* Otherwise implement each method using the indexed data structure *)
              plan CreateTerm EarlyIndex LastIndex
                   makeClause_dep EarlyIndex_dep LastIndex_dep
          end;
          match goal with
            | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
              FullySharpenQueryStructure Schema Indexes
          end).
  intros; simpl.
  match goal with
      |- context [Build_IndexedQueryStructure_Impl_Sigs ?SearchTerms _] =>
      BuildQSIndexedBags
        SearchTerms
        ltac:(fun Bags => eapply (LookupQSDelegateImpls' Bags))
  end.
  Start Profiling.
  repeat match goal with
             |- refineADT (ComputationalADT.LiftcADT
                             (Sharpened_Implementation
                                (let id' := ?B in ?bod)
                                ?C ?D))
                          ?bod' =>
             change (let id' := B in
                     refineADT (ComputationalADT.LiftcADT
                                  (Sharpened_Implementation
                                     bod
                                     C D))
                               bod'); intros end.
  Show Profile.
  simpl.

  (Sharpened_Implementation
                           (let id := ?B in ?bod)))
                     ?bod'=> idtac end.
        change
          (let id := B in
           refineADT (ComputationalADT.LiftcADT
                        (Sharpened_Implementation
                           (let id := B in bod)))
                     bod'); intros
    end.

             (Sharpened_DelegateSpecs bod idx)
                     (ComputationalADT.LiftcADT
                        (existT (ComputationalADT.pcADT
                                   (Sharpened_DelegateSigs
                                      bod' idx))
                                (bod2 idx) (bod3 idx)))); intros
    end.

  simpl.

  simpl in X.
      eapply X.
    let impl' :=
        match goal with
            |- @FullySharpenedUnderDelegates _ _ ?Impl => Impl
        end in
    (* Not having to worry about re-typing the body during zeta-expansion
     yields a 30x speedup.
     *)
    assert (True) by
        (clear FullySharpenedImpl; zeta_expand_all impl; unify impl impl'; econstructor);
      exact FullySharpenedImpl.



  Set Printing All.
  idtac.
  Unset Printing All.
  idtac.
  intros.
  Ltac foo idx :=
    match goal with
        |- refineADT (Sharpened_DelegateSpecs (let id := ?B in ?bod) idx)
                     (ComputationalADT.LiftcADT
                        (existT (ComputationalADT.pcADT
                                   (Sharpened_DelegateSigs
                                      (let id := ?B in ?bod') idx))
                                (?bod2 idx) (?bod3 idx))) =>
        change
          (let id := B in
           refineADT (Sharpened_DelegateSpecs bod idx)
                     (ComputationalADT.LiftcADT
                        (existT (ComputationalADT.pcADT
                                   (Sharpened_DelegateSigs
                                      bod' idx))
                                (bod2 idx) (bod3 idx)))); intros
    end.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  foo idx.
  simpl.
  subst id33.
  subst id32; subst id31.
  subst id29; subst id30.
  match goal with
      |- context [Build_IndexedQueryStructure_Impl_Sigs ?SearchTerms _] =>
      BuildQSIndexedBags
        SearchTerms
        ltac:(fun Bags => eapply proof (LookupQSDelegateImpls' Bags))
  end.
      simpl in X.
      eapply X.
    let impl' :=
        match goal with
            |- @FullySharpenedUnderDelegates _ _ ?Impl => Impl
        end in
    (* Not having to worry about re-typing the body during zeta-expansion
     yields a 30x speedup.
     *)
    assert (True) by
        (clear FullySharpenedImpl; zeta_expand_all impl; unify impl impl'; econstructor);
      exact FullySharpenedImpl.

Time Defined.
  (* <95 seconds for master_plan.
     <100 seconds for Defined.
      500 seconds after switch.
   *)

Print SharpenedWeatherStation.
Set Printing All.
Print FullySharpened_Start.

Extraction "examples/Weather.ml" init_bookstore add_book place_order get_titles num_orders.

Time Definition WeatherStationImpl' : ComputationalADT.cADT WeatherSig := projT1 SharpenedWeatherStation.
  Eval simpl in projT1 SharpenedWeatherStation.

Print WeatherStationImpl'. *)
