Require Import AutoDB.

Definition MEASUREMENT := "MEASUREMENT".
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
                      MEASUREMENT :: Z,
                      MEASUREMENT_TYPE :: MeasurementType,
                      DAY :: nat,
                      TIME :: nat> ]
    enforcing [attribute CELL_ID for MEASUREMENTS references CELLS].
(* Try with three tables (distribution of areas per state) *)

Definition WeatherSig : ADTSig :=
  ADTsignature {
      "Init"           : unit                               → rep,
      "AddCell"        : rep × (WeatherSchema#CELLS)        → rep × bool,
      "AddMeasurement" : rep × (WeatherSchema#MEASUREMENTS) → rep × bool,
      "CountCells"     : rep × AreaCode                        → rep × nat,
(*      "CellIsActive"   : rep × nat                          → rep × bool, *)
      "LocalCount"       : rep × (AreaCode * MeasurementType)    → rep × nat
    }.

Definition WeatherSpec : ADT WeatherSig :=
  QueryADTRep WeatherSchema {
    const "Init" (_ : unit) : rep := empty,

    update "AddCell" (cell : WeatherSchema#CELLS) : bool :=
        Insert cell into CELLS,

    update "AddMeasurement" (measurement : WeatherSchema#MEASUREMENTS) : bool :=
        Insert measurement into MEASUREMENTS,

    query "CountCells" (area : AreaCode) : nat :=
      Count (For (cell in CELLS)
             Where (area = cell!AREA_CODE)
             Return 1),

     query "LocalCount" (params: AreaCode * MeasurementType) : nat :=
        Count (For (cell in CELLS) (measurement in MEASUREMENTS)
               Where (cell!AREA_CODE = fst params)
               Where (measurement!MEASUREMENT_TYPE = snd params)
               Where (cell!CELL_ID = measurement!CELL_ID)
               Return 1)
}.

Definition CellHeading := GetHeading WeatherSchema CELLS.
Definition MeasurementsHeading := GetHeading WeatherSchema MEASUREMENTS.

Definition CellsStorage : @BagPlusBagProof (WeatherSchema#CELLS).
  mkIndex CellHeading [ CellHeading/AREA_CODE ].
Defined.

Definition MeasurementsStorage : @BagPlusBagProof (WeatherSchema#MEASUREMENTS).
  mkIndex MeasurementsHeading [ MeasurementsHeading/MEASUREMENT_TYPE; MeasurementsHeading/CELL_ID ].
Defined.

Definition TCellsBag := BagType CellsStorage.
Definition TMeasurementsBag := BagType MeasurementsStorage.

Definition Weather_AbsR
           (or : UnConstrQueryStructure WeatherSchema)
           (nr : (TCellsBag) * (TMeasurementsBag)) : Prop :=
  or!CELLS ≃ benumerate (fst nr) /\ or!MEASUREMENTS ≃ benumerate (snd nr).

Definition WeatherStation :
  Sharpened WeatherSpec.
Proof.
  Print Ltac plan. match goal with
  | |- Sharpened ?spec =>
        unfolder spec ltac:(fun spec' => change spec with spec')
  end. start_honing_QueryStructure. hone_representation Weather_AbsR.

  hone method "LocalCount".
  Print Ltac observer.
  Print Ltac observer'.

  observer.
  startMethod Weather_AbsR. 
  concretize.
  asPerm .
  asPerm_indep.
  asPerm_indep.
  asPerm_indep.
  asPerm_indep.
  asPerm_indep.
  Unset Ltac Debug.
  asPerm_dep (CellsStorage, MeasurementsStorage).

  asPerm_indep.
  asPerm_dep (CellsStorage, MeasurementsStorage).

  asPerm_indep.

  match goal with
    | [ |- _ ] =>
                 setoid_rewrite filter_join_lists; simp
  end.

  match goal with
    | [ |- context[filter _ (Join_Lists ?ls1 (filter ?f ?ls2))] ] =>
      setoid_rewrite (swap_joins ls1 (filter f ls2)); trickle_swap; simp
  end.
  asPerm_indep.
  repeat asPerm_indep.
  asPerm Weather_AbsR.
  asPerm_indep.
  asPerm_indep.
  Print Ltac asPerm_indep.
  Check filter_join_lists.
  match goal with
  | |- context [filter ?F (Join_Lists _ _)] => pose F
  end.

  honeOne.
  hone method "CountCells".
  observer.

  hone method "AddCell".
  mutator.

  hone method "AddMeasurement".
  mutator. (* Badly needs a second index on CellIDs *)

  hone method "LocalCount".
  Print Ltac observer.
  Print Ltac observer'.

  startMethod Weather_AbsR. 
  concretize.
  Print Ltac asPerm_indep.
  Check filter_join_lists.
  match goal with
  | |- context [filter ?F (Join_Lists _ _)] => pose F
  end.

Ltac getFst2 F k :=
  match type of F with
  | ?A * ?B -> ?C =>
    let G := fresh "G" in let p := fresh "p" in let H := fresh "H" in
    evar (G : A -> C); assert (H : forall p, F p = G (fst p)) by (subst G; intro p;
      pattern (fst p);
      match goal with
      | [ |- (fun t => @?f t = @?g t) _ ] => equate g f; reflexivity
      end); clear H;
    let G' := eval unfold G in G in clear G; k G'
  end.

  Unset Ltac Debug.
getFst2 (fun a: (@Tuple CellHeading) * (@Tuple MeasurementsHeading) => ?[eq_nat_dec (fst a)!AREA_CODE (fst n)]) ltac:(fun f => rewrite (filter_join_fst f)). getSnd F ltac:(fun f => rewrite (filter_join_snd f))

  Print Ltac asPerm'.
  asPerm storages.
  commit. 
  choose_db Weather_AbsR.
  finish honing

  observer' Weather_AbsR (CellsStorage, MeasurementsStorage).

  honeOne.

  hone
  match goal with
  | _:?AbsR _ _
    |- _ =>
        match type of AbsR with
        | UnConstrQueryStructure _ -> ?T -> Prop =>
            let storages := storageOf T in
            pose AbsR; pose storages
        end
  end.

  startMethod Weather_AbsR. 
  concretize.
  asPerm (CellsStorage, MeasurementsStorage).

  Eval cbv delta [CellsStorage] in CellsStorage.
  Print Ltac fields.
  
  Ltac check_for_attr_list X :=
    match type of X with
      | list (Attributes _) => idtac
    end.

  Ltac pull_attributes_list body :=
    match body with
      | let x := ?X in _ => check_for_attr_list X; X
      | let x := ?X in let y := ?Y in _ => check_for_attr_list Y; 
                                          Y
      | _ => fail "No list of attributes found"
    end.

  Unset Ltac Debug.
  pull_attributes_list ltac:(eval cbv delta [CellsStorage] in CellsStorage).

  let fs := pull_attributes_list CellsStorage in pose (fs' := fs). 


  
  match  with
    | let src := ?X in ?body => X
  end


  match type of fs' with
    | ?a => assert a
  end.
  compute in fs'.

  
  unfold WeatherSchema in fs'.
  Unset Printing Notations. Show. 
  unfold QSGetNRelSchemaHeading, GetNRelSchemaHeading, schemaHeading, GetNRelSchema in fs'. simpl in fs'. idtac "hello".
  useIndex CellsStorage.

  Print Ltac concretize1.
  
asPerm storages; commit; choose_db AbsR;
  finish honing.
observer' AbsR storages
  (*unfold cast, eq_rect_r, eq_rect, eq_sym.*)
  Notation "a ! b" := (a ``(b)).
  Notation "a == b" := (if string_dec a b then true else false).
  Notation "a != b" := (negb (beq_nat b a)) (at level 20, no associativity).
  Notation "a == b" := (beq_nat b a).
  repeat match goal with
           | [ H := _ |- _ ] => unfold H; clear H
         end.
  finish sharpening.
Defined.
