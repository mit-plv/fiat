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

Ltac CombineUse x y :=
  fun a c =>
    match goal with
      | _ => x a c
      | _ => y a c
    end.

Ltac foo :=
  remove trivial insertion checks;
    (* The trivial insertion checks involve the fresh id,
       so we need to drill under the binder before
       attempting to remove them. *)
    rewrite refine_bind;
    [ | reflexivity |
      unfold pointwise_relation; intros; subst_strings;
      repeat remove_trivial_insertion_constraints;
      subst_strings;
      (* These simplify and implement nontrivial constraint checks *)
      repeat first
             [ drop_symmetric_functional_dependencies
             | fundepToQuery; try simplify with monad laws
             | foreignToQuery; try simplify with monad laws
             | setoid_rewrite refine_trivial_if_then_else; simplify with monad laws
             ];
             higher_order_reflexivity ];
    finish honing.

Ltac bar :=
  simplify with monad laws;
    subst_strings; repeat (setoid_rewrite DropQSConstraintsQuery_In; simpl);
    repeat setoid_rewrite DropQSConstraintsQuery_In_UnderBinder;
    simpl; pose_string_ids;
    setoid_rewrite refineEquiv_pick_eq';
    simplify with monad laws; cbv beta; simpl;
    match goal with
        H : DropQSConstraints_AbsR _ _ |- _ =>
        unfold DropQSConstraints_AbsR in H; rewrite H
    end;
    finish honing.

Definition WeatherSpec' : ADT WeatherSig.
  let H := eval cbv delta [WeatherSpec
                         QSGetNRelSchemaHeading GetNRelSchema
                         GetNRelSchemaHeading Domain Specif.value
                         IndexBound_tail IndexBound_head WeatherSpec] beta in WeatherSpec in
      let H' := eval simpl in H in
          exact H'.
Defined.

Definition SharpenedWeatherStation' :
  sigT (fun adt => refineADT WeatherSpec' adt).
Proof.
  eexists.
  Set Printing All.
  Show Proof.
  cbv beta delta [WeatherSpec' Specif.value].
  pose_string_ids.
  repeat match goal with
               | |- context[BuildHeading ?attrlist] =>
                 let heading := fresh "heading" in
                 set (BuildHeading attrlist) as heading
           end.
  match goal with
      |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _] =>
      eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
  [ repeat (first [eapply refine_Constructors_nil
                        | eapply refine_Constructors_cons;
                          [ intros;
                            match goal with
                              |  |- refine _ (?E _) => let H := fresh in set (H := E)
                              | _ => idtac
                            end | ] ])
        | repeat (first [eapply refine_Methods_nil
                        | eapply refine_Methods_cons;
                          [ intros;
                            match goal with
                              |  |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | _ => idtac
                            end | ]
                        ])]
  end.
  Show Proof.
  apply Constructor_DropQSConstraints.
  - subst heading; subst heading0; foo.
  - foo.
  - subst heading; subst heading0.
    bar.
  - subst heading; subst heading0; bar.
Defined.


Definition SharpenedWeatherStation :
  Sharpened WeatherSpec.
Proof.
  eapply SharpenStep.
  eapply (projT2 SharpenedWeatherStation').
  unfold SharpenedWeatherStation'; simpl.
  Start Profiling.

  (* Old, explicit index selection*)
  (* make simple indexes using [[AREA_CODE]; [MEASUREMENT_TYPE; CELL_ID]]. *)

  GenerateIndexesForAll
    ClauseMatchers
    ltac:(fun attrlist =>
            match goal with
              | [ |- Sharpened (@BuildADT (UnConstrQueryStructure ?sch) _ _ _ _ )] =>
                let sch' := eval simpl in (qschemaSchemas sch) in
                    makeIndex' sch' attrlist
                               ltac:(fun l =>
                                       let index := fresh "Index" in
                                       pose l as index;
                                     revert Index;
                                     pose_string_ids;
                                     repeat match goal with
                                              | |- context [ ``(?R) ] =>
                                                let idx := fresh in
                                                set ``(R) as fresh in *
                                              | |- context [@Build_BoundedIndex ?A ?Bound ?idx ?bnd] =>
                                                let idx := fresh in
                                                set (@Build_BoundedIndex A Bound idx bnd) as idx in *
                                            end;
                                     repeat match goal with
                                              | |- context[BuildHeading ?attrlist] =>
                                                let heading := fresh "heading" in
                                                set (BuildHeading attrlist) as heading

                                            end;
                                     intros; cbv beta; simpl in *;
                                       unfold Domain in *; simpl in *;
                                       hone representation using (@DelegateToBag_AbsR sch index))
            end).
  - initializer.
  - subst heading; subst heading0.
    insertion
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
  - subst heading; subst heading0.
    insertion
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
  - observer
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
  - observer
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
    Unset Printing All.
    idtac.
    simpl.
    Set Printing All.
    idtac.
    Unset Printing All.
    pose_string_ids.
    repeat match goal with
             | |- context [ ``(?R) ] =>
               let idx := fresh in
               set ``(R) as fresh in *
             | |- context [@Build_BoundedIndex ?A ?Bound ?idx ?bnd] =>
               let idx := fresh in
               set (@Build_BoundedIndex A Bound idx bnd) as idx in *
           end;
      repeat match goal with
               | |- context[BuildHeading ?attrlist] =>
                 let heading := fresh "heading" in
                 set (BuildHeading attrlist) as heading
                                                  
             end.
    Set Printing All.
    idtac.
    repeat match goal with
        |- context[IndexedQueryStructure ?qs_schema ?search_terms] =>
        let repType := fresh "repType" in
        set (IndexedQueryStructure qs_schema search_terms) as repType in *
    end.
    Check CallBagMethod.
    repeat match goal with
               |- appcontext[@CallBagMethod ?qs_schema (@icons ?A ?B ?a ?As ?b ?Bs)] => 
               let index := fresh "Index" in
               set (@icons A B a As b Bs) as index in *
           end.
    Print SearchUpdateTerms.
    repeat match goal with
               |- context [@Build_SearchUpdateTerms
                             ?heading ?stType ?stMatcher
                             ?utType ?utApply] =>
               let stu := fresh "SearchUpdateTerm" in
               set (@Build_SearchUpdateTerms heading stType stMatcher utType utApply) as stu in *
           end.
    Unset Printing All.
    idtac.
  - simpl.


    subst_strings; pose_string_ids.
  Set Printing All.
  idtac.
  honeOne
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
  Set Printing All.
  idtac.
  simpl.
  subst_strings; pose_string_ids.
  subst heading; subst heading0.
  repeat match goal with
           | |- context[BuildHeading ?attrlist] =>
             let heading := fresh "heading" in
             set (BuildHeading attrlist) as heading
         end.
  honeOne
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
  simpl.
  subst_strings; pose_string_ids.
  repeat match goal with
           | |- context[BuildHeading ?attrlist] =>
             let heading := fresh "heading" in
             set (BuildHeading attrlist) as heading
         end.
  Print IndexedQueryStructure.

        Set Printing All.
        honeOne
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
  simplify with monad laws.
  Show Profile.
  implement_bag_methods.
  Show Profile.
Time Defined.
Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval simpl in projT1 SharpenedWeatherStation. (* 28 --> 10 *)

Print SharpenedWeatherStation.
Print transitivity.
Optimize Proof.

Optimize Heap.


(* Time Definition WeatherStationImpl' : SharpenedUnderDelegates WeatherSig :=
  Eval lazy zeta iota beta delta [projT1 SharpenedWeatherStation]
  in projT1 SharpenedWeatherStation. (* 1473 *) *)


(* Time Definition WeatherStationImpl : SharpenedUnderDelegates WeatherSig :=
  Eval cbv zeta iota beta delta [projT1 SharpenedWeatherStation]
  in projT1 SharpenedWeatherStation. (* 881 *)*)
