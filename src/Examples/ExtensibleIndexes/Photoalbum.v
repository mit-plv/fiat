Require Import Coq.Strings.String.
Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListInclusion
        Fiat.QueryStructure.Specification.SearchTerms.InRange.

Definition PHOTOS := "Photos".
Definition EVENTS := "Events".

Definition IMAGE_DATA := "ImageData".
Definition PERSONS := "Persons".
Definition EVENT_NAME := "EventName".
Definition DATE := "Date".

(* Represents image data by a list of byte characters *)
Definition DataT := list ascii.

Definition AlbumSchema :=
  Query Structure Schema
    [ relation PHOTOS has
               schema <IMAGE_DATA :: DataT,
                       PERSONS :: list string,
                       EVENT_NAME :: string>;
      relation EVENTS has
               schema <EVENT_NAME :: string,
                       DATE :: nat>
    ]
    enforcing [attribute EVENT_NAME for PHOTOS references EVENTS].

Definition AlbumSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
           : unit                             -> rep,
      Method "AddPhoto"
           : rep x (AlbumSchema#PHOTOS)       -> rep x bool,
      Method "AddEvent"
           : rep x (AlbumSchema#EVENTS)       -> rep x bool,
      Method "PhotosByDateRange"
           : rep x (nat * nat)                -> rep x list (AlbumSchema#PHOTOS),
      Method "PhotosByPersons"
           : rep x list string                -> rep x list (AlbumSchema#PHOTOS)
    }.

Definition AlbumSpec : ADT AlbumSig :=
  QueryADTRep AlbumSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddPhoto" (photo : AlbumSchema#PHOTOS) : bool :=
      Insert photo into PHOTOS,

    update "AddEvent" (event : AlbumSchema#EVENTS) : bool :=
      Insert event into EVENTS,

    query "PhotosByDateRange" (range : nat * nat) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          (event in EVENTS)
          Where (event!EVENT_NAME = photo!EVENT_NAME)
          Where (InRange event!DATE range)
          Return photo,

    query "PhotosByPersons" (persons : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          Where (IncludedIn persons photo!PERSONS)
          Return photo
}.

Ltac CombineUse x y :=
  fun a c =>
    match goal with
      | _ => x a c
      | _ => y a c
    end.

Definition SharpenedAlbum :
  Sharpened AlbumSpec.
Proof.
  unfold AlbumSpec.
  simpl.
  start honing QueryStructure.

  make indexes using matchRangeIndex.

  hone method "PhotosByDateRange".
  {
    Focused_refine_Query.
    implement_In_opt.
    etransitivity.
    etransitivity.
    apply refine_under_bind; intros.
    simpl.
    match goal with
        |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                   List_Query_In (ResultT := ?ResultT)
                                 (filter (fun a : ilist _ (?heading :: ?headings) =>
                                            @?f a && @?g a) l') ?resultComp)
                  _ =>
        first [makeEvar (ilist (@Tuple) headings -> bool)
                        ltac:(fun f' => find_equiv_tl heading headings f f';
                              let Comp_l2 := fresh in
                              assert
                                (forall a : ilist (@Tuple) headings,
                                 exists v : list (@Tuple heading),
                                   refine (l2 a) (ret v)) as Comp_l2
                                  by Realize_CallBagMethods;
                              etransitivity;
                              [apply (@refine_Join_Filtered_Comp_Lists_filter_hd_andb heading headings f' g ResultT resultComp l2 cond' Comp_l2 l1)
                              | ])
              | etransitivity;
                [apply (@refine_Join_Filtered_Comp_Lists_filter_tail_andb heading headings f ResultT resultComp l2 ) | ] ]

      | |- refine
             (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
              List_Query_In (ResultT := ?ResultT)
                            (@filter (ilist _ (?heading :: ?headings)) ?f l') ?resultComp)
             _ =>
        first [ makeEvar (ilist (@Tuple) headings -> bool)
                         ltac:(fun f' => find_equiv_tl heading headings f f';
                               let Comp_l2 := fresh in
                               assert
                                 (forall a : ilist (@Tuple) headings,
                                  exists v : list (@Tuple heading),
                                    refine (l2 a) (ret v)) as Comp_l2 by
                                     Realize_CallBagMethods;
                               apply (@refine_Join_Filtered_Comp_Lists_filter_hd heading headings f' ResultT resultComp l2 Comp_l2 l1))
              | apply (@refine_Join_Filtered_Comp_Lists_filter_tail heading headings f ResultT resultComp l2 cond' l1) ]

    end.
    simpl.
    match goal with
        |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                   List_Query_In (ResultT := ?ResultT)
                                 (filter (fun a : ilist _ (?heading :: ?headings) =>
                                            @?f a && @?g a) l') ?resultComp)
                  _ =>
        first [makeEvar (ilist (@Tuple) headings -> bool)
                        ltac:(fun f' => find_equiv_tl heading headings f f';
                              let Comp_l2 := fresh in
                              assert
                                (forall a : ilist (@Tuple) headings,
                                 exists v : list (@Tuple heading),
                                   refine (l2 a) (ret v)) as Comp_l2
                                  by Realize_CallBagMethods;
                              etransitivity;
                              [apply (@refine_Join_Filtered_Comp_Lists_filter_hd_andb heading headings f' g ResultT resultComp l2 cond' Comp_l2 l1)
                              | ])
              | etransitivity;
                [apply (@refine_Join_Filtered_Comp_Lists_filter_tail_andb heading headings f ResultT resultComp l2 ) | ] ]

      | |- refine
             (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
              List_Query_In (ResultT := ?ResultT)
                            (@filter (ilist _ (?heading :: ?headings)) ?f l') ?resultComp)
             _ =>
        first [ makeEvar (ilist (@Tuple) headings -> bool)
                         ltac:(fun f' => find_equiv_tl heading headings f f';
                               let Comp_l2 := fresh in
                               assert
                                 (forall a : ilist (@Tuple) headings,
                                  exists v : list (@Tuple heading),
                                    refine (l2 a) (ret v)) as Comp_l2 by
                                     Realize_CallBagMethods;
                               apply (@refine_Join_Filtered_Comp_Lists_filter_hd heading headings f' ResultT resultComp l2 Comp_l2 l1))
              | apply (@refine_Join_Filtered_Comp_Lists_filter_tail heading headings f ResultT resultComp l2 cond' l1) ]

    end.

    end.

    cbv beta; simpl.
    match goal with
        |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                   l'' <- Join_Filtered_Comp_Lists
                       ?a ?l2' ?cond2;
                   @?k l'')
                  _  => pose (fun a' => @refine_merge_bind _ _ _
                                                 (Join_Filtered_Comp_Lists l1 l2 cond1)
                                                 a'
                                                 (fun l' =>
                                                    Join_Filtered_Comp_Lists
                                                      a l2' cond2)

                                                 (fun l' =>
                                                    Join_Filtered_Comp_Lists
                                                      l' l2' cond2)
                                                 k
                             )
    end.
          repeat match goal with
                     |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                Join_Filtered_Comp_Lists
                                  (filter (fun a : ilist _ (?heading1 :: ?heading2 :: ?headings) =>
                                             @?f a && @?g a) l') ?l2' ?cond2)
                               _ => first (* No test case for this branch *)
                                      [ makeEvar (ilist (@Tuple) headings -> bool)
                                                 ltac:(fun f' =>
                                                         find_equiv_tl heading1 headings f f';
                                                       let Comp_l2 := fresh in
                                                       assert
                                                         (forall a : ilist (@Tuple) headings,
                                                          exists v : list (@Tuple heading1),
                                                            refine (l2 a) (ret v)) as Comp_l2
                                                           by Realize_CallBagMethods;
                                                       etransitivity;
                                                       [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb heading1 heading2 headings f' g l2 l2' cond1 cond2 Comp_l2 l1) | ])
                                      | etransitivity;
                                        [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb heading1 heading2 headings f g l2 l2' cond1 cond2 l1)
                                        | ]
                                      ]
                   | |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                Join_Filtered_Comp_Lists (a := ?heading2)
                                                         (@filter (ilist _ (?heading1 :: ?headings)) ?f l') ?l2' ?cond2) _
                     =>   first
                            [ makeEvar (ilist (@Tuple) headings -> bool) (* No test case for this branch either *)
                                       ltac:(fun f' =>
                                               find_equiv_tl heading1 headings f f';
                                             let Comp_l2 := fresh in
                                             assert
                                               (forall a : ilist (@Tuple) headings,
                                                exists v : list (@Tuple heading1),
                                                  refine (l2 a) (ret v)) as Comp_l2
                                                 by Realize_CallBagMethods;
                                             etransitivity;
                                             [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_hd heading1 heading2 headings f' l2 l2' cond1 cond2 Comp_l2 l1)
                                             | ])
                            | etransitivity;
                              [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_tail heading1 heading2 headings f l2 l2' cond1 cond2 l1) | ] ]
                   (* If there's no filter on the first list, we're done. *)
                   | |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                Join_Filtered_Comp_Lists l' ?l2' ?cond2)
                               _ => reflexivity
                 end
    end.

            (* The bottom case where we've recursed under all the bound Joins. *)
            | |- refine (l' <- Join_Filtered_Comp_Lists _ _ _;
                         List_Query_In _ _)
                        _ =>
              repeat match goal with
                         |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                                    List_Query_In (ResultT := ?ResultT)
                                                  (filter (fun a : ilist _ (?heading :: ?headings) =>
                                                             @?f a && @?g a) l') ?resultComp)
                                   _ =>
                         first [makeEvar (ilist (@Tuple) headings -> bool)
                                         ltac:(fun f' => find_equiv_tl heading headings f f';
                                               let Comp_l2 := fresh in
                                               assert
                                                 (forall a : ilist (@Tuple) headings,
                                                  exists v : list (@Tuple heading),
                                                    refine (l2 a) (ret v)) as Comp_l2
                                                   by Realize_CallBagMethods;
                                               etransitivity;
                                               [apply (@refine_Join_Filtered_Comp_Lists_filter_hd_andb heading headings f' g ResultT resultComp l2 cond' Comp_l2 l1)
                                               | ])
                               | etransitivity;
                                 [apply (@refine_Join_Filtered_Comp_Lists_filter_tail_andb heading headings f ResultT resultComp l2 ) | ] ]

                       | |- refine
                              (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                               List_Query_In (ResultT := ?ResultT)
                                             (@filter (ilist _ (?heading :: ?headings)) ?f l') ?resultComp)
                              _ =>
                         first [ makeEvar (ilist (@Tuple) headings -> bool)
                                          ltac:(fun f' => find_equiv_tl heading headings f f';
                                                let Comp_l2 := fresh in
                                                assert
                                                  (forall a : ilist (@Tuple) headings,
                                                   exists v : list (@Tuple heading),
                                                     refine (l2 a) (ret v)) as Comp_l2 by
                                                      Realize_CallBagMethods;
                                                apply (@refine_Join_Filtered_Comp_Lists_filter_hd heading headings f' ResultT resultComp l2 Comp_l2 l1))
                               | apply (@refine_Join_Filtered_Comp_Lists_filter_tail heading headings f ResultT resultComp l2 cond' l1) ]

                     end
  end
        ]
    | |- _ => higher_order_reflexivity

  end.

    distribute_filters_to_joins.

    (* Step 3: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep
  |
  ].

    observer
      RangeIndexUse createEarlyRangeTerm createLastRangeTerm
      RangeIndexUse_dep randomCrab createLastRangeTerm_dep.
  }

  hone method "PhotosByPersons".
  {
    observer
      RangeIndexUse createEarlyRangeTerm createLastRangeTerm
      RangeIndexUse_dep randomCrab createLastRangeTerm_dep.
  }


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

  }

  hone method "AddPhoto".
  {
    Implement_Insert_Checks.
    etransitivity.
     Focused_refine_Query.
  { (* Step 1: Implement [In] by enumeration. *)
    implement_In.
    (* Step 2: Convert where clauses into compositions of filters. *)
    repeat convert_Where_to_filter.
    (* Step 3: Do some simplication.*)
    repeat setoid_rewrite <- filter_and;
    try setoid_rewrite andb_true_r;
    (* Step 4: Move filters to the outermost [Join_Comp_Lists] to which *)
    (* they can be applied. *)
    repeat setoid_rewrite Join_Filtered_Comp_Lists_id;
    distribute_filters_to_joins.
    convert_filter_to_search_term.


    find_equivalent_search_term ltac:(find_simple_search_term RangeIndexUse
createEarlyRangeTerm createLastRangeTerm).
    cbv beta; simpl; convert_filter_search_term_to_find.


    let qs_schema := eval unfold q in q in
        let idx := eval unfold b in b in
            let filter_dec := eval unfold b0 in b0 in
                let search_term := eval unfold b1 in b1 in
                    find_simple_search_term InclusionIndexUse createEarlyInclusionTerm createLastInclusionTerm qs_schema idx filter_dec search_term.


  match type of search_term with
    | BuildIndexSearchTerm ?indexed_attrs =>
      let indexed_attrs' :=
          eval simpl in (map (fun kidx =>
                                {| KindNameKind := KindIndexKind kidx;
                                   KindNameName := @bindex string _ (KindIndexIndex kidx) |}) indexed_attrs) in
          let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
          findGoodTerm SC filter_dec indexed_attrs' InclusionIndexUse
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm indexed_attrs' SC fds tail createEarlyInclusionTerm createLastInclusionTerm ltac:(fun tm => try unify tm search_term;
                                                                                                                              unfold ExtensionalEq, MatchIndexSearchTerm;
                                                                                                                              simpl; intro; try prove_extensional_eq
                                                                                                                             )) end.


                    match type of search_term with
    | BuildIndexSearchTerm ?indexed_attrs =>
      let indexed_attrs' :=
          eval simpl in (map (fun kidx =>
                                {| KindNameKind := KindIndexKind kidx;
                                   KindNameName := @bindex string _ (KindIndexIndex kidx) |}) indexed_attrs) in
          let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
          findGoodTerm SC filter_dec indexed_attrs' InclusionIndexUse
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm indexed_attrs' SC fds tail createEarlyRangeTerm createLastRangeTerm ltac:(fun tm => pose tm; try unify tm search_term )) end.
assert (p1 = b1).
re
pose tail) end.


let search_term' := eval unfold b1, BuildIndexSearchTerm in b1 in
    let indexed_attrs' := eval unfold l in l in
        let SC := eval unfold h in h in
            let fds := eval unfold p in p in
                let tail := eval unfold b2 in b2 in
                    makeTerm indexed_attrs' SC fds tail createEarlyRangeTerm createLastRangeTerm ltac:(fun tm => try unify tm search_term' ).

                                                                                                         pose tm as tm''';                                                  try unify tm b1.
                                                                                                                                                                                assert (tm''' = b1)
                                                                                                      ).

    reflexivity.
    unfo b1, p2. reflexivity.
    simpl in *.

    find_simple_search_term
    ltac:(fun SC F indexed_attrs f k =>
            match goal with
              | _ => InclusionIndexUse SC F indexed_attrs f k
              | _ => RangeIndexUse SC F indexed_attrs f k
            end)
    ltac:(fun f fds tail fs kind s k =>
            match goal with
              | _ => createLastInclusionTerm f fds tail fs kind s k
              | _ => createLastRangeTerm f fds tail fs kind s k
            end)
    ltac:(fun f fds tail fs kind EarlyIndex LastIndex rest s k =>
            match goal with
              | _ => createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k
              | _ => createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k
            end)). ltac:(find_simple_search_term_dep
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
            end)).

  FullySharpenQueryStructure AlbumSchema Index.

  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.

Time Defined.
