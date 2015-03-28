Require Import Coq.Strings.String.
Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Automation.IndexSelection
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListInclusion
        ADTSynthesis.QueryStructure.Specification.SearchTerms.InRange.

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

Definition SharpenedAlbum :
  Sharpened AlbumSpec.
Proof.
  unfold AlbumSpec.

  start honing QueryStructure.

  make indexes using (CombineUse matchInclusionIndex matchRangeIndex).

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
