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
          
    query "PhotosByPersons" (search_tags : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          Where (IncludedIn search_tags photo!PERSONS)
          Return photo
}.

Definition SharpenedAlbum :
  Sharpened AlbumSpec.
Proof.
  unfold AlbumSpec.

  start honing QueryStructure.

  make simple indexes using [[(EqualityIndex, EVENT_NAME); (InclusionIndex, PERSONS)]; [(RangeIndex, DATE)]].

  plan.

  FullySharpenQueryStructure AlbumSchema Index.

  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.

Time Defined.