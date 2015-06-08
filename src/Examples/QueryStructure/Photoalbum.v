Require Import Coq.Strings.String.
Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common.

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

Locate InRange.

Require Import Fiat.QueryStructure.Specification.SearchTerms.ListInclusion.
Require Import Fiat.QueryStructure.Specification.SearchTerms.InRange.


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
          Where (fst range <= event!DATE <= snd range)
          Return photo,

    query "PhotosByPersons" (persons : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          Where (StringInclusion.IncludedIn persons photo!PERSONS)
          Return photo
}.

Definition SharpenedAlbum :
  MostlySharpened AlbumSpec.
Proof.

  start honing QueryStructure.
    (* Manually select indexes + data structure. *)
    make simple indexes using [[("EqualityIndex", EVENT_NAME); ("InclusionIndex", PERSONS)]; [("EqualityIndex", EVENT_NAME); ("RangeIndex", DATE)]].
  - packaged_plan ltac:(CombineIndexTactics InclusionIndexTactics
                                            ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).
  - packaged_plan ltac:(CombineIndexTactics InclusionIndexTactics
                                            ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).
  - packaged_plan ltac:(CombineIndexTactics InclusionIndexTactics
                                            ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).
  - packaged_plan ltac:(CombineIndexTactics InclusionIndexTactics
                                            ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).
  - packaged_plan ltac:(CombineIndexTactics InclusionIndexTactics
                                            ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).

  - FullySharpenQueryStructure AlbumSchema Index.

Time Defined.
