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

Definition AlbumSpec : ADT AlbumSig :=
  QueryADTRep AlbumSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddPhoto" (r : rep, photo : AlbumSchema#PHOTOS) : bool :=
      Insert photo into r!PHOTOS,

    update "AddEvent" (r : rep, event : AlbumSchema#EVENTS) : bool :=
      Insert event into r!EVENTS,

    query "PhotosByDateRange" (r : rep, range : nat * nat) : list (AlbumSchema#PHOTOS) :=
      For (photo in r!PHOTOS)
          (event in r!EVENTS)
          Where (event!EVENT_NAME = photo!EVENT_NAME)
          Where (InRange event!DATE range)
          Return photo,

    query "PhotosByPersons" (r : rep, persons : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in r!PHOTOS)
          Where (IncludedIn persons photo!PERSONS)
          Return photo
}.

  Require Import Fiat.QueryStructure.Specification.SearchTerms.ListInclusion.
  Require Import Fiat.QueryStructure.Specification.SearchTerms.InRange.

Definition SharpenedAlbum :
  MostlySharpened AlbumSpec.
Proof.

  start honing QueryStructure.


  (* Manually select indexes + data structure. *)
    make simple indexes using [[("EqualityIndex", Fin.FS (Fin.FS Fin.F1)); ("InclusionIndex", Fin.FS Fin.F1)]; [("EqualityIndex", Fin.F1); ("RangeIndex", Fin.FS Fin.F1)]].
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
