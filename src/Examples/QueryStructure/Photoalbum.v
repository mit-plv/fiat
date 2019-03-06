Require Import Fiat.QueryStructure.Automation.MasterPlan.

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
           : rep,
      Method "AddPhoto"
           : rep * (AlbumSchema#PHOTOS)       -> rep * bool,
      Method "AddEvent"
           : rep * (AlbumSchema#EVENTS)       -> rep * bool,
      Method "PhotosByDateRange"
           : rep * nat * nat                -> rep * (list (AlbumSchema#PHOTOS)),
      Method "PhotosByPersons"
           : rep * (list string)                -> rep * (list (AlbumSchema#PHOTOS))
    }.

Require Import Fiat.QueryStructure.Specification.SearchTerms.ListInclusion.
Require Import Fiat.QueryStructure.Specification.SearchTerms.InRange.

Definition AlbumSpec : ADT AlbumSig :=
  Def ADT {
    rep := QueryStructure AlbumSchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "AddPhoto" (r : rep) (photo : AlbumSchema#PHOTOS) : rep * bool :=
      Insert photo into r!PHOTOS,

    Def Method1 "AddEvent" (r : rep) (event : AlbumSchema#EVENTS) : rep * bool :=
      Insert event into r!EVENTS,

    Def Method2 "PhotosByDateRange" (r : rep) (startDate : nat) (endDate : nat) : rep * list (AlbumSchema#PHOTOS) :=
      photos <- For (photo in r!PHOTOS)
             (event in r!EVENTS)
             Where (event!EVENT_NAME = photo!EVENT_NAME)
             Where (startDate <= event!DATE <= endDate)
             Return photo;
    ret (r, photos),

    Def Method1 "PhotosByPersons" (r : rep) (persons : list string) : rep * list (AlbumSchema#PHOTOS) :=
      photos <- For (photo in r!PHOTOS)
             Where (IncludedIn persons photo!PERSONS)
             Return photo;
    ret (r, photos)
}%methDefParsing.

Definition SharpenedAlbum :
  FullySharpened AlbumSpec.
Proof.

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan ltac:(CombineIndexTactics InclusionIndexTactics
          ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).*)
  master_plan
    ltac:(CombineIndexTactics InclusionIndexTactics
          ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics)).
Time Defined.
(*Mem: 1380MB *)

Time Definition AlbumImpl : ComputationalADT.cADT AlbumSig :=
  Eval simpl in (projT1 SharpenedAlbum).
(* Mem: 1028MB *)
Print AlbumImpl.
