Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Automation.IndexSelection
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListInclusion
        ADTSynthesis.QueryStructure.Specification.SearchTerms.InRange.

Definition PHOTOS := "Photos".
Definition PEOPLE := "Places".

Definition IMAGE_DATA := "ImageData".
Definition TAGS := "Tags".
Definition NAME := "Name".
Definition AGE := "Age".

(* Represents image data by a list of byte characters *)
Definition DataT := list ascii.

Definition AlbumSchema :=
  Query Structure Schema
    [ relation PHOTOS has
               schema <IMAGE_DATA :: DataT,
                       TAGS :: list string,
                       NAME :: string>;
      relation PEOPLE has
               schema <NAME :: string,
                       AGE :: nat>
    ]
    enforcing [attribute NAME for PHOTOS references PEOPLE].

Definition AlbumSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
           : unit                             -> rep,
      Method "AddPhoto"
           : rep x (AlbumSchema#PHOTOS)       -> rep x bool,
      Method "AddPerson"
           : rep x (AlbumSchema#PEOPLE)       -> rep x bool,
      Method "PhotosByAgeRange"
           : rep x (nat * nat)                -> rep x list (AlbumSchema#PHOTOS),
      Method "PhotosByTags"
           : rep x list string                -> rep x list (AlbumSchema#PHOTOS)
    }.

Definition AlbumSpec : ADT AlbumSig :=
  QueryADTRep AlbumSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddPhoto" (photo : AlbumSchema#PHOTOS) : bool :=
      Insert photo into PHOTOS,

    update "AddPerson" (person : AlbumSchema#PEOPLE) : bool :=
      Insert person into PEOPLE,

    query "PhotosByAgeRange" (range : nat * nat) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          (person in PEOPLE)
          Where (person!NAME = photo!NAME)
          Where (InRange person!AGE range)
          Return photo,
          
    query "PhotosByTags" (search_tags : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          Where (IncludedIn search_tags photo!TAGS)
          Return photo
}.

Definition SharpenedAlbum :
  Sharpened AlbumSpec.
Proof.
  unfold AlbumSpec.

  start honing QueryStructure.

  make simple indexes using [[(EqualityIndex, NAME); (InclusionIndex, TAGS)]; [(RangeIndex, AGE)]].

  hone constructor "Init".
  { initializer. }

  hone method "PhotosByTags".
  { observer. }

  hone method "PhotosByAgeRange".
  { observer. }

  hone method "AddPhoto".
  { insertion. }

  hone method "AddPerson".
  { insertion. }

  FullySharpenQueryStructure AlbumSchema Index.

  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.

Time Defined.