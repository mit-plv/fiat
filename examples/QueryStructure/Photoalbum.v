Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Automation.IndexSelection
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListInclusion
        ADTSynthesis.QueryStructure.Specification.SearchTerms.InRange.

(* Collection of Photos. Each photo contains the owner, the list of tags, and
   the geolocation (latitude and longitude) *)

Definition PHOTOS := "Album".
Definition USERS := "Users".

Definition USER_ID := "UserId".
Definition IMAGE_DATA := "ImageData".
Definition TAGS := "Tags".
Definition LATITUDE := "Latitude".
Definition LONGITUDE := "Longitude".
Definition NAME := "Name".

(* Represents image data by a list of byte characters *)
Definition DataT := list ascii.

(* Represents a natural number range by a pair of natural numbers *)
Definition NatRange := prod nat nat.

Definition AlbumSchema :=
  Query Structure Schema
    [ relation PHOTOS has
               schema <USER_ID :: nat,
                       IMAGE_DATA :: DataT,
                       TAGS :: list string,
                       LATITUDE :: nat,
                       LONGITUDE :: nat>;
      relation USERS has
               schema <USER_ID :: nat,
                       NAME :: string>
                       where attributes [NAME] depend on [USER_ID]
    ]
    enforcing [attribute USER_ID  for PHOTOS references USERS].

Definition AlbumSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
           : unit                             -> rep,
      Method "AddPhoto"
           : rep x (AlbumSchema#PHOTOS)       -> rep x bool,
      Method "AddUser"
           : rep x (AlbumSchema#USERS)        -> rep x bool,
      Method "PhotosByLocation"
           : rep x (NatRange * NatRange)      -> rep x list (AlbumSchema#PHOTOS),
      Method "PhotosByTags"
           : rep x list string                -> rep x list (AlbumSchema#PHOTOS),
      Method "PhotosByUploader"
           : rep x string                     -> rep x list (AlbumSchema#PHOTOS)
    }.

Definition AlbumSpec : ADT AlbumSig :=
  QueryADTRep AlbumSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddPhoto" (photo : AlbumSchema#PHOTOS) : bool :=
      Insert photo into PHOTOS,

    update "AddUser" (user : AlbumSchema#USERS) : bool :=
      Insert user into USERS,

    query "PhotosByLocation" (ranges : NatRange * NatRange) : list (AlbumSchema#PHOTOS) :=
      (* let (range_latitude, range_longitude) := ranges in *)
      For (photo in PHOTOS)
          Where (InRange photo!LATITUDE (fst ranges) /\
                 InRange photo!LONGITUDE (snd ranges))
          Return photo,
          
    query "PhotosByTags" (search_tags : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in PHOTOS)
          Where (IncludedIn search_tags photo!TAGS)
          Return photo,

    query "PhotosByUploader" (uploader : string) : list (AlbumSchema#PHOTOS) :=
      For (user in USERS)
          (photo in PHOTOS)
          Where (user!NAME = uploader)
          Where (photo!USER_ID = user!USER_ID)
          Return photo
}.

Definition SharpenedAlbum :
  Sharpened AlbumSpec.
Proof.
  unfold AlbumSpec.

  start honing QueryStructure.

  make simple indexes using [[(RangeIndex, LATITUDE)]; [(EqualityIndex, NAME)]].

  hone constructor "Init".
  { initializer. }

  hone method "PhotosByLocation".
  { observer. }
    
  hone method "PhotosByTags".
  { observer. }

  hone method "PhotosByUploader".
  { observer. }

  hone method "AddPhoto".
  { insertion. }

  hone method "AddUser".
  { insertion. }


  FullySharpenQueryStructure AlbumSchema Index.

  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.

Time Defined.