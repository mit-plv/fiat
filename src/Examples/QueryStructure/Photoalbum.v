Require Import Coq.Strings.String.
Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.QSImplementation.

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
          Where (fst range <= event!DATE <= snd range)
          Return photo,

    query "PhotosByPersons" (r : rep, persons : list string) : list (AlbumSchema#PHOTOS) :=
      For (photo in r!PHOTOS)
          Where (IncludedIn persons photo!PERSONS)
          Return photo
}.

Definition SharpenedAlbum :
  FullySharpened AlbumSpec.
Proof.

  start honing QueryStructure.

  {
  (* Manually select indexes + data structure. *)
let attrList := constr:(icons3 (B := fun heading => list (prod string (Attributes (rawSchemaHeading heading)))) (a := Vector.hd (qschemaSchemas AlbumSchema)) [("EqualityIndex", Fin.FS (Fin.FS (@Fin.F1 0))); ("InclusionIndex", Fin.FS (@Fin.F1 1))] (icons3 (a := Vector.hd (Vector.tl (qschemaSchemas AlbumSchema))) [("EqualityIndex", @Fin.F1 1); ("RangeIndex", Fin.FS (@Fin.F1 0))] inil3)) in
make_simple_indexes attrList
  ltac:(CombineCase6 BuildEarlyEqualityIndex
                     ltac:(CombineCase6 BuildEarlyRangeIndex
                                        ltac:(fun _ _ _ _ _ _ => fail)))
         ltac:(CombineCase5 BuildLastEqualityIndex
                            ltac:(CombineCase5

                                    BuildLastInclusionIndex ltac:(CombineCase5 BuildLastRangeIndex
                                                                               ltac:(fun _ _ _ _ _ => fail)))).

    - initializer.
    - insertion ltac:(CombineCase5 InclusionIndexUse ltac:(CombineCase5 RangeIndexUse EqIndexUse))
             ltac:(CombineCase10 createEarlyInclusionTerm ltac:(CombineCase10 createEarlyRangeTerm createEarlyEqualityTerm))
                    ltac:(CombineCase7 createLastInclusionTerm ltac:(CombineCase7 createLastRangeTerm createLastEqualityTerm))
                           ltac:(CombineCase7 InclusionIndexUse_dep ltac:(CombineCase7 RangeIndexUse_dep EqIndexUse_dep))
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep ltac:(CombineCase11 createEarlyRangeTerm_dep createEarlyEqualityTerm_dep))
                                         ltac:(CombineCase8 createLastInclusionTerm_dep ltac:(CombineCase8 createLastRangeTerm_dep createLastEqualityTerm_dep)).
    - insertion ltac:(CombineCase5 InclusionIndexUse ltac:(CombineCase5 RangeIndexUse EqIndexUse))
             ltac:(CombineCase10 createEarlyInclusionTerm ltac:(CombineCase10 createEarlyRangeTerm createEarlyEqualityTerm))
                    ltac:(CombineCase7 createLastInclusionTerm ltac:(CombineCase7 createLastRangeTerm createLastEqualityTerm))
                           ltac:(CombineCase7 InclusionIndexUse_dep ltac:(CombineCase7 RangeIndexUse_dep EqIndexUse_dep))
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep ltac:(CombineCase11 createEarlyRangeTerm_dep createEarlyEqualityTerm_dep))
                                         ltac:(CombineCase8 createLastInclusionTerm_dep ltac:(CombineCase8 createLastRangeTerm_dep createLastEqualityTerm_dep)).
    - observer ltac:(CombineCase5 InclusionIndexUse ltac:(CombineCase5 RangeIndexUse EqIndexUse))
             ltac:(CombineCase10 createEarlyInclusionTerm ltac:(CombineCase10 createEarlyRangeTerm createEarlyEqualityTerm))
                    ltac:(CombineCase7 createLastInclusionTerm ltac:(CombineCase7 createLastRangeTerm createLastEqualityTerm))
                           ltac:(CombineCase7 InclusionIndexUse_dep ltac:(CombineCase7 RangeIndexUse_dep EqIndexUse_dep))
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep ltac:(CombineCase11 createEarlyRangeTerm_dep createEarlyEqualityTerm_dep))
                                         ltac:(CombineCase8 createLastInclusionTerm_dep ltac:(CombineCase8 createLastRangeTerm_dep createLastEqualityTerm_dep)).
    - observer ltac:(CombineCase5 InclusionIndexUse ltac:(CombineCase5 RangeIndexUse EqIndexUse))
             ltac:(CombineCase10 createEarlyInclusionTerm ltac:(CombineCase10 createEarlyRangeTerm createEarlyEqualityTerm))
                    ltac:(CombineCase7 createLastInclusionTerm ltac:(CombineCase7 createLastRangeTerm createLastEqualityTerm))
                           ltac:(CombineCase7 InclusionIndexUse_dep ltac:(CombineCase7 RangeIndexUse_dep EqIndexUse_dep))
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep ltac:(CombineCase11 createEarlyRangeTerm_dep createEarlyEqualityTerm_dep))
                                         ltac:(CombineCase8 createLastInclusionTerm_dep ltac:(CombineCase8 createLastRangeTerm_dep createLastEqualityTerm_dep)).
    - pose_headings_all.

     match goal with
     | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
       FullySharpenQueryStructure Schema Indexes
     end.
     }

  { simpl; pose_string_ids; pose_headings_all;
    pose_search_term; pose_SearchUpdateTerms.

BuildQSIndexedBags' ltac:(CombineCase6 BuildEarlyRangeTreeBag BuildEarlyEqualityBag)
                        ltac:(CombineCase5 BuildLastInclusionIndexBag
                                           ltac:(CombineCase5 BuildLastRangeTreeBag BuildLastEqualityBag)).
  }
  higher_order_reflexivityT.

Time Defined.
