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

  start sharpening ADT.
  start_honing_QueryStructure'.
  Unset Ltac Debug.
  GenerateIndexesForAll
    ltac:((InRangeExpressionAttributeCounter
             ltac:(IncludedInExpressionAttributeCounter
             EqExpressionAttributeCounter)))
           ltac:(fun attrlist =>
                   let attrlist' := eval compute in (PickIndexes (CountAttributes' attrlist)) in
                   pose attrlist').
  pose ({|
       prim_fst := [
                    ("EqualityIndex", Fin.FS (Fin.FS Fin.F1));
                    ("InclusionIndex", Fin.FS Fin.F1)];
       prim_snd := {|
                   prim_fst := [("EqualityIndex", Fin.F1);
                               ("RangeIndex", Fin.FS Fin.F1)];
                   prim_snd := () |} |}
    : prim_prod (list (string * Fin.t 3))
        (prim_prod (list (string * Fin.t 2)) ())).

  let attrlist' := eval unfold p0 in p0 in
      make_simple_indexes attrlist'
                          ltac:(CombineCase6 BuildEarlyInclusionIndex
                                             ltac:(CombineCase6 BuildEarlyRangeIndex
                           ltac:(LastCombineCase6 BuildEarlyEqualityIndex)))
                                 ltac:(CombineCase5 BuildLastInclusionIndex
                                                    ltac:(CombineCase5 BuildLastRangeIndex
                                  ltac:(CombineCase5  BuildLastRangeIndex ltac:(LastCombineCase5 BuildLastEqualityIndex)))).


  Unset Ltac Debug.


  Unset Ltac Debug.
  repeat eapply @ExpressionAttributeCounterConstructorsCons; intros.
    psearch 200 ltac:(psearch_combine
            InRangeExpressionAttributeCounter
            ltac:(psearch_combine
                    IncludedInExpressionAttributeCounter
                    EqExpressionAttributeCounter)) ().
  repeat eapply @ExpressionAttributeCounterMethodsCons; intros.
  Focus 4.
  repeat eapply @ExpressionAttributeCounterBind; intros.
  eapply @ExpressionAttributeCounterFor.
  eapply @ExpressionAttributeCounterQueryIn; intros.
  eapply @ExpressionAttributeCounterWhere; intros.
Instance ExpressionAttributeCounterIncludedIn {A }
         {qsSchema : RawQueryStructureSchema}
         {a}
         {a' : list A}
         (RidxL : Fin.t _)
         (BAidxL : @Attributes (Vector.nth _ RidxL))
         (ExpCountL : @TermAttributeCounter _ qsSchema a' RidxL BAidxL)
  : @ExpressionAttributeCounter _ qsSchema (IncludedIn a a')
                                (@InsertOccurenceOfAny _ _ RidxL (InclusionIndex, BAidxL)
                                                       (InitOccurences _)) | 0 := { }.

  eapply ExpressionAttributeCounterIncludedIn.
  psearch 200 ltac:(InRangeExpressionAttributeCounter
            ltac:(
                    IncludedInExpressionAttributeCounter
                      EqExpressionAttributeCounter)) ().
    psearch 200 ltac:(InRangeExpressionAttributeCounter
            ltac:(
                    IncludedInExpressionAttributeCounter
                    EqExpressionAttributeCounter)) ().
  psearch 200 ltac:(InRangeExpressionAttributeCounter
            ltac:(
                    IncludedInExpressionAttributeCounter
                    EqExpressionAttributeCounter)) ().
  Focus 5.
  eapply @ExpressionAttributeCounterWhere; intros.
  psearch 200 ltac:(InRangeExpressionAttributeCounter
                      ltac:(IncludedInExpressionAttributeCounter
                           EqExpressionAttributeCounter)) ().
psearch 200 ltac:(psearch_combine
            InRangeExpressionAttributeCounter
            ltac:(psearch_combine
                    IncludedInExpressionAttributeCounter
                    EqExpressionAttributeCounter)) ().
psearch 200 ltac:(psearch_combine
            InRangeExpressionAttributeCounter
            ltac:(psearch_combine
                    IncludedInExpressionAttributeCounter
                    EqExpressionAttributeCounter)) ().
Focus 5.

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
