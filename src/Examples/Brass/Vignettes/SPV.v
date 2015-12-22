(****************************************************************************)
(* NOTES on the Simple Parser Vignette (SPV)                                *)
(*                                                                          *)
(* After talking with Ben, it seems that the way to proceed here is to      *)
(* break this up into four aspects:                                         *)
(*                                                                          *)
(* 1. Parse, using a parser generated from a BNF spec, from a string to a   *)
(*    constrained multiset. The constraints state which properties must     *)
(*    hold over the entire multiset between any two contiguous points in    *)
(*    time (i.e., where there is no intervening point).                     *)
(*                                                                          *)
(*    Ben stresses we should never think about efficiency or resources at   *)
(*    this level, only what gives the clearest mathematical model. So, we   *)
(*    don't apply constraints between individual points, but rather between *)
(*    any two time-contiguous points over the whole multiset; and we don't  *)
(*    test each constraint "as we parse", but only state them as properties *)
(*    of the whole multiset.                                                *)
(*                                                                          *)
(* 2. Fiat provides a query architecture for working with multisets, which  *)
(*    is why we choose that model in particular.                            *)
(*                                                                          *)
(* 3. In the "insertPoint" method of our Query Spec, we express the only    *)
(*    sequence dependent constraint: that points must arrive in ascending   *)
(*    order of time, or else the parse fails.                               *)
(*                                                                          *)
(* 4. Once we have built up our constrained multiset, we "query" it for its *)
(*    computed sum, stated simply as a sum over its point distances, using  *)
(*    Fiat's SQL-like query language.                                       *)
(*                                                                          *)
(* See simple-parser-spec.txt for a description of what is encoded here.    *)
(****************************************************************************)

Require Import Fiat.Parsers.ContextFreeGrammar.Notations.

(****************************************************************************)
(* Grammar for parsing SPV data                                             *)
(*                                                                          *)
(* Basically these are lines of the following form:                         *)
(*    <time in seconds> <latitude> <longituted><NEWLINE>                    *)
(*                                                                          *)
(* jww (2015-12-20): Until I figure out how to represent NEWLINE in Fiat    *)
(* grammars, I'm using a colon (:).                                         *)
(****************************************************************************)

Definition spv_grammar : grammar ascii :=
  [[[ ("expr"   ::== << $< "coords" >$
                      | $< "coords" $ #":" $ "expr" >$ >>) ;;
      ("coords" ::== << $< "nat" $ #" " $ "float" $ #" " $ "float" >$ >>) ;;
      ("digit"  ::== << $< #"0" >$ | $< #"1" >$ | $< #"2" >$ | $< #"3" >$
                      | $< #"4" >$ | $< #"5" >$ | $< #"6" >$ | $< #"7" >$
                      | $< #"8" >$ | $< #"9" >$ >>) ;;
      ("nat"    ::== << $< "digit" >$
                      | $< "digit" $ "nat" >$ >>) ;;
      ("dotted" ::== << $< "nat" $ #"." $ "nat" >$ >>) ;;
      ("float"  ::== << $< "dotted" >$
                      | $< #"-" $ "dotted" >$ >>)
  ]]]%grammar.

(****************************************************************************)
(* Helper function to express SPV data constraints                          *)
(****************************************************************************)

Require Import Coq.Reals.Reals.

Definition time_point := R.
Definition time_delta := R. (* aka, time_duration *)
Definition coord_point := R.
Definition coord_delta := R.

Open Scope R_scope.

Definition distance (x y : coord_point) : coord_delta := y - x.

Definition manhattan_distance (x1 y1 x2 y2 : coord_point) : coord_point :=
  (y2 - y1) + (x2 - x1).

(* Use a Polar Coordinate Flat-Earth model, because the distances are
   human-scale. Results is given in meters. *)
Definition great_circle_distance (lat1 lon1 lat2 lon2 : R) : R :=
  let a := PI/2 - lat1 in
  let b := PI/2 - lat2 in
  let c := sqrt (a^2 + b^2 - 2 * a * b * cos(lon2 - lon1)) in
  let radiusOfEarth : R := 6371000 in
  radiusOfEarth * c.

Definition speed_mph (time1 lat1 lon1 time2 lat2 lon2 : R) : R :=
  let diff_secs := time2 - time1 in
  let dist_meters := great_circle_distance lat1 lon1 lat2 lon2 in
  let meters_to_feet m := m * (328084 / 100000) in
  let feet_to_miles f := f / 5280 in
  let secs_to_hours s := s / 3600 in
  feet_to_miles (meters_to_feet dist_meters) / secs_to_hours diff_secs.

(****************************************************************************)
(* Query structure for storing time series points                           *)
(*                                                                          *)
(* This structure has two types of constraints: One that appplies globally  *)
(* over the entire multiset, and one that is applied by decision whenever a *)
(* new point is to be inserted.                                             *)
(****************************************************************************)

Require Import Fiat.QueryStructure.Automation.MasterPlan.
Require Import Fiat.QueryStructure.Specification.Representation.Notations.

Definition sPOINTS        := "Points".
Definition sPOINT_TIME    := "point_time".
Definition sPOINT_LAT     := "point_lat".
Definition sPOINT_LON     := "point_lon".

Definition SPVSchema := Query Structure Schema
  [ relation sPOINTS has
    schema < sPOINT_TIME :: time_point
           , sPOINT_LAT  :: coord_point
           , sPOINT_LON  :: coord_point >
    where
      (fun p p' =>
         let tm   :=  p!sPOINT_TIME in
         let tm'  := p'!sPOINT_TIME in
         let lat  :=  p!sPOINT_LAT in
         let lat' := p'!sPOINT_LAT in
         let lon  :=  p!sPOINT_LON in
         let lon' := p'!sPOINT_LON in
         (* constraint on every pair of time consecutive points:
            distance traveled is >= 0, and is within human norms *)
         Rlt tm tm' -> Rle 0 (manhattan_distance lat lon lat' lon')
                    /\ Rgt 6 (speed_mph tm lat lon tm' lat' lon')
                    /\ (attributes [sPOINT_LAT; sPOINT_LON]
                         depend on [sPOINT_TIME]) p p')
  ] enforcing [ ].

Definition SPVSig : ADTSig := ADTsignature {
  Constructor "Init"    : rep,
  Method "insertPoint"  : rep * time_point * coord_point * coord_point
                       -> rep * bool,
  Method "sumDistances" : rep
                       -> rep * (option R)
}.

Fixpoint insert {a} (P : a -> a -> bool) (z : a) (l : list a) : list a :=
  match l with
  | x :: xs => if P x z
               then x :: insert P z xs
               else z :: x :: xs
  | _ => [z]
  end.
Arguments insert {a} P z l : simpl never.

Fixpoint sortBy {a} (p : a -> a -> bool) (l : list a) : list a :=
  match l with
  | [] => nil
  | x :: xs => insert p x (sortBy p xs)
  end.

Definition fst_of_three `(x : a * b * c) : a := match x with (a, b, c) => a end.

Require Import Coq.Reals.ROrderedType.

Definition comparing_times (x y : time_point) :=
  match Rcompare x y with
  | Lt => true
  | _  => false
  end.

Definition comparing_coords (x y : time_point * coord_point * coord_point) :=
  comparing_times (fst_of_three x) (fst_of_three y).

Definition compute_total_distance
  (acc : option (R * coord_point * coord_point))
  (x : time_point * coord_point * coord_point) :=
  match x with
    (moment, lat, lon) =>
      match acc with
      | Some (thus_far, prev_lat, prev_long) =>
          let dist := manhattan_distance prev_lat prev_long lat lon in
          Some (thus_far + dist, lat, lon)
      | None => Some (0, lat, lon)
      end
  end.

Definition SPVSpec : ADT _ := QueryADTRep SPVSchema {
  Def Constructor0 "Init" : rep := empty,

  Def Method3 "insertPoint"
    (r : rep) (moment : time_point) (lat : coord_point) (lon : coord_point)
    : rep * bool
    := ps <- For (p in r!sPOINTS) Return (p!sPOINT_TIME);
       (* Ensure the most recent time we've thus seen is less recent than the
          new point to be inserted. *)
       If comparing_times (fold_left Rmax ps 0) moment
       Then Insert < sPOINT_TIME::moment
                   , sPOINT_LAT::lat
                   , sPOINT_LON::lon > into r!sPOINTS
       Else ret (r, false),

  (* Although the method [sumDistances] is ordering independent, it is still
     important to ensure that incoming data is order dependent, since
     otherwise we incur the additional requirement of needing *all* data
     before being able to give a reliable track length. If data is properly
     ordered, the user can meaningfully ask for the "running total" as data is
     received by the system. By making [sumDistances] order independent, we do
     not require either proofs or runtime logic to implement a functionally
     correct algorithm with regard to the meaning of "sum total distance". *)
  Def Method0 "sumDistances"
    (r : rep) : rep * option R
    := res <- For (p in r!sPOINTS)
              Return (p!sPOINT_TIME, p!sPOINT_LAT, p!sPOINT_LON);
       match fold_left compute_total_distance
                       (sortBy comparing_coords res) None with
       | None => ret (r, None)
       | Some (acc, _, _) => ret (r, Some acc)
       end

}%methDefParsing.

(****************************************************************************)
(* TODO: jww (2015-12-21): The open question now is how to tie the output   *)
(* of the parser (a sequence of time-located points) to the input of the    *)
(* multiset (a collection of such points).                                  *)
(****************************************************************************)

(****************************************************************************)
(* End of SPV.v                                                             *)
(****************************************************************************)
