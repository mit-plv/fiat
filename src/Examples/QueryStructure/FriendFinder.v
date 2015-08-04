Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition PEOPLE := "People".
Definition CITIES := "Cities".
Definition FRIENDSHIPS := "Friendship".

Definition NAME := "Name".
Definition CITY := "City".
Definition LATITUDE := "Latitude".
Definition LONGITUDE := "Longitude".

Definition FriendFinderSchema :=
  Query Structure Schema
    [ relation PEOPLE has
              schema <NAME :: string,
                      CITY :: string>;
      relation CITIES has
              schema <CITY :: string,
                      LATITUDE :: nat,
                      LONGITUDE :: nat>
    ]
    enforcing [attribute CITY for PEOPLE references CITIES].

Definition FriendFinderSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
           : unit                              -> rep,
      Method "AddPerson"
           : rep x (FriendFinderSchema#PEOPLE) -> rep x bool,
      Method "AddCity"
           : rep x (FriendFinderSchema#CITIES) -> rep x bool,
      Method "PeopleAround"
           : rep x (string * nat)              -> rep x list string,
      Method "PeopleInCity"
           : rep x string                 -> rep x nat
    }.

Definition FriendFinderSpec : ADT FriendFinderSig :=
  QueryADTRep FriendFinderSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddPerson" (r : rep, person : FriendFinderSchema#PEOPLE) : bool :=
      Insert person into r!PEOPLE,

    update "AddCity" (r : rep, city : FriendFinderSchema#CITIES) : bool :=
      Insert city into r!CITIES,

    query "PeopleAround" (r : rep, name_distance : string * nat) : list string :=
      For (person_me in r!PEOPLE)
          (person in r!PEOPLE)
          (city_me in r!CITIES)
          (city in r!CITIES)
          Where (person_me!NAME = (fst name_distance))
          Where (city_me!CITY = person_me!CITY)
          Where (city_me!LATITUDE - (snd name_distance) <=
                 city!LATITUDE <= city_me!LATITUDE + (snd name_distance))
          Where (city_me!LONGITUDE - (snd name_distance) <=
                 city!LONGITUDE <= city_me!LONGITUDE + (snd name_distance))
          Where (person!CITY = city!CITY)
          Return person!NAME,
          
     query "PeopleInCity" (r : rep, city : string) : nat :=
       Count (For (person in r!PEOPLE)
                  Where (person!CITY = city)
                  Return ())
}.

Definition SharpenedFriendFinder :
  FullySharpened FriendFinderSpec.
Proof.
  master_plan ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics).
Time Defined.

Time Definition FriendFinderImpl : ComputationalADT.cADT FriendFinderSig :=
  Eval simpl in (projT1 SharpenedFriendFinder).
Print FriendFinderImpl.