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
           : rep * (FriendFinderSchema#PEOPLE) -> rep * bool,
      Method "AddCity"
           : rep * (FriendFinderSchema#CITIES) -> rep * bool,
      Method "PeopleAround"
           : rep * string * nat              -> rep * (list string),
      Method "PeopleInCity"
           : rep * string                 -> rep * nat
    }.

Definition FriendFinderSpec : ADT _ :=
  Def ADT {
    rep := QueryStructure FriendFinderSchema,
    Def Constructor0 "Init"  : rep := empty,,

    Def Method1 "AddPerson" (r : rep) (person : FriendFinderSchema#PEOPLE) : rep * bool :=
      Insert person into r!PEOPLE,

    Def Method1 "AddCity" (r : rep) (city : FriendFinderSchema#CITIES) : rep * bool :=
      Insert city into r!CITIES,

    Def Method2 "PeopleAround" (r : rep) (name : string) (distance : nat) : rep * (list string) :=
        res <- For (person_me in r!PEOPLE)
          (person in r!PEOPLE)
          (city_me in r!CITIES)
          (city in r!CITIES)
          Where (person_me!NAME = name)
          Where (city_me!CITY = person_me!CITY)
          Where (city_me!LATITUDE - distance <=
                 city!LATITUDE <= city_me!LATITUDE + distance)
          Where (city_me!LONGITUDE - distance <=
                 city!LONGITUDE <= city_me!LONGITUDE + distance)
          Where (person!CITY = city!CITY)
          Return person!NAME;
    ret (r, res),

     Def Method1 "PeopleInCity" (r : rep) (city : string) : rep * nat :=
      res <- Count (For (person in r!PEOPLE)
                  Where (person!CITY = city)
                  Return ());
    ret (r, res)
}%methDefParsing.

Definition SharpenedFriendFinder :
  FullySharpened FriendFinderSpec.
Proof.
  start sharpening ADT.
  pose_string_hyps.
  eapply SharpenStep;
  [ match goal with
        |- context [@BuildADT (QueryStructure ?Rep) _ _ _ _ _ _] =>
        eapply refineADT_BuildADT_Rep_refine_All with (AbsR := @DropQSConstraints_AbsR Rep);
          [ repeat (first [eapply refine_Constructors_nil
                          | eapply refine_Constructors_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              (* Drop constraints from empty *)
                              try apply Constructor_DropQSConstraints;
                              cbv delta [GetAttribute] beta; simpl
                            | ] ])
          | repeat (first [eapply refine_Methods_nil
                          | eapply refine_Methods_cons;
                            [ simpl; intros;
                              match goal with
                              | |- refine _ (?E _ _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _ _) => let H := fresh in set (H := E)
                              | |- refine _ (?E _) => let H := fresh in set (H := E)
                              | |- refine _ (?E) => let H := fresh in set (H := E)
                              | _ => idtac
                              end;
                              cbv delta [GetAttribute] beta; simpl | ]
                          ])]
    end | ].
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
           master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - hone representation using (@FiniteTables_AbsR FriendFinderSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
             Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + simpl.

  master_plan ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics).
Time Defined.

Time Definition FriendFinderImpl : ComputationalADT.cADT FriendFinderSig :=
  Eval simpl in (projT1 SharpenedFriendFinder).
Print FriendFinderImpl.
