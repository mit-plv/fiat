Require Import Fiat.QueryStructure.Automation.MasterPlan.

Definition MESSAGES := "Messages".
Definition CONTACTS := "Contacts".

Definition PHONE_NUMBER := "PhoneNumber".
Definition TIME := "Time".
Definition MESSAGE := "Message".
Definition NAME := "Name".

Definition MessageT := list string.

Definition MessagesSchema :=
  Query Structure Schema
    [ relation MESSAGES has
              schema <PHONE_NUMBER :: nat,
                      TIME :: nat,
                      MESSAGE :: MessageT>;
      relation CONTACTS has
              schema <PHONE_NUMBER :: nat,
                      NAME :: string>
                      where attributes [NAME] depend on [PHONE_NUMBER]
    ]
    enforcing [attribute PHONE_NUMBER for MESSAGES references CONTACTS].

Definition MessagesSig : ADTSig :=
  ADTsignature {
      Constructor "Init"
           : rep,
      Method "AddMessage"
           : rep * (MessagesSchema#MESSAGES)  -> rep * bool,
      Method "AddContact"
           : rep * (MessagesSchema#CONTACTS) -> rep * bool,
      Method "ContactMessages"
           : rep * string                     -> rep * (list MessageT),
      Method "RelevantMessages"
           : rep * (list string)                -> rep * (list MessageT)
    }.

Definition MessagesSpec : ADT MessagesSig :=
  QueryADTRep MessagesSchema {
    Def Constructor0 "Init" : rep := empty,

    Def Method1 "AddMessage" (r : rep) (message : MessagesSchema#MESSAGES) : rep * bool :=
      Insert message into r ! MESSAGES,

    Def Method1 "AddContact" (r : rep) (contact : MessagesSchema#CONTACTS) : rep * bool :=
      Insert contact into r ! CONTACTS,

    Def Method1 "ContactMessages" (r : rep) (name : string) : rep * list MessageT :=
      msgs <- For (contact in r ! CONTACTS)
           (messages in r ! MESSAGES)
           Where (contact!NAME = name)
           Where (messages!PHONE_NUMBER = contact!PHONE_NUMBER)
           Return messages!MESSAGE;
    ret (r, msgs),

     Def Method1 "RelevantMessages" (r : rep) (search_terms : list string) : rep * list MessageT :=
      msgs <- For (message in r ! MESSAGES)
           Where (IncludedIn search_terms message!MESSAGE)
           Return message!MESSAGE;
    ret (r, msgs)
              }%methDefParsing.

Definition SharpenedMessages :
  FullySharpened MessagesSpec.
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
  - hone representation using (@FiniteTables_AbsR MessagesSchema).
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

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics). *)
  master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics).

Time Defined.
(* 1336MB *)
Time Definition MessagesImpl : ComputationalADT.cADT MessagesSig :=
  Eval simpl in (projT1 SharpenedMessages).
Print MessagesImpl.
