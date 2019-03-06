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
  Def ADT {
    rep := QueryStructure MessagesSchema,

    Def Constructor0 "Init" : rep := empty,,

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

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics). *)
  master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics).

Time Defined.
(* 1336MB *)
Time Definition MessagesImpl : ComputationalADT.cADT MessagesSig :=
  Eval simpl in (projT1 SharpenedMessages).
Print MessagesImpl.
