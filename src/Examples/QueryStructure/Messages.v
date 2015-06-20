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
           : unit                             -> rep,
      Method "AddMessage"
           : rep x (MessagesSchema#MESSAGES)  -> rep x bool,
      Method "AddContact"
           : rep x (MessagesSchema#CONTACTS) -> rep x bool,
      Method "ContactMessages"
           : rep x string                     -> rep x list MessageT,
      Method "RelevantMessages"
           : rep x list string                -> rep x list MessageT
    }.

Definition MessagesSpec : ADT MessagesSig :=
  QueryADTRep MessagesSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "AddMessage" (r : rep, message : MessagesSchema#MESSAGES) : bool :=
      Insert message into r ! MESSAGES,

    update "AddContact" (r : rep, contact : MessagesSchema#CONTACTS) : bool :=
      Insert contact into r ! CONTACTS,

    query "ContactMessages" (r : rep, name : string) : list MessageT :=
      For (contact in r ! CONTACTS)
          (messages in r ! MESSAGES)
          Where (contact!NAME = name)
          Where (messages!PHONE_NUMBER = contact!PHONE_NUMBER)
          Return messages!MESSAGE,

     query "RelevantMessages" (r : rep, search_terms : list string) : list MessageT :=
       For (message in r ! MESSAGES)
           Where (IncludedIn search_terms message!MESSAGE)
           Return message!MESSAGE

}.

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
