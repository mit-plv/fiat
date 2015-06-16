Require Import Coq.Strings.String.
Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Automation.IndexSelection.

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
Require Import Fiat.QueryStructure.Specification.SearchTerms.ListInclusion.

Definition SharpenedMessages :
  FullySharpened MessagesSpec.
Proof.

  start_honing_QueryStructure.

  { GenerateIndexesForAll ltac:(CombineCase3 matchInclusionIndex matchEqIndex)
                                 ltac:(fun attrList =>
                                         make simple indexes using attrList).
     initializer.
      insertion ltac:(CombineCase5 InclusionIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyInclusionTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastInclusionTerm createLastEqualityTerm)
                           ltac:(CombineCase7 InclusionIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastInclusionTerm_dep createLastEqualityTerm_dep).
      insertion ltac:(CombineCase5 InclusionIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyInclusionTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastInclusionTerm createLastEqualityTerm)
                           ltac:(CombineCase7 InclusionIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastInclusionTerm_dep createLastEqualityTerm_dep).
      observer ltac:(CombineCase5 InclusionIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyInclusionTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastInclusionTerm createLastEqualityTerm)
                           ltac:(CombineCase7 InclusionIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastInclusionTerm_dep createLastEqualityTerm_dep).
      observer ltac:(CombineCase5 InclusionIndexUse EqIndexUse)
             ltac:(CombineCase10 createEarlyInclusionTerm createEarlyEqualityTerm)
                    ltac:(CombineCase7 createLastInclusionTerm createLastEqualityTerm)
                           ltac:(CombineCase7 InclusionIndexUse_dep EqIndexUse_dep)
                                  ltac:(CombineCase11 createEarlyInclusionTerm_dep createEarlyEqualityTerm_dep)
                                         ltac:(CombineCase8 createLastInclusionTerm_dep createLastEqualityTerm_dep).
      pose_headings_all.

     match goal with
     | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
       FullySharpenQueryStructure Schema Indexes
     end.
  }

  { simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms.
    BuildQSIndexedBags'. }
  higher_order_reflexivityT.

Time Defined.

  (* With the standard indexes, 'RelevantMessages' enumerates and filters. *)
  partial_master_plan EqIndexTactics.
  Undo 1.

  (* Using search terms for checking IncludedIn uses the more efficient BFind method. *)


  partial_master_plan ltac:(CombineIndexTactics InclusionIndexTactics EqIndexTactics).

  FullySharpenQueryStructure MessagesSchema Index.

Time Defined.

Definition MessagesImpl : SharpenedUnderDelegates MessagesSig.
  Time let Impl := eval simpl in (projT1 SharpenedMessages) in
           exact Impl.
Defined.
