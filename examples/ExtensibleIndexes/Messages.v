Require Import Coq.Strings.String.
Require Import ADTSynthesis.QueryStructure.Automation.AutoDB
        ADTSynthesis.QueryStructure.Automation.IndexSelection
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListInclusion.

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

    update "AddMessage" (message : MessagesSchema#MESSAGES) : bool :=
      Insert message into MESSAGES,

    update "AddContact" (contact : MessagesSchema#CONTACTS) : bool :=
      Insert contact into CONTACTS,

    query "ContactMessages" (name : string) : list MessageT :=
      For (contact in CONTACTS)
          (messages in MESSAGES)
          Where (contact!NAME = name)
          Where (messages!PHONE_NUMBER = contact!PHONE_NUMBER)
          Return messages!MESSAGE,

     query "RelevantMessages" (search_terms : list string) : list MessageT :=
       For (message in MESSAGES)
           Where (IncludedIn search_terms message!MESSAGE)
           Return message!MESSAGE

}.

Definition SharpenedMessages :
  Sharpened MessagesSpec.
Proof.

  unfold MessagesSpec.

  start honing QueryStructure.

  Ltac matchInclusionClause WhereClause k :=
    match WhereClause with
      | fun tups => IncludedIn _ (@?C1 tups) =>
        let attrs1 := TermAttributes C1 in
        k (map (fun a12 => (InclusionIndex, (fst a12, snd a12)))
               (attrs1))
    end.


  Ltac matchPrefixClause WhereClause k :=
    match WhereClause with
      | fun tups => IsPrefix (@?C1 tups) _ =>
        let attrs1 := TermAttributes C1 in
        k (map (fun a12 => (FindPrefixIndex, (fst a12, snd a12)))
               (attrs1))
    end.

  GenerateIndexesForAll ltac:(fun W k => match goal with
                                           | _ => matchInclusionClause W k
                                           | _ => matchPrefixClause W k end)
                               ltac:(fun l => make simple indexes using l).

(*
  make simple indexes using [[(EqualityIndex, PHONE_NUMBER); (InclusionIndex, MESSAGE)]; [(EqualityIndex, NAME); (UnIndex, NAME)]].
 *)

  plan.

  FullySharpenQueryStructure MessagesSchema Index.

  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.
  implement_bag_methods.

Time Defined.

Definition MessagesImpl : SharpenedUnderDelegates MessagesSig.
  Time let Impl := eval simpl in (projT1 SharpenedMessages) in
           exact Impl.
Defined.
