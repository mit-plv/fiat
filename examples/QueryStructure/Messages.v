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

  Unset Ltac Debug.
  unfold MessagesSpec.

  start honing QueryStructure.

  GenerateIndexesForAll matchInclusionClause ltac:(fun l => make simple indexes using l).

  hone method "RelevantMessages".
  {
    implement_Query InclusionIndexUse createLastInclusionTerm createEarlyInclusionTerm
      InclusionIndexUse_dep createLastInclusionTerm_dep createEarlyInclusionTerm_dep.  
    (* Do some more simplication using the monad laws. *)
    simpl; simplify with monad laws.
    (* Satisfied with the query, we now implement the new data
       representation (in this case, it is unchanged).
     *)
    simpl; commit.
    repeat setoid_rewrite filter_true;
      repeat setoid_rewrite app_nil_r;
      repeat setoid_rewrite map_length.
    finish honing.
  }

  hone method "ContactMessages".
  {
    implement_Query InclusionIndexUse createLastInclusionTerm createEarlyInclusionTerm
      InclusionIndexUse_dep createLastInclusionTerm_dep createEarlyInclusionTerm_dep.
    simpl; simplify with monad laws.
    simpl; commit.
    repeat setoid_rewrite filter_true;
      repeat setoid_rewrite app_nil_r;
      repeat setoid_rewrite map_length.
    finish honing.
  }

  hone constructor "Init".
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    simpl.
    finish honing.
  }

  hone method "AddMessage".
  {
    Implement_Insert_Checks.

    implement_Query.
    simpl; simplify with monad laws.
    setoid_rewrite refineEquiv_swap_bind.
    implement_Insert_branches.

    cleanup_Count.
    finish honing.
  }

  hone method "AddContact".
  {
    Implement_Insert_Checks.

    implement_Query.
    simpl; simplify with monad laws.
    setoid_rewrite refineEquiv_swap_bind.
    implement_Insert_branches.

    cleanup_Count.
    finish honing.
  }

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
