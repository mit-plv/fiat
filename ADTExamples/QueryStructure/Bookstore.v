Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation QueryStructureSchema
        BuildADTRefinements QueryQSSpecs InsertQSSpecs
        QueryStructure GeneralInsertRefinements ListInsertRefinements
        GeneralQueryRefinements ListQueryRefinements
        ProcessScheduler.AdditionalLemmas.

Section BookStoreExamples.

  (* Our bookstore has two relations (tables):
     - The [Books] relation contains the books in the
       inventory, represented as a tuple with
       [Author], [Title], and [ISBN] attributes.
       The [ISBN] attribute is a key for the relation,
       specified by the [where attributes .. depend on ..]
       constraint.
     - The [Orders] relation contains the orders that
       have been placed, represented as a tuple with the
       [ISBN] and [Date] attributes.

     The schema for the entire query structure specifies that
     the [ISBN] attribute of [Orders] is a foreign key into
     [Books], specified by the [attribute .. of .. references ..]
     constraint.
   *)

  Open Scope QSSchema.

  Definition BookStoreSchema :=
    query structure schema
      [ relation "Books" has
                schema <"Author" :: string,
                        "Title" :: string,
                        "ISBN" :: nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" :: nat,
                        "Date" :: nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"].

  Definition Books := GetRelationKey BookStoreSchema "Books".
  Definition Orders := GetRelationKey BookStoreSchema "Orders".

  Definition Author := GetAttributeKey Books "Author".
  Definition Title := GetAttributeKey Books "Title".
  Definition ISBN := GetAttributeKey Books "ISBN".

  Definition oISBN := GetAttributeKey Orders "ISBN".
  Definition Date := GetAttributeKey Orders "Date".

  Definition BookStoreRefRep := QueryStructure BookStoreSchema.

  Definition BookSchemaHeading :=
    QSGetNRelSchemaHeading BookStoreSchema Books.
  Definition OrderSchemaHeading :=
    QSGetNRelSchemaHeading BookStoreSchema Orders.

  Definition Book := @Tuple BookSchemaHeading.
  Definition Order := @Tuple OrderSchemaHeading.

  (* Our bookstore has two mutators:
     - [PlaceOrder] : Place an order into the 'Orders' table
     - [AddBook] : Add a book to the inventory

     Our bookstore has two observers:
     - [GetTitles] : The titles of books written by a given author
     - [NumOrders] : The number of orders for a given author
   *)

  Local Open Scope ADTSig_scope.
  Local Open Scope QueryStructureParsing_scope.
  Local Open Scope Schema.
  Local Open Scope QuerySpec.
  Local Open Scope string.

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "PlaceOrder" : rep × Order → rep,
        "AddBook" : rep × Book → rep ;
        "GetTitles" : rep × string → list string,
        "NumOrders" : rep × string → nat
      }.

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreRefRep {
             (* [PlaceOrder] : Place an order into the 'Orders' table *)
                  def update "PlaceOrder" ( o : Order ) : rep :=
                    Insert o into Orders,

             (* [AddBook] : Add a book to the inventory *)
             def update "AddBook" ( b : Book ) : rep :=
                 Insert b into Books ;

             (* [GetTitles] : The titles of books written by a given author *)
             def query "GetTitles" ( author : string ) : list string :=
               For (b in Books)
               Where (author = b!Author)
               Return (b!Title),

             (* [NumOrders] : The number of orders for a given author *)
             def query "NumOrders" ( author : string ) : nat :=
                 Count (For (o in Orders) (b in Books)
                        Where (author = b!Author)
                        Where (b!ISBN = o!oISBN)
                        Return o!oISBN)
         } .

  Local Close Scope QueryStructureParsing_scope.
  Local Close Scope QuerySpec.
  Local Open Scope QueryStructure_scope.

  Tactic Notation "implement" "queries" "over" "lists" :=
      unfold DropQSConstraints_SiR in *; subst;
      repeat rewrite GetRelDropConstraints in *; subst; split_and;
      repeat (progress
                (try (setoid_rewrite Equivalent_In_EnsembleListEquivalence; simpl; eauto);
                 try (setoid_rewrite Equivalent_List_In_Where with (P_dec := _); simpl);
                 try (setoid_rewrite Equivalent_Join_Lists; eauto)));
        setoid_rewrite refine_For_List_Return; simplify with monad laws.

  Definition BookStoreListImpl_SiR or (nr : (list Book) * (list Order)) : Prop :=
    (EnsembleListEquivalence (GetUnConstrRelation or Books) (fst nr))
    /\ (EnsembleListEquivalence (GetUnConstrRelation or Orders) (snd nr)).

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    (* Step 1: Drop the constraints on the tables. From the perspective
      of a client of a sharpened ADT the invariants will still hold,
      since ADT refinement preserves the simulation relation.   *)
    hone representation using (@DropQSConstraints_SiR BookStoreSchema).

    (* Step 2: Remove extraneous schema and cross-relation constraints
       from the [PlaceOrder] mutator so that subsequent refinements
       will only need to implement with the foreign key constraint. *)
    hone mutator "PlaceOrder".
    {
      remove trivial insertion checks.
      finish honing.
    }

    (* Step 3: Similarly remove extraneous schema and cross-relation
       constraints [AddBook] mutator so that subsequent refinements
       will only need to implement the single key constraint. *)
    hone mutator "AddBook".
    {
      remove trivial insertion checks.
      remove_trivial_insertion_constraints r_n n Orders Books
                                           oISBN ISBN H.
      finish honing.
    }

    (* Step 4: Switch to an implementation of the representation
       type as a pair of lists of tuples. *)
    hone representation using BookStoreListImpl_SiR.

    (* Step 5: Implement the [GetTitles] observer for the pair of lists
     representation. *)
    hone observer "GetTitles".
    {
      unfold BookStoreListImpl_SiR in *; split_and.
      implement queries for lists.
      finish honing.
    }

    (* Step 6: Implement the [NumOrders] observer for the pair of lists
     representation. *)
    hone observer "NumOrders".
    {
      unfold BookStoreListImpl_SiR in *; split_and.
      unfold Count.
      (* We first swap the order of the 'fors' to make the
         implementation more efficient. *)
      rewrite Equivalent_Swap_In.
      rewrite refine_Query_For_In_Equivalent;
        [ | apply Equivalent_Swap_In_Where with (qs := _)].
      (* Now implement the list query. *)
      implement queries for lists.
      rewrite map_length.
      finish honing.
    }

    (* Step 7: Implement the [AddBook] mutator for the pair of lists
     representation. *)
    hone mutator "AddBook".
    { unfold BookStoreListImpl_SiR in *; split_and.
      setoid_rewrite refineEquiv_split_ex.
      setoid_rewrite refineEquiv_pick_computes_to_and.
      setoid_rewrite refine_unused_key_check with
      (h_dec_eq := BookSchemaHeading_dec); eauto.
      simplify with monad laws.
      setoid_rewrite refine_unused_key_check' with
      (h_dec_eq := BookSchemaHeading_dec); eauto.
      simplify with monad laws.
      rewrite refine_pick_eq_ex_bind.
      rewrite refineEquiv_pick_pair.
      Split Constraint Checks.
      implement insert for lists.
      unfold Orders, Books; congruence.
      implement failed insert.
    }

    (* Step 7: Implement the [PlaceOrder] mutator for the pair of lists
     representation. *)
    hone mutator "PlaceOrder".
    { unfold BookStoreListImpl_SiR in *; split_and.
      setoid_rewrite refineEquiv_split_ex.
      setoid_rewrite refineEquiv_pick_computes_to_and.
      setoid_rewrite refine_foreign_key_check with
                     (P_dec := _); eauto.
      simplify with monad laws.
      rewrite refine_pick_eq_ex_bind.
      rewrite refineEquiv_pick_pair.
      Split Constraint Checks.
      implement insert for lists.
      unfold Orders, Books; congruence.
      implement failed insert.
    }

    (* Step 8: Profit. :)*)

    finish sharpening.
  Defined.

    (* Alternate 'simple' steps. *)
    (* Step 3: Add the '#Orders' attribute to Books schema. *)


    (* Step 3.1: Hone GetTitles to ignore the new field. *)
    (* Step 3.2: Hone AddBook to set '#Orders' to 0. *)
    (* Step 3.3: Hone PlaceOrder to increment '#Orders'. *)
    (* Step 3.4: Hone NumOrders to use said field. *)

    (* Step 4: Switch to implementation of Books to a
               hashmap from authors to lists of titles. *)
    (* Step 4.1: Update mutators *)
    (* Step 4.2: Update observers *)

  (* Definition BookStoreSchema' :=
    query structure schema
      [ relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat,
                        "#Orders" : nat>
                where attributes ["Title" ; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"]. *)

  (*Definition AddAttribute_SiR
             (or : BookStoreRefRep)
             (nr : QueryStructure BookStoreSchema') :=
    (GetRelation or Orders = GetRelation nr Orders /\
     GetRelation or Books = map (fun tup => <"Author" : tup!Author,
                                             "Title" : tup!Title,
                                             "ISBN" : tup!ISBN>%Tuple)
                                (GetRelation nr Books)). *)


  (* Definition Ref_SiR
             (or : BookStoreRefRep)
             (nr : list Book * list Order) :=
    (forall o : Order, List.In o (snd nr)  (or 's Orders) rel' /\ rel rel' o) /\
    (forall b : Book, List.In b (fst nr) <-> exists rel', (or 's Books) rel' /\ rel rel' b). *)

  (* Still need to reimplement specs using a better query notation.

  Definition PlaceOrderSpec
             (r : BookStoreRefRep) (n : nat) (r' : BookStoreRefRep) :=
    (* The Book tables are the same. *)
    Books r = Books r'
    (* If the ordered book is in the inventory (i.e. is a foreign
            key), the updated set of orders is a subset of the
            original set of orders. *)
    /\
    forall b,
      In (Books r) b /\ ISBN b = n ->
      Orders r' = @cons Order n (Orders r).

  Definition AddBookSpec
             (r : BookStoreRefRep) (b : Book) (r' : BookStoreRefRep) :=
         (* The Order tables are the same.*)
         Orders r = Orders r'
         (* If the new book's ISBN isn't already in the inventory,
            the updated set of books now includes it
            (i.e. ISBN is a primary key). *)
         /\
         (forall b', ISBN b = ISBN b' -> ~ In (Books r) b') ->
         Books r' = union (Books r) (Coq.Sets.Uniset.Singleton _ Book_eq_dec b).

  Definition GetTitlesSpec
             (r : BookStoreRefRep) (author : string) (titles : list string) :=
         (* Every element in the returned list iff a corresponding book
            in the original inventory. *)
         forall title, List.In title titles <->
                       exists b, In (Books r) b /\ Title b = title.

  Inductive NumOrdersSpec
  : BookStoreRefRep -> string -> nat -> Prop :=
    numOrderSpec :
      forall inventory author (l : list nat) (f : Order -> bool),
        (* The number of orders for a *)
        (forall o, f o = true <->
                   exists book, In (Books inventory) book
                              /\ ISBN book = oISBN o
                              /\ Author book = author) ->
        NumOrdersSpec inventory author
                      (length (filter f (Orders inventory))).

  Definition BookStorePick : ADT BookStoreSig :=
    ADTRep BookStoreRefRep {
             def mut "PlaceOrder" ( r : rep , n : nat ) : rep :=
               {r' | PlaceOrderSpec r n r'},
             def mut AddBook ( r : rep , b : Book ) : rep :=
               {r' | AddBookSpec r b r'} ;
             def obs GetTitles ( r : rep , author : string ) : (list string) :=
               {titles | GetTitlesSpec r author titles} ,
             def obs NumOrders ( r : rep , author : string ) : nat :=
               {numtitles | NumOrdersSpec r author numtitles}
         } .

Definition Ref_SiR
           (or : BookStoreRefRep)
           (nr : list Book * list Order) :=
  List.incl (snd nr) (Orders or) /\ (* The orders in the new rep are a subset
                                           of the orders in the old rep. *)
  List.incl (Orders or) (snd nr) /\ (* and vice-versa. *)
  forall b, In (Books or) b <-> List.In b (fst nr).

  Definition BookStore :
    Sharpened BookStorePick.
  Proof.
    hone representation' using Ref_SiR.
  Admitted. *)

End BookStoreExamples.
