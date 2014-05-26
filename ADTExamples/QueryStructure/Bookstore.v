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
  }.

  Local Close Scope QueryStructureParsing_scope.
  Local Close Scope QuerySpec.
  Local Open Scope QueryStructure_scope.

  Definition BookStoreListImpl_SiR or (nr : list Book * list Order) : Prop :=
    EnsembleListEquivalence (GetUnConstrRelation or Books) (fst nr)
    /\ EnsembleListEquivalence (GetUnConstrRelation or Orders) (snd nr).

  Instance ISBN_attr_dec :
    List_Query_eq (map (Domain BookSchemaHeading) ["ISBN"]%SchemaConstraints).
  eauto with typeclass_instances.
  Defined.

  Instance Title_Author_attr_dec :
    List_Query_eq (map (Domain BookSchemaHeading) ["Title";"Author"]%SchemaConstraints).
  eauto with typeclass_instances.
  Defined.

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    (* Step 1: Drop the constraints on the tables. From the perspective
      of a client of a sharpened ADT the invariants will still hold,
      since ADT refinement preserves the simulation relation. *)
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
       constraints from the [AddBook] mutator so that subsequent
       refinements will only need to implement the single key
       constraint. *)
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
        [ | apply Equivalent_Swap_In_Where with (qs := _)]; cbv beta.
      (* Now implement the list query. *)
      implement queries for lists.
      rewrite map_length.
      finish honing.
    }

    (* Step 7: Implement the [AddBook] mutator for the pair of lists
     representation. *)
    hone mutator "AddBook".
    {
      unfold BookStoreListImpl_SiR in *; split_and.
      setoid_rewrite refineEquiv_split_ex.
      setoid_rewrite refineEquiv_pick_computes_to_and.
      simplify with monad laws.
      setoid_rewrite refine_unused_key_check
      with (attr_eq_dec' := ISBN_attr_dec)
             (attr_eq_dec := _); eauto.
      simplify with monad laws.
      setoid_rewrite refine_unused_key_check'
      with (attr_eq_dec' := ISBN_attr_dec)
             (attr_eq_dec := _); eauto.
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
    {
      unfold BookStoreListImpl_SiR in *; split_and.
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

    (* Step 8: Profit. :) *)

    finish sharpening.
  Defined.

End BookStoreExamples.
