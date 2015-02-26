Require Import Coq.Strings.String.
Require Import ADTSynthesis.QueryStructure.Automation.AutoDB.

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

(* Let's define some synonyms for strings we'll need,
 * to save on type-checking time. *)
Definition sBOOKS := "Books".
Definition sAUTHOR := "Authors".
Definition sTITLE := "Title".
Definition sISBN := "ISBN".
Definition sORDERS := "Orders".
Definition sDATE := "Date".

(* Now here's the actual schema, in the usual sense. *)

Definition BookStoreSchema :=
  Query Structure Schema
    [ relation sBOOKS has
              schema <sAUTHOR :: string,
                      sTITLE :: string,
                      sISBN :: nat>
                      where attributes [sTITLE; sAUTHOR] depend on [sISBN];
      relation sORDERS has
              schema <sISBN :: nat,
                      sDATE :: nat> ]
    enforcing [attribute sISBN for sORDERS references sBOOKS].

(* Aliases for the tuples contained in Books and Orders, respectively. *)
Definition Book := TupleDef BookStoreSchema sBOOKS.
Definition Order := TupleDef BookStoreSchema sORDERS.

(* Our bookstore has two mutators:
   - [PlaceOrder] : Place an order into the 'Orders' table
   - [AddBook] : Add a book to the inventory

   Our bookstore has two observers:
   - [GetTitles] : The titles of books written by a given author
   - [NumOrders] : The number of orders for a given author
 *)

(* So, first let's give the type signatures of the methods. *)
Definition BookStoreSig : ADTSig :=
  ADTsignature {
      Constructor "Init" : unit -> rep,
      Method "PlaceOrder" : rep x Order -> rep x bool,
      Method "DeleteOrder" : rep x nat -> rep x list Order,
      Method "AddBook" : rep x Book -> rep x bool,
      Method "DeleteBook" : rep x nat -> rep x list Book,
      Method "GetTitles" : rep x string -> rep x list string,
      Method "NumOrders" : rep x string -> rep x nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS,

    update "DeleteOrder" ( oid : nat ) : list Order :=
      Delete o from sORDERS where o!sISBN = oid,

    update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS ,

     update "DeleteBook" ( id : nat ) : list Book :=
        Delete book from sBOOKS where book!sISBN = id ,

    query "GetTitles" ( author : string ) : list string :=
      For (b in sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE) ,

    query "NumOrders" ( author : string ) : nat :=
      Count (For (o in sORDERS) (b in sBOOKS)
                 Where (author = b!sAUTHOR)
                 Where (b!sISBN = o!sISBN)
                 Return ())
}.

Theorem BookStoreManual :
  Sharpened BookStoreSpec.
Proof.

  unfold BookStoreSpec.

  (* First, we unfold various definitions and drop constraints *)
  start honing QueryStructure.


  (* Then we define an index structure for each table using Bag ADTs *)
  make simple indexes using [[sAUTHOR; sISBN]; [sISBN]].
  (* In other words, implement the Book table with a Bag ADT
    indexed first on the author field, then the ISBN field
    and the Orders table with a Bag ADT indexed on just the ISBN field. *)

  (* Having selected a more concrete data-representation, we start
     the actual refinement with the constructor, in a fully automated way *)
  hone constructor "Init".
  { abstract initializer. }

  (* We then move on to the "NumOrders" method, which we decide to
     implement semi-manually *)
  hone method "NumOrders".
  {
    (* First we generate a new goal to just focus on refining the query. *)
    Focused_refine_Query. (* With Focused_refine_Query: 7 seconds. *)
    { (* Step 1: Implement [In] by enumeration. *)
      implement_In.
      (* Step 2: Convert where clauses into compositions of filters. *)
      repeat convert_Where_to_filter.
      (* Step 3: Do some simplication.*)
      repeat setoid_rewrite <- filter_and.
      try setoid_rewrite andb_true_r.
      (* Step 4: Move filters to the outermost [Join_Comp_Lists] to which *)
      (* they can be applied. *)
      repeat setoid_rewrite Join_Filtered_Comp_Lists_id.
      distribute_filters_to_joins.
      (* Step 5: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
      implement_filters_with_find.
    }
    (* Do some more simplication using the monad laws. *)
    simpl; simplify with monad laws.
    (* Satisfied with the query, we now implement the new data
       representation (in this case, it is unchanged).
     *)
    simpl; commit.
    (* And we're done! *)
    finish honing.
  }

  (* We'll now refine a insertion operation. *)
  hone method "AddBook".
  {
    (* First Convert Integrity Checks to Queries. *)
    Implement_Insert_Checks.

    (* These queries can be implemented using the [implement_Query] tactic *)
    (* which automatically concretizes queries. *)
    implement_Query.

    simpl; simplify with monad laws.

    setoid_rewrite refineEquiv_swap_bind.
    implement_Insert_branches.

    finish honing.
  }

  hone method "DeleteBook".
  {
    simplify with monad laws.
    implement_Query.
    simpl; simplify with monad laws.
    implement_Delete_branches.
    finish honing.
  }

  hone method "GetTitles".
  { observer. }

  hone method "DeleteOrder".
  {
    implement_QSDeletedTuples find_simple_search_term.
    simplify with monad laws; cbv beta; simpl.
    implement_EnsembleDelete_AbsR find_simple_search_term.
    simplify with monad laws.
    finish honing.
  }

  hone method "PlaceOrder".
  {
  repeat first
         [setoid_rewrite FunctionalDependency_symmetry
         | cbv beta; simpl; simplify with monad laws
         | setoid_rewrite if_duplicate_cond_eq
         | fundepToQuery
         | foreignToQuery
         | setoid_rewrite refine_trivial_if_then_else
         ].
    etransitivity;
      [ repeat match goal with
                 | |- context[Query_For _] =>
                   setoid_rewrite refineEquiv_swap_bind at 1;
                     implement_Query;
                     eapply refine_under_bind; intros
               end;
        repeat setoid_rewrite refine_if_If at 1;
        repeat setoid_rewrite refine_If_Then_Else_Bind at 1;
        repeat setoid_rewrite Bind_refine_If_Then_Else at 1;
        repeat eapply refine_If_Then_Else;
        try simplify with monad laws; cbv beta; simpl;
        match goal with
          (* Implement the then branch *)
          | [ H : DelegateToBag_AbsR ?r_o ?r_n
              |- context[{r_n' |
                          DelegateToBag_AbsR
                            (UpdateUnConstrRelation ?r_o ?TableID
                                                    (EnsembleInsert
                                                       {| elementIndex := _; indexedElement := ?tup |}
                                                       (GetUnConstrRelation ?r_o ?TableID))) r_n'}]]
            => repeat setoid_rewrite <- refineEquiv_bind_bind;
              setoid_rewrite (@refine_BagADT_QSInsert _ _ r_o r_n H TableID tup);
              try (simplify with monad laws; higher_order_reflexivity)
          (* Implement the else branch *)
          | [ H : DelegateToBag_AbsR ?r_o ?r_n
              |- context[{r_n' | DelegateToBag_AbsR ?r_o r_n'}]] =>
            match goal with
            | |- context[{idx | UnConstrFreshIdx (GetUnConstrRelation r_o ?TableID) idx}] =>
              destruct ((proj2 H) TableID) as [l [[bnd fresh_bnd] _]];
                refine pick val bnd;
                [ simplify with monad laws;
                  refine pick val r_n;
                  [ simplify with monad laws;
                    higher_order_reflexivity
                  | eassumption ]
                | eassumption]
            end
        end
      | cbv beta; simpl; try simplify with monad laws; finish honing ].
  }

  FullySharpenQueryStructure BookStoreSchema Index.

  Time implement_bag_methods. (*  42 seconds*)
  Time implement_bag_methods. (*  28 seconds *)
  Time implement_bag_methods. (*  30 seconds *)
  Time implement_bag_methods. (*  87 seconds *)
  Time implement_bag_methods. (*   9 seconds *)
  Time implement_bag_methods. (*  27 seconds *)

  Time Defined.

(* Need to add better automation for extracting Query Structure Implementations. *)
(* Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined. *)
