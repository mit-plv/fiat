Require Import Coq.Strings.String.
Require Import AutoDB.

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

  make simple indexes using [[sAUTHOR; sISBN]; [sISBN]].

  hone constructor "Init".
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    simpl.
    finish honing.
  }

  hone method "NumOrders".
  {
    simplify with monad laws.
    implement_In.
    setoid_rewrite refine_Join_Enumerate_Swap; eauto.
    convert_Where_to_search_term.

    find_equivalent_search_term 1 find_simple_search_term.
    find_equivalent_search_term_pair 1 0 find_simple_search_term_dep.

    convert_filter_to_find.
    Implement_Aggregates.
    commit.
    finish honing.
  }

  hone method "GetTitles".
  {
    simplify with monad laws.
    implement_In.
    convert_Where_to_search_term.
    find_equivalent_search_term 0 find_simple_search_term.
    convert_filter_to_find.
    Implement_Aggregates.
    commit.
    finish honing.
}

  hone method "DeleteOrder".
  {
    implement_QSDeletedTuples find_simple_search_term.
    simplify with monad laws; cbv beta; simpl.
    implement_EnsembleDelete_AbsR find_simple_search_term.
    simplify with monad laws.
    finish honing.
  }

  hone method "DeleteBook".
  {
    simplify with monad laws.
    implement_In.
    setoid_rewrite refine_Join_Enumerate_Swap; eauto.
    convert_Where_to_search_term.

    find_equivalent_search_term 1 find_simple_search_term.
    find_equivalent_search_term_pair 1 0 find_simple_search_term_dep.

    convert_filter_to_find.
    Implement_Aggregates.
    simplify with monad laws.

    implement_Delete_branches.
    finish honing.
  }

    hone method "AddBook".
  {
    repeat first
           [setoid_rewrite FunctionalDependency_symmetry
           | fundepToQuery; try simplify with monad laws
           | foreignToQuery; try simplify with monad laws
           | setoid_rewrite refine_trivial_if_then_else; simplify with monad laws
           ].

  FullySharpenQueryStructure BookStoreSchema Index.

Defined.

(* Need to add better automation for extracting Query Structure Implementations. *)
(* Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined. *)
