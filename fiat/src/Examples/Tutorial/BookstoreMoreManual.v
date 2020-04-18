(* Let's look at the standard Bookstore example in more detail,
 * performing some steps manually. *)

Require Import Tutorial.

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
      Constructor "Init" : rep,
      Method "PlaceOrder" : rep * Order -> rep * bool,
      Method "DeleteOrder" : rep * nat -> rep * (list Order),
      Method "AddBook" : rep * Book -> rep * bool,
      Method "DeleteBook" : rep * nat -> rep * (list Book),
      Method "GetTitles" : rep * string -> rep * (list string),
      Method "NumOrders" : rep * string -> rep * nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  Eval simpl in
    Def ADT {
      rep := QueryStructure BookStoreSchema,
    Def Constructor0 "Init" : rep := empty,,

    Def Method1 "PlaceOrder" (r : rep) (o : Order) : rep * bool :=
        Insert o into r!sORDERS,

    Def Method1 "DeleteOrder" (r : rep) (oid : nat) : rep * list Order :=
        Delete o from r!sORDERS where o!sISBN = oid,

    Def Method1 "AddBook" (r : rep) (b : Book) : rep * bool :=
        Insert b into r!sBOOKS,

    Def Method1 "DeleteBook" (r : rep) (id : nat) : rep * list Book :=
        Delete book from r!sBOOKS where book!sISBN = id,

    Def Method1 "GetTitles" (r : rep) (author : string) : rep * list string :=
        titles <- For (b in r!sBOOKS)
                  Where (author = b!sAUTHOR)
                  Return (b!sTITLE);
        ret (r, titles),

    Def Method1 "NumOrders" (r : rep) (author : string) : rep * nat :=
        count <- Count (For (o in r!sORDERS) (b in r!sBOOKS)
                        Where (author = b!sAUTHOR)
                        Where (o!sISBN = b!sISBN)
                        Return ());
        ret (r, count)
  }%methDefParsing.

Theorem SharpenedBookStore :
  FullySharpened BookStoreSpec.
Proof.
  start sharpening ADT.
  start_honing_QueryStructure'.
  chooseIndexes.

  Focus 6.
  simpl in *.

  monad_simpl.
  Focused_refine_Query.
  implement_In_opt.
  distribute_filters_to_joins.
  implement_filters_using_find.
  (* unfold Join_Comp_Lists; simpl. *)
  monad_simpl.
  pick_new_database.
  finish honing.

  Focus 6.
  simpl in *.

  monad_simpl.
  Focused_refine_Query.
  implement_In_opt.
  distribute_filters_to_joins.
  implement_filters_using_find.
  monad_simpl.
  pick_new_database.
  finish honing.

  (* Now let's finish off the others with standard automation,
   * so that we can move on to more interesting stuff. *)
  planOne.
  planOne.
  planOne.
  planOne.
  planOne.

  (* The final steps involve getting the program into functional, executable form. *)
  final_optimizations.

  determinize.            (* Put the program into a form where it's obviously
                           * deterministic, given an implementation of each
                           * index data structure. *)
  choose_data_structures. (* Choose an implementation for each index data structure. *)
  final_simplification.   (* Perform any more algebraic simplfications that are possible,
                           * now that we know each concrete data structure. *)
  use_this_one.           (* Now commit to this precise implementation. *)
Defined.

Definition BookstoreImpl : ComputationalADT.cADT BookStoreSig :=
  Eval simpl in projT1 SharpenedBookStore.

Print BookstoreImpl.
