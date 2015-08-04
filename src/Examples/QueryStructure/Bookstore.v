Require Import Fiat.QueryStructure.Automation.MasterPlan.

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

Set Printing All.
Definition BookStoreSpec : ADT BookStoreSig :=
  Eval simpl in
    QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    update "PlaceOrder" ( r : rep , o : Order ) : bool :=
        Insert o into r!sORDERS,

    update "DeleteOrder" (r : rep, oid : nat ) : list Order :=
       Delete o from r!sORDERS where o!sISBN = oid,

    update "AddBook" (r : rep, b : Book ) : bool :=
        Insert b into r!sBOOKS ,

    update "DeleteBook" ( r : rep, id : nat ) : list Book :=
        Delete book from r!sBOOKS where book!sISBN = id,

    query "GetTitles" (r : rep, author : string ) : list string :=
      For (b in r ! sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE),

    query "NumOrders" (r : rep, author : string ) : nat :=
      Count (For (o in r!sORDERS) (b in r!sBOOKS)
                 Where (author = b!sAUTHOR)
                 Where (o!sISBN = b!sISBN)
                 Return ())
}.


Theorem SharpenedBookStore :
  FullySharpened BookStoreSpec.
Proof.

Ltac master_plan' matchIndex
     BuildEarlyIndex BuildLastIndex
     IndexUse createEarlyTerm createLastTerm
     IndexUse_dep createEarlyTerm_dep createLastTerm_dep
     BuildEarlyBag BuildLastBag :=
  (* Implement constraints as queries. *)
  start honing QueryStructure;
  (* Automatically select indexes + data structure. *)
  [GenerateIndexesForAll
     matchIndex
     ltac:(fun attrlist => make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex;
           match goal with
           | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
           | |- _ => (* Otherwise implement each method using the indexed data structure *)
             plan IndexUse createEarlyTerm createLastTerm
                  IndexUse_dep createEarlyTerm_dep createLastTerm_dep
           end;
           pose_headings_all;
           match goal with
           | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
             FullySharpenQueryStructure Schema Indexes
           end
          )
  | simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;

    BuildQSIndexedBags' BuildEarlyBag BuildLastBag
  | cbv zeta; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;
    simpl Sharpened_Implementation;
    unfold
      Update_Build_IndexedQueryStructure_Impl_cRep,
    Join_Comp_Lists',
    GetIndexedQueryStructureRelation,
    GetAttributeRaw; simpl
  ].

Ltac master_plan IndexTactics := IndexTactics master_plan'.

  (* Uncomment this to see the mostly sharpened implementation *)
  (* partial_master_plan EqIndexTactics. *)
  master_plan EqIndexTactics.
  idtac.
  apply reflexivityT.

Time Defined.

Time Definition BookstoreImpl : ComputationalADT.cADT BookStoreSig :=
  Eval simpl in projT1 SharpenedBookStore.

Print BookstoreImpl.
