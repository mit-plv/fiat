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

Definition TablesAndColumns (qs: QueryStructureSchema) :=
  Vector.fold_right2
    (fun table colnames acc => (table, colnames) :: acc) [] _
    (QSschemaNames qs) (Vector.map (fun sch => Vector.to_list (schemaHeadingNames sch)) (QSschemaSchemas qs)).

Eval compute in (TablesAndColumns BookStoreSchema).

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

  (* To pick a specific index structure using
     [master_plan_w_specific_indexes], users provide a list of (type
     of index, attribute name) for each table.  As an example, the
     invocation below specifies that the Books table should be indexed
     first on authors and then ISBNs (using nested AVLs keyed on those
     attributes), and that the Orders table should be indexed on
     ISBNs, again using an AVL tree keyed on order ISBNs.

     Changing the attributes used, the order of those attributes, and
     the type of index for each pair will result in a different data
     structure.

     We currently support (more details on each are in the
     QueryStructure/Automation/SearchTerms/ directory):

     - "EqualityIndex" : AVL Trees keyed on equality
     - "FindPrefixIndex" : Tries
     - "InclusionIndex" : Inverted Indexes
     - "RangeIndex" : AVL Trees keyed on range

     You'll also have to change the package of tactics, as
     demonstrated by other examples in this directory, in order to use
     these different index data structures. *)

  Notation IndexType :=
    (@ilist3 RawSchema (fun sch : RawSchema =>
                          list (string * Attributes (rawSchemaHeading sch)))
             (numRawQSschemaSchemas BookStoreSchema) (qschemaSchemas BookStoreSchema)).

  Definition indices0 : IndexType :=
    {| prim_fst := [("EqualityIndex", sISBN # sBOOKS ## BookStoreSchema)];
       prim_snd := {| prim_fst := [("EqualityIndex", sISBN # sORDERS ## BookStoreSchema)];
                     prim_snd := () |} |}.

  Definition indices1 : IndexType :=
    {| prim_fst := [("EqualityIndex", sAUTHOR # sBOOKS ## BookStoreSchema);
                   ("EqualityIndex", sISBN # sBOOKS ## BookStoreSchema)];
       prim_snd := {| prim_fst := [("EqualityIndex", sISBN # sORDERS ## BookStoreSchema)];
                     prim_snd := () |} |}.

  Definition indices2 : IndexType :=
    {| prim_fst := [("EqualityIndex", sTITLE # sBOOKS ## BookStoreSchema)];
       prim_snd := {| prim_fst := [("EqualityIndex", sISBN # sORDERS ## BookStoreSchema)];
                     prim_snd := () |} |}.

  Definition indices3 : IndexType :=
    {| prim_fst := [("EqualityIndex", sTITLE # sBOOKS ## BookStoreSchema)];
       prim_snd := {| prim_fst := [("EqualityIndex", sDATE # sORDERS ## BookStoreSchema)];
                     prim_snd := () |} |}.

  Definition indices4 : IndexType :=
    {| prim_fst := [("EqualityIndex", sAUTHOR # sBOOKS ## BookStoreSchema);
                   ("EqualityIndex", sTITLE # sBOOKS ## BookStoreSchema);
                   ("EqualityIndex", sISBN # sBOOKS ## BookStoreSchema)];
       prim_snd := {| prim_fst := [("EqualityIndex", sISBN # sORDERS ## BookStoreSchema)];
                     prim_snd := () |} |}.

  Definition indices5 : IndexType :=
    {| prim_fst := [("EqualityIndex", sAUTHOR # sBOOKS ## BookStoreSchema);
                   ("RangeIndex", sISBN # sBOOKS ## BookStoreSchema)];
       prim_snd := {| prim_fst := [("RangeIndex", sISBN # sORDERS ## BookStoreSchema)];
                     prim_snd := () |} |}.

  master_plan_w_specific_indexes
    indices0
    ltac:(CombineIndexTactics RangeIndexTactics EqIndexTactics).
Defined.
