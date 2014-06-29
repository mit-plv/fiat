Class mkIndex_helper {T1 T2} (heading : T1) (attributes' : T2) retT := make_mkIndex_helper : retT.
Ltac constr_mkIndex heading0 attributes0 retT0 :=
  constr:((_ : mkIndex_helper heading0 attributes0 retT0) : retT0).
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
 * to save on type-checking time.
 * (Thanks for being weird, Coq!) *)
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
      "Init" : unit → rep,
      "PlaceOrder" : rep × Order → rep × bool,
      "AddBook" : rep × Book → rep × bool,
      "GetTitles" : rep × string → rep × list string,
      "NumOrders" : rep × string → rep × nat
    }.

(* Now we write what the methods should actually do. *)
Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    const "Init" (_ : unit) : rep := empty,

    update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS,

    update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS ,

    query "GetTitles" ( author : string ) : list string :=
      For (b in sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE),

     query "NumOrders" ( author : string ) : nat :=
        Count (For (o in sORDERS) (b in sBOOKS)
               Where (author = b!sAUTHOR)
               Where (b!sISBN = o!sISBN)
               Return o!sISBN)
}.

(* Aliases for internal names of the two tables *)
Definition Books := BookStoreSchema/sBOOKS.
Definition Orders := BookStoreSchema/sORDERS.

(* Aliases for internal notions of schemas for the two tables *)
Definition BookSchema := QSGetNRelSchemaHeading BookStoreSchema Books.
Definition OrderSchema := QSGetNRelSchemaHeading BookStoreSchema Orders.

Hint Extern 0 (mkIndex_helper ?heading ?attributes' ?retT) => change retT; mkIndex heading attributes' : typeclass_instances.

Tactic Notation "plan" "with" "abstraction" "relation" "for" constr(Schema)
       "with" "name" constr(strName1) "and" "schema" constr(schema1) "of" "bag" "of" constr(thing1) "indexed" "on" constr(indices1)
        "and" "name" constr(strName2) "and" "schema" constr(schema2) "of" "bag" "of" constr(thing2) "indexed" "on" constr(indices2)
  := let Storage1 := constr_mkIndex schema1 indices1 (@BagPlusBagProof thing1) in
     let T1 := constr:(BagType Storage1) in
     let Storage2 := constr_mkIndex schema2 indices2 (@BagPlusBagProof thing2) in
     let T2 := constr:(BagType Storage2) in
     let x := constr:(fun (or : UnConstrQueryStructure Schema)
                          (nr : T1 * T2)
                      => or!strName1 ≃ benumerate (fst nr) /\ or!strName2 ≃ benumerate (snd nr)) in
     let AbsR := fresh "AbsR" in
     pose x as AbsR;
       plan AbsR;
       subst AbsR.

Definition BookStore :
  Sharpened BookStoreSpec.
Proof.
  plan with abstraction relation for BookStoreSchema
       with name sBOOKS  and schema BookSchema  of bag of Book  indexed on [ Books//sAUTHOR ; Books//sISBN ]
       and  name sORDERS and schema OrderSchema of bag of Order indexed on [ Orders//sISBN ].
  finish sharpening.
Defined.
