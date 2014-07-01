Require Import AutoDB.

Definition BookstoreSchema := 
  Query Structure Schema [ 
    relation "Books" has schema <"Author" :: string,
                                 "Title"  :: string,
                                 "ISBN"   :: nat>
                     where attributes ["Title"; "Author"] 
                            depend on ["ISBN"];
    relation "Orders" has schema <"ISBN" :: nat,
                                  "Date" :: nat> 
  ] enforcing [attribute "ISBN" for "Orders" references "Books"].

Definition BooksHeading  := GetHeading BookstoreSchema "Books".
Definition OrdersHeading := GetHeading BookstoreSchema "Orders".

Definition Book  := @Tuple BooksHeading.
Definition Order := @Tuple OrdersHeading.

Definition BookstoreSig : ADTSig :=
  ADTsignature {
    "Init"       : unit         → rep,
    "AddBook"    : rep × Book   → rep × bool,
    "PlaceOrder" : rep × Order  → rep × bool,
    "GetTitles"  : rep × string → rep × list string,
    "NumOrders"  : rep × string → rep × nat
  }.

Definition BookstoreSpec : ADT BookstoreSig :=
  QueryADTRep BookstoreSchema {
    const "Init"        (_: unit)         : rep := 
      empty,
      
    update "AddBook"    (book: Book)      : bool :=
      Insert book into "Books",

    update "PlaceOrder" (order: Order)    : bool :=
      Insert order into "Orders",

    query "GetTitles"   (author: string)  : list string :=
      For (b in "Books")
      Where (author = b!"Author")
      Return (b!"Title"),

    query "NumOrders"   (author : string) : nat :=
      Count (
        For (o in "Orders") (b in "Books")
        Where (author = b!"Author")
        Where (b!"ISBN" = o!"ISBN")
        Return o!"ISBN"
      )
  }.

Definition BooksStorage : @BagPlusBagProof Book.
  mkIndex BooksHeading  [BooksHeading/"Author"; BooksHeading/"ISBN"].
Defined.

Definition OrdersStorage : @BagPlusBagProof Order.
  mkIndex OrdersHeading [OrdersHeading/"ISBN"].
Defined.

Definition BookstoreAbsR
           (or : UnConstrQueryStructure BookstoreSchema)
           (nr : (BagType BooksStorage) * (BagType OrdersStorage)) :=
  or!"Books" ≃ benumerate (fst nr) /\ or!"Orders" ≃ benumerate (snd nr).

Definition Bookstore :
  Sharpened BookstoreSpec.
Proof.
  plan BookstoreAbsR.
  finish sharpening.
Defined.

(* TODO: Print List.length, not Datatypes.length *)

Sharpened
  (ADTRep (TBookStorage * TOrderStorage)
    { const "Init" (_: ()) : rep :=
        ret
          (StringTreeBag.IndexedBag_bempty
             (fun x : Tuple => cast eq_refl (x ``(sAUTHOR))),
           NatTreeBag.IndexedBag_bempty
             (fun x : Tuple => cast eq_refl (x ``(sISBN)))) ,
        meth "PlaceOrder" (r_n : rep, n : Order) : bool :=
          (if negb (beq_nat
                      (Datatypes.length (bfind (fst r_n) (None, (Some n!sISBN, [])))) 0)
           then ret (fst r_n, binsert (snd r_n) n, true)
           else ret (r_n, false)) ,
        meth "AddBook" (r_n : rep, n : Book) : bool :=
          (if beq_nat
                (Datatypes.length
                   (bfind (fst r_n)
                      (None,
                      (Some (n ``(sISBN)),
                      [fun a : Tuple =>
                       negb
                         ((?[string_dec (n ``(sTITLE)) (a ``(sTITLE))]) &&
                          (?[string_dec (n ``(sAUTHOR)) (a ``(sAUTHOR))]))]))))
                0
           then ret (binsert (fst r_n) n, snd r_n, true)
           else ret (r_n, false)) ,
        meth "GetTitles" (p : rep, s : string) : (list string) :=
          ret
            (p,
            map (fun tup : Tuple => tup!sTITLE)
              (bfind (fst p) (Some s, (None, [])))) ,
        meth "NumOrders" (p : rep, s : string) : nat :=
          ret
            (p,
            fold_left
              (fun (count : nat) (x : Tuple) =>
               count + Datatypes.length (bfind (snd p) (Some x!sISBN, [])))
              (bfind (fst p) (Some s, (None, []))) 0)  })%ADT

(* Sample output after running repeat match goal with 
           | [ H := _ |- _ ] => unfold H in *; clear H
         end. :

Sharpened
     (ADTRep (TBookStorage * TOrderStorage)
      { const "Init" (_: ()) : rep :=
          ret
            (StringTreeBag.IndexedBag_bempty
               (fun x : Tuple => cast eq_refl (x ``(sAUTHOR))),
            NatTreeBag.IndexedBag_bempty
              (fun x : Tuple => cast eq_refl (x ``(sISBN)))) ,
        meth "PlaceOrder" (r_n : rep, n : Order) : bool :=
          (if negb
                (beq_nat
                   (Datatypes.length
                      (bfind (fst r_n) (None, (Some n!sISBN, [])))) 0)
           then ret (fst r_n, binsert (snd r_n) n, true)
           else ret (r_n, false)) ,
        meth "AddBook" (r_n : rep, n : Book) : bool :=
          (if beq_nat
                (Datatypes.length
                   (bfind (fst r_n)
                      (None,
                      (Some (n ``(sISBN)),
                      [fun a : Tuple =>
                       negb
                         ((?[string_dec (n ``(sTITLE)) (a ``(sTITLE))]) &&
                          (?[string_dec (n ``(sAUTHOR)) (a ``(sAUTHOR))]))]))))
                0
           then ret (binsert (fst r_n) n, snd r_n, true)
           else ret (r_n, false)) ,
        meth "GetTitles" (p : rep, s : string) : (list string) :=
          ret
            (p,
            map (fun tup : Tuple => tup!sTITLE)
              (bfind (fst p) (Some s, (None, [])))) ,
        meth "NumOrders" (p : rep, s : string) : nat :=
          ret
            (p,
            fold_left
              (fun (count : nat) (x : Tuple) =>
               count + Datatypes.length (bfind (snd p) (Some x!sISBN, [])))
              (bfind (fst p) (Some s, (None, []))) 0)  })%ADT
*)