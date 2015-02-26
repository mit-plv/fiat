Require Import AutoDB.

Definition SC := 
  Query Structure Schema [ 
    relation "Books" has schema <"Author" :: string,
                                 "Title"  :: string,
                                 "ISBN"   :: nat>
                     where attributes ["Title"; "Author"] 
                            depend on ["ISBN"];
    relation "Orders" has schema <"ISBN" :: nat,
                                  "Date" :: nat> 
  ] enforcing [attribute "ISBN" for "Orders" references "Books"].

Definition BookstoreSig : ADTSig :=
  ADTsignature {
    "Init"       : unit              → rep,
    "AddBook"    : rep × SC#"Books"  → rep × bool,
    "PlaceOrder" : rep × SC#"Orders" → rep × bool,
    "GetTitles"  : rep × string      → rep × list string,
    "NumOrders"  : rep × string      → rep × nat
  }.

Definition BookstoreSpec : ADT BookstoreSig :=
  QueryADTRep SC {
    const "Init"        (_: unit)            : rep := 
      empty,
      
    update "AddBook"    (book: SC#"Books")   : bool :=
      Insert book into "Books",

    update "PlaceOrder" (order: SC#"Orders") : bool :=
      Insert order into "Orders",

    query "GetTitles"   (author: string)     : list string :=
      For (b in "Books")
      Where (author = b!"Author")
      Return (b!"Title"),

    query "NumOrders"   (author : string)    : nat :=
      Count (
        For (o in "Orders") (b in "Books")
        Where (author = b!"Author")
        Where (b!"ISBN" = o!"ISBN")
        Return o!"ISBN"
      )
  }.

Definition BooksStorage : @BagPlusBagProof (SC#"Books").
  makeIndex SC "Books" ["Author"; "ISBN"].
Defined.

Definition OrdersStorage : @BagPlusBagProof (SC#"Orders").
  makeIndex SC "Orders" ["ISBN"].
Defined.

Definition Bookstore_AbsR
           (or : UnConstrQueryStructure SC)
           (nr : (BagType BooksStorage) * (BagType OrdersStorage)) :=
  or!"Books" ≃ benumerate (fst nr) /\ or!"Orders" ≃ benumerate (snd nr).

Definition Bookstore :
  Sharpened BookstoreSpec.
Proof.
  plan Bookstore_AbsR.
  finish sharpening.
Defined.
