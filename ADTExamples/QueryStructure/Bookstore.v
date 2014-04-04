Require Import String Omega List FunctionalExtensionality Ensembles.
Require Export Computation ADT ADTRefinement ADT.Pick ADTNotation
        ADTRefinement.BuildADTRefinements
        QueryStructureSchema QueryStructure QueryQSSpecs InsertQSSpecs.

Generalizable All Variables.
Set Implicit Arguments.

Section BookStoreExamples.

  (* Our bookstore has two relations (tables):
     - The books in the inventory
     - The orders that have been placed *)

Definition MovieSchema :=
  (schema <"Title" : string, ("ReleaseDate"%string : nat)%Attribute>
   where attributes ["ReleaseDate"] depend on ["Title"])%Schema.

Open Scope QSSchema.

  Definition BookStoreSchema :=
    query structure schema
      [ relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"].

  (* Sanity check to show that the definitions produced
     can be efficiently evaluated. *)
  Goal (forall b,
          qschemaConstraints
            BookStoreSchema
            {| bstring := "Orders" |}
            {| bstring := "Books" |} = b).
  Time simpl.
  Abort.

  Definition BookStoreRefRep := @QueryStructure BookStoreSchema.

  Definition BookSchema :=
    schemaHeading (qschemaSchema BookStoreSchema {| bstring := "Books" |}).
  Definition OrderSchema :=
    schemaHeading (qschemaSchema BookStoreSchema {| bstring := "Orders" |}).

  Definition Book := Tuple BookSchema.
  Definition Order := Tuple OrderSchema.

  (* Our bookstore has two mutators:
     - [PlaceOrder] : Place an order into the 'Orders' table
     - [AddBook] : Add a book to the inventory

     Our bookstore has two observers:
     - [GetTitles] : The titles of books written by a given author
     - [NumOrders] : The number of orders for a given author
   *)

  Local Open Scope ADTSig_scope.
  Local Open Scope ADTParsing_scope.
  Local Open Scope Schema.
  Local Open Scope QuerySpec.

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "PlaceOrder" : rep × Order → rep,
        "AddBook" : rep × Book → rep ;
        "GetTitles" : rep × string → Relation schema <"Title" : string>,
        "NumOrders" : rep × string → nat
      }.

  (* [GetTitles] : The titles of books written by a given author *)
  Definition GetTitlesSpec
             (r : BookStoreRefRep) (author : string) :=
    For (b in r 's "Books")
    Where (b 's "Author" = author)
    Return <"Title" : (b 's "Title") >
    returning (schema <"Title" : string>).

  (* [NumOrders] : The number of orders for a given author *)
  Definition NumOrdersSpec
             (r : BookStoreRefRep) (author : string) : Ensemble nat :=
    Count (For (b in r 's "Books") (o in r 's "Orders" )
           Where (b 's "Author" = author /\ (b 's "ISBN") = (o 's "ISBN"))
           Return <"ISBN" : (o 's "ISBN") >
           returning (schema <"ISBN" : nat>)).

  Definition BookStoreSpec : ADT BookStoreSig :=
    ADTRep BookStoreRefRep {
             (* [PlaceOrder] : Place an order into the 'Orders' table *)
             def mut "PlaceOrder" ( r : rep , o : Order ) : rep :=
               Pick (Insert o into "Orders" of r),

             (* [AddBook] : Add a book to the inventory *)
             def mut "AddBook" ( r : rep , b : Book ) : rep :=
                 Pick (Insert b into "Books" of r) ;

             (* [GetTitles] : The titles of books written by a given author *)
             def obs "GetTitles" ( r : rep , author : string ) :
               Relation schema <"Title" : string> :=
               {titles | forall rel', rel (GetTitlesSpec r author) rel'
                                      <-> rel titles rel' } ,

             (* [NumOrders] : The number of orders for a given author *)
             def obs "NumOrders" ( r : rep , author : string ) : nat :=
                 Pick (Count (For (b in r 's "Books") (o in r 's "Orders" )
                              Where (b 's "Author" = author /\ (b 's "ISBN") = (o 's "ISBN"))
                              Return <"ISBN" : (o 's "ISBN") >
                              returning (schema <"ISBN" : nat>)))
         } .

  Open Scope QueryStructure.

  Definition Ref_SiR
             (or : BookStoreRefRep)
             (nr : list Book * list Order) :=
    (forall o : Order, List.In o (snd nr) <-> exists rel', (or 's "Orders") rel' /\ rel rel' o) /\
    (forall b : Book, List.In b (fst nr) <-> exists rel', (or 's "Books") rel' /\ rel rel' b).

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    hone representation' using Ref_SiR.
    (* This breaks our query notation- we need to reformulate that in a
     better way. We also need to abstract it to return arbitrary
     collection structures so we can tune the data type of the returned
     structures. *)

  Admitted.

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
             def mut "AddBook" ( r : rep , b : Book ) : rep :=
               {r' | AddBookSpec r b r'} ;
             def obs "GetTitles" ( r : rep , author : string ) : (list string) :=
               {titles | GetTitlesSpec r author titles} ,
             def obs "NumOrders" ( r : rep , author : string ) : nat :=
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
