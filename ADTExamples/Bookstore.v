Require Import String Omega List Coq.Sets.Uniset Coq.Sets.Multiset.
Require Import FunctionalExtensionality.
Require Export Computation ADT ADTRefinement ADT.Pick ADTNotation
        ADTRefinement.BuildADTRefinements.

Generalizable All Variables.
Set Implicit Arguments.

Section BookStoreExamples.

  (* Our bookstore has two 'tables':
     - A list of books in the inventory
     - A list of orders that have been placed. *)

  Record Book :=
    { Author : string;
       Title : string;
       ISBN : nat}.

  Hint Resolve string_dec.

  Lemma Book_eq_dec : forall o o' : Book, {o = o'} + {o <> o'}.
    decide equality; auto with arith.
  Qed.

  Record Order := { oISBN : nat }.
  Coercion Build_Order : nat >-> Order.

  Lemma Order_eq_dec : forall o o' : Order, {o = o'} + {o <> o'}.
    decide equality; auto with arith.
  Qed.

  (* Our bookstore has two mutators:
     - [PlaceOrder] : Place an order into the 'Orders' table
     - [AddBook] : Add a book to the inventory

     Our bookstore has two observers:
     - [GetTitles] : The titles of books written by a given author
     - [NumOrders] : The number of orders for a given author
   *)

  Inductive BookStoreMutators : Set :=
    PlaceOrder | AddBook.
  Inductive BookStoreObservers : Set :=
    GetTitles | NumOrders.

  (* Well, this is what we'd like to write. *)

  Local Open Scope ADTSig_scope.
  Local Open Scope ADT_scope.
  Local Open Scope string_scope.

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "PlaceOrder" : rep × nat → rep,
        "AddBook" : rep × Book → rep ;
        "GetTitles" : rep × string → list string,
        "NumOrders" : rep × string → nat
      }.

  Record BookStoreRefRep :=
    { Books : uniset Book;
      Orders : list Order }.

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
  Admitted.

End BookStoreExamples.
