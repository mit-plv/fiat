Require Import String Omega List FunctionalExtensionality Ensembles.
Require Export Computation ADT ADTRefinement ADT.Pick
        ADTRefinement.BuildADTRefinements ADTNotation
        QueryStructureSchema QueryQSSpecs InsertQSSpecs QueryStructure.

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
            "Orders"%string
            "Books"%string = b).
  Time simpl.
  Abort.

  Definition BookStoreRefRep := QueryStructure BookStoreSchema.

  Definition BookSchema :=
    schemaHeading (GetNamedSchema BookStoreSchema "Books"%string).
  Definition OrderSchema :=
    schemaHeading (GetNamedSchema BookStoreSchema "Orders"%string).

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
  Local Open Scope QueryStructureParsing_scope.
  Local Open Scope Schema.
  Local Open Scope QuerySpec.

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "PlaceOrder" : rep × Order → rep,
        "AddBook" : rep × Book → rep ;
        "GetTitles" : rep × string → list string,
        "NumOrders" : rep × string → nat
      }.

  (* [GetTitles] : The titles of books written by a given author *)

  Arguments GetNamedSchema _ _ / .

  Arguments qsSchemaHint _ / .

  (* [NumOrders] : The number of orders for a given author *)
  Definition NumOrdersSpec
             (r : BookStoreRefRep) (author : string) :=
    let _ := {|qsHint := r |} in
    Count (For (o in "Orders") (b in "Books")
           Where (author == b!"Author")
           Where (b!"ISBN" == o!"ISBN")
           Return tt).

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreRefRep {
             (* [PlaceOrder] : Place an order into the 'Orders' table *)
             def update "PlaceOrder" ( o : Order ) : rep :=
               Insert o into "Orders",

             (* [AddBook] : Add a book to the inventory *)
             def update "AddBook" ( b : Book ) : rep :=
                 Insert b into "Books" ;

             (* [GetTitles] : The titles of books written by a given author *)
             def query "GetTitles" ( author : string ) : list string :=
               For (b in "Books")
               Where (author == b!"Author")
               Return b!"Title",

             (* [NumOrders] : The number of orders for a given author *)
             def query "NumOrders" ( author : string ) : nat :=
                 Count (For (o in "Orders") (b in "Books")
                        Where (author == b!"Author")
                        Where (b!"ISBN" == o!"ISBN")
                        Return <"ISBN" : o!"ISBN" >)
         } .

  Local Close Scope QueryStructureParsing_scope.
  Local Close Scope QuerySpec.
  Local Open Scope QueryStructure_scope.

  Definition BookStoreSchema' :=
    query structure schema
      [ relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat,
                        "#Orders" : nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"].

  Definition AddAttribute_SiR
             (or : BookStoreRefRep)
             (nr : QueryStructure BookStoreSchema') :=
    (GetRelation or "Orders" = GetRelation nr "Orders" /\
     GetRelation or "Books" = map (fun tup => <"Author" : tup!"Author",
                                   "Title" : tup!"Title",
                                   "ISBN" : tup!"ISBN">%Tuple)
                          (GetRelation nr "Books")).

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.
    (* Step 1: Decide what to do when inserting a book that
       violates the key constraints of Books. I think
       we will leave table unchanged when a 'bad' book is
       inserted. *)
    hone' mutator "PlaceOrder"%string.
    {
      simpl in *; intros; subst.
      setoid_rewrite refineEquiv_pick_eq';
      autorewrite with refine_monad.
      rewrite QSInsertSpec_refine with (default := ret r_n).
      subst_body.
      higher_order_2_reflexivity.
    }
    (* Step 2: Decide what to do when adding an order that
       violates foreign key constraints of Orders. *)
    hone' mutator "AddBook"%string.
    {
      intros; subst.
      setoid_rewrite refineEquiv_pick_eq';
      autorewrite with refine_monad.
      rewrite QSInsertSpec_refine with (default := ret r_n).
      subst_body.
      higher_order_2_reflexivity.
    }
    (* Step 3: Add the '#Orders' attribute to Books schema. *)
    hone representation' using AddAttribute_SiR.

    (* Step 3.1: Hone GetTitles to ignore the new field. *)
    (* Step 3.2: Hone AddBook to set '#Orders' to 0. *)
    (* Step 3.3: Hone PlaceOrder to increment '#Orders'. *)
    (* Step 3.4: Hone NumOrders to use said field. *)

    (* Step 4: Switch to implementation of Books to a
               hashmap from authors to lists of titles. *)
    (* Step 4.1: Update mutators *)
    (* Step 4.2: Update observers *)

  Admitted.

  (* Definition Ref_SiR
             (or : BookStoreRefRep)
             (nr : list Book * list Order) :=
    (forall o : Order, List.In o (snd nr)  (or 's "Orders") rel' /\ rel rel' o) /\
    (forall b : Book, List.In b (fst nr) <-> exists rel', (or 's "Books") rel' /\ rel rel' b). *)

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
