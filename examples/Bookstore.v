Section BookStoreExamples.
  Require Import QueryStructureNotations.
  Require Import ListImplementation.

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

  Definition BookStoreSchema :=
    Query Structure Schema
      [ relation "Books" has
                schema <"Author" :: string,
                        "Title" :: string,
                        "ISBN" :: nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
        relation "Orders" has
                schema <"ISBN" :: nat,
                        "Date" :: nat> ]
      enforcing [attribute "ISBN" of "Orders" references "Books"].

  (* Aliases for the tuples contained in Books and Orders, respectively. *)
  Definition Book := TupleDef BookStoreSchema "Books".
  Definition Order := TupleDef BookStoreSchema "Orders".

  (* Our bookstore has two mutators:
     - [PlaceOrder] : Place an order into the 'Orders' table
     - [AddBook] : Add a book to the inventory

     Our bookstore has two observers:
     - [GetTitles] : The titles of books written by a given author
     - [NumOrders] : The number of orders for a given author
   *)

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "InitBookstore" : unit → rep,
        "PlaceOrder" : rep × Order → rep × unit,
        "AddBook" : rep × Book → rep × unit,
        "GetTitles" : rep × string → rep × list string,
        "NumOrders" : rep × string → rep × nat
      }.

  Definition BookStoreSpec : ADT BookStoreSig :=
    QueryADTRep BookStoreSchema {
      const "InitBookstore" (_ : unit) : rep := empty,

      update "PlaceOrder" ( o : Order ) : unit :=
          Insert o into "Orders",

      update "AddBook" ( b : Book ) : unit :=
          Insert b into "Books" ,

      query "GetTitles" ( author : string ) : list string :=
        For (b in "Books")
        Where (author = b!"Author")
        Return (b!"Title"),

       query "NumOrders" ( author : string ) : nat :=
          Count (For (o in "Orders") (b in "Books")
                 Where (author = b!"Author")
                 Where (b!"ISBN" = o!"ISBN")
                 Return o!"ISBN")
  }.

  Definition BookStoreListImpl_AbsR
             (or : UnConstrQueryStructure BookStoreSchema)
             (nr : list Book * list Order) : Prop :=
    or ! "Books" ≃ fst nr /\ or ! "Orders" ≃ snd nr.

  Definition BookStore :
    Sharpened BookStoreSpec.
  Proof.
    unfold BookStoreSpec.

    (* Step 1: Drop the constraints on the tables. From the perspective
      of a client of a sharpened ADT the invariants will still hold,
      since ADT refinement preserves the simulation relation. *)
    start honing QueryStructure.

    (* Step 2: We first swap the order of the 'For's to make the
         implementation more efficient. *)

    hone method "NumOrders".
    { rewrite Equivalent_Swap_In;
      rewrite refine_Query_For_In_Equivalent;
        [ | apply Equivalent_Swap_In_Where with (qs := _)]; cbv beta;
        finish honing. }

    (* Step 3: Switch to an implementation of the representation
       type as a pair of lists of tuples. *)

    implement using lists under BookStoreListImpl_AbsR.

    (* Step 4: Profit. :) *)

    finish sharpening.
  Defined.
End BookStoreExamples.
