Require Import String Omega List FunctionalExtensionality Ensembles.
Require Export Computation ADT ADTRefinement ADT.Pick ADTNotation
        ADTRefinement.BuildADTRefinements
        QueryStructureSchema QueryStructure.

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
      [relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
       relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ] enforcing [attribute "ISBN" of "Orders" references "Books"].

  Arguments BuildForeignKeyConstraints _ _ [_ _ _ _] _ _ / .
            (* Arguments BuildQueryStructureConstraints [_] _ / _ _ _ _.
  Arguments BuildQueryStructureConstraints_obligation_1 [_] _ _ _ _ / .
  Arguments BuildQueryStructureConstraints_obligation_2 [_] _ _ _ _ _ / .
  Arguments ith_obligation_2 [A B C] AC_eq [As] _ c default_A default_B [a] As' H il0 / .
  Arguments ith_obligation_1 [A B C] _ [As] _ c default_A default_B _ / . *)

  Goal (forall b,
          qschemaConstraints
            BookStoreSchema
            {| bstring := "Orders" |}
            {| bstring := "Books" |} = b).
  Time simpl.
  Time unfold BuildQueryStructureConstraints.
  Time simpl BuildQueryStructureConstraints_obligation_1.
  Time simpl BuildQueryStructureConstraints_obligation_2.
  Time simpl BuildQueryStructureConstraints_eq_snd.
  Time simpl BuildQueryStructureConstraints_eq_fst.
  Time simpl siglist2ilist.
  Time simpl eq_ind_r.
  Time simpl eq_rect at 2.
  Time simpl eq_rect at 1.
  Time simpl.
  Abort.
  simpl.
  unfold ith_obligation_1; simpl.
  unfold ith_obligation_2; simpl.
  BuildQueryStructureConstraints_obligation_1,
  BuildQueryStructureConstraints_obligation_2.
  unfold ith_obligation_1, ith_obligation_2; simpl.
  unfold ith_obligation_1; simpl.
  unfold ith_obligation_2; simpl.
  simpl.

  Definition bar :=       [relation "Books" has
                schema <"Author" : string,
                        "Title" : string,
                        "ISBN" : nat>
                where attributes ["Title"; "Author"] depend on ["ISBN"];
       relation "Orders" has
                schema <"ISBN" : nat,
                        "Date" : nat> ]%NamedSchema.

  Definition foo := (
                     @BuildForeignKeyConstraints
                       bar
                       "Orders"%string "Books"%string _ _
                       {| bstring := "ISBN" |} {| bstring := "ISBN" |}
                   id).

  Notation "'attribute' attr 'of' rel1 'references' rel2 " :=
    (
      @BuildForeignKeyConstraints
        (@nSchemaHint _) rel1%string rel2%string _ _
        {| bstring := attr%string;
           stringb := _|}
        {| bstring := attr%string;
           stringb := _|} id).

  Check (let bar' := Build_namedSchemaHint bar in
         (attribute "ISBN" of "Orders" references "Books")).

  Check (let bar' := Build_namedSchemaHint bar in
         [attribute "ISBN" of "Orders" references "Books"]).

    (fun relBnd1 relBnd2 attr1map attr2map
         tupmap =>
       @BuildForeignKeyConstraints
         nSchemaHint rel1 rel2 relBnd1 relBnd2
         (attr1map {| bstring := attr |}) (attr2map {| bstring := attr |})
         tupmap) : QSSchemaConstraints_scope.

  Notation "[ constr1 ; .. ; constrn ]" :=
    (cons (constr1 _ _ _ id id id) .. (cons (constrn _ _ _ id id id) nil) ..).

  Definition baz :=
    let bar' := Build_namedSchemaHint bar in
    @BuildForeignKeyConstraints
      (@nSchemaHint _) "Orders"%string "Books"%string _ _
      {| bstring := "ISBN"%string;
         stringb := _|}
    {| bstring := "ISBN"%string;
         stringb := _|} id.

  Check baz.
    fun relBnd1 relBnd2 attr1map attr2map attr1Bnd attr2Bnd tupmap =>
      @BuildForeignKeyConstraints
         (@nSchemaHint bar') "Orders"%string "Books"%string relBnd1 relBnd2
         (attr1map {| bstring := "ISBN"%string;
                      stringb := attr1Bnd|})
         (attr2map {| bstring := "ISBN"%string;
                      stringb := attr1Bnd |})
         tupmap.

    (let bar' := Build_namedSchemaHint bar in
     (attribute "ISBN" of "Orders" references "Books") (@nSchemaHint bar'))%QSSchemaConstraints.
     in foo)%QSSchemaConstraints.
      baz _ _).

      foo id)%QSSchemaConstraints.

  Check foo.

  Definition foo :
    @sigT (qschemaIndex BookStoreSchema * qschemaIndex BookStoreSchema)
          (fun ids => @Relation (qschemaSchema BookStoreSchema (fst ids))
                      -> @Relation (qschemaSchema BookStoreSchema (snd ids))
                    -> Prop) :=
    (fun qSchema =>  existT (fun ids => @Relation (qSchema (fst ids))
                       -> @Relation (qSchema (snd ids))
                    -> Prop)
          ({| bstring := "Orders"%string|}, {| bstring := "Books"%string|})
          (fun (R1 : @Relation (_ (fst _)))
               (R2 : @Relation (_ (snd _)))
           =>
           forall tup1,
             rel R1 tup1 ->
             exists tup2,
               rel R2 tup2 /\
               (tup1 {| bstring := "ISBN"%string|} = tup2 {| bstring := "ISBN"%string|} ))) (qschemaSchema BookStoreSchema).


      [attribute "ISBN" of "Orders" references "Books"].

  Definition BookStore := QueryStructure BookStoreSchema.

  Definition BookSchema :=
    schemaHeading (qschemaSchema BookStoreSchema {| bstring := "Books" |}).

  (* Our bookstore has two mutators:
     - [PlaceOrder] : Place an order into the 'Orders' table
     - [AddBook] : Add a book to the inventory

     Our bookstore has two observers:
     - [GetTitles] : The titles of books written by a given author
     - [NumOrders] : The number of orders for a given author
   *)

  Local Open Scope ADTSig_scope.
  Local Open Scope ADT_scope.
  Local Open Scope string_scope.

  Definition Book := Tuple BookSchema.

  Definition BookStoreSig : ADTSig :=
    ADTsignature {
        "PlaceOrder" : rep × nat → rep,
        "AddBook" : rep × Book → rep ;
        "GetTitles" : rep × string → list string,
        "NumOrders" : rep × string → nat
      }.

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
