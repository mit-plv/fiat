Require Import Coq.Strings.String.
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
      (* Method "PlaceOrder" : rep x Order -> rep x bool, *)
      Method "DeleteOrder" : rep x nat -> rep x list Order,
      (* Method "AddBook" : rep x Book -> rep x bool, *)
      (* Method "DeleteBook" : rep x nat -> rep x list Book, *)
      Method "GetTitles" : rep x string -> rep x list string,
      Method "NumOrders" : rep x string -> rep x nat
    }.

(* Now we write what the methods should actually do. *)

Definition BookStoreSpec : ADT BookStoreSig :=
  QueryADTRep BookStoreSchema {
    Def Constructor "Init" (_ : unit) : rep := empty,

    (*update "PlaceOrder" ( o : Order ) : bool :=
        Insert o into sORDERS, *)

    update "DeleteOrder" ( oid : nat ) : list Order :=
      Delete o from sORDERS where o!sISBN = oid,

    (*update "AddBook" ( b : Book ) : bool :=
        Insert b into sBOOKS , *)

    (* update "DeleteBook" ( id : nat ) : list Book :=
        Delete book from sBOOKS where book!sISBN = id , *)

    query "GetTitles" ( author : string ) : list string :=
      For (b in sBOOKS)
      Where (author = b!sAUTHOR)
      Return (b!sTITLE) ,

    query "NumOrders" ( author : string ) : nat :=
      Count (For (o in sORDERS) (b in sBOOKS)
                 Where (author = b!sAUTHOR)
                 Where (b!sISBN = o!sISBN)
                 Return ())
}.

Definition BooksSearchTerm :=
{|
             BagSearchTermType := @BuildIndexSearchTerm
                                    <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                    [sAUTHOR; sISBN]%SchemaConstraints;
             BagMatchSearchTerm := @MatchIndexSearchTerm
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints
                                     (@icons
                                        (@BoundedString
                                           [sAUTHOR; sTITLE; sISBN])
                                        (fun
                                           attr : @BoundedString
                                                  [sAUTHOR; sTITLE; sISBN] =>
                                         Query_eq
                                           (attrType
                                              (@nth_Bounded Attribute string
                                                 attrName
                                                 [(sAUTHOR :: string)%Attribute;
                                                 (sTITLE :: string)%Attribute;
                                                 (sISBN :: nat)%Attribute]
                                                 attr))) ``
                                        (sAUTHOR) [sISBN]%SchemaConstraints
                                        Astring_eq
                                        (@icons
                                           (@BoundedString
                                              [sAUTHOR; sTITLE; sISBN])
                                           (fun
                                              attr :
                                               @BoundedString
                                                 [sAUTHOR; sTITLE; sISBN] =>
                                            Query_eq
                                              (attrType
                                                 (@nth_Bounded Attribute
                                                  string attrName
                                                  [
                                                  (sAUTHOR :: string)%Attribute;
                                                  (sTITLE :: string)%Attribute;
                                                  (sISBN :: nat)%Attribute]
                                                  attr))) ``
                                           (sISBN)
                                           [] Anat_eq
                                           (@inil
                                              (@BoundedString
                                                 [sAUTHOR; sTITLE; sISBN])
                                              (fun
                                                 attr :
                                                  @BoundedString
                                                  [sAUTHOR; sTITLE; sISBN] =>
                                               Query_eq
                                                 (attrType
                                                  (@nth_Bounded Attribute
                                                  string attrName
                                                  [
                                                  (sAUTHOR :: string)%Attribute;
                                                  (sTITLE :: string)%Attribute;
                                                  (sISBN :: nat)%Attribute]
                                                  attr))))));
             BagUpdateTermType := @Tuple
                                    <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading ->
                                  @Tuple
                                    <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading;
             BagApplyUpdateTerm := fun
                                     z : @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading => z |}.

Definition OrderSearchTerm :=
  {|
                BagSearchTermType := @BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints;
                BagMatchSearchTerm := @MatchIndexSearchTerm
                                        <sISBN :: nat,
                                           sDATE :: nat>%Heading
                                        [sISBN]%SchemaConstraints
                                        (@icons
                                           (@BoundedString [sISBN; sDATE])
                                           (fun
                                              attr :
                                               @BoundedString
                                                 [sISBN; sDATE] =>
                                            Query_eq
                                              (attrType
                                                 (@nth_Bounded Attribute
                                                  string attrName
                                                  [
                                                  (sISBN :: nat)%Attribute;
                                                  (sDATE :: nat)%Attribute]
                                                  attr))) ``
                                           (sISBN)
                                           [] Anat_eq
                                           (@inil
                                              (@BoundedString [sISBN; sDATE])
                                              (fun
                                                 attr :
                                                  @BoundedString
                                                  [sISBN; sDATE] =>
                                               Query_eq
                                                 (attrType
                                                  (@nth_Bounded Attribute
                                                  string attrName
                                                  [
                                                  (sISBN :: nat)%Attribute;
                                                  (sDATE :: nat)%Attribute]
                                                  attr)))));
                BagUpdateTermType := @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading;
                BagApplyUpdateTerm := fun
                                        z : @Tuple
                                              <sISBN :: nat,
                                                 sDATE :: nat>%Heading ->
                                            @Tuple
                                              <sISBN :: nat,
                                                 sDATE :: nat>%Heading => z |}.

Definition BookSchema' :=
  ({|
                  schemaHeading := <sAUTHOR :: string,
                                      sTITLE :: string,
                                      sISBN :: nat>%Heading;
                  schemaConstraints := @Some
                                         (@Tuple
                                            <sAUTHOR :: string,
                                               sTITLE :: string,
                                               sISBN :: nat>%Heading ->
                                          @Tuple
                                            <sAUTHOR :: string,
                                               sTITLE :: string,
                                               sISBN :: nat>%Heading -> Prop)
                                         (@FunctionalDependency_P
                                            <sAUTHOR :: string,
                                               sTITLE :: string,
                                               sISBN :: nat>%Heading
                                            [sTITLE; sAUTHOR]%SchemaConstraints
                                            [sISBN]%SchemaConstraints) |})%NamedSchema.

(*Lemma foo
: let Init := "Init" in
      let Empty := "Empty" in
      let DeleteOrder := "DeleteOrder" in
      let sDelete := "Delete" in
      let Find := "Find" in
      let Enumerate := "Enumerate" in
      let GetTitles := "GetTitles" in
      let NumOrders := "NumOrders" in
      let Index := @icons NamedSchema
             (fun ns : NamedSchema =>
              SearchUpdateTerms (schemaHeading (relSchema ns)))
             (relation sBOOKS has BookSchema')%NamedSchema
             [relation sORDERS has (schema <sISBN :: nat,
                                              sDATE :: nat>)%NamedSchema]
             BooksSearchTerm


             (@icons NamedSchema
                (fun ns : NamedSchema =>
                 SearchUpdateTerms (schemaHeading (relSchema ns)))
                relation sORDERS has (schema <sISBN :: nat,
                                                sDATE :: nat>)%NamedSchema
                []
                OrderSearchTerm

                (@inil NamedSchema
                   (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))))
        : @ilist NamedSchema
            (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns)))
            [relation sBOOKS
             has BookSchema'%NamedSchema;
            relation sORDERS has (schema <sISBN :: nat,
                                            sDATE :: nat>)%NamedSchema] in
      forall d,
      (forall DelegateImpls' , sigT (fun d' =>
                                       forall ValidImpl, Build_IndexedQueryStructure_Impl_AbsR' (qs_schema := BookStoreSchema) (Index := Index) (DelegateImpls := DelegateImpls') ValidImpl d d')) ->
   @sigT
     (SharpenedUnderDelegates (BuildADTSig [] []))
     (fun
        adt : SharpenedUnderDelegates (BuildADTSig [] []) =>
      @FullySharpenedUnderDelegates _
        (@BuildADT (IndexedQueryStructure BookStoreSchema Index)
           ((@nil consSig))
           ((@nil methSig))
           ((@inil consSig
                 (@consDef (IndexedQueryStructure BookStoreSchema Index))))
           ((@inil methSig
                 (@methDef (IndexedQueryStructure BookStoreSchema Index)))))
        adt).
 Proof.
   intros.
   Set Printing Universes.
   FullySharpenQueryStructure BookStoreSchema Index.
   Show Proof.

   Print Implicit Notation_Friendly_SharpenFully.

      Definition foo := ((let Init := "Init" in
 let Empty := "Empty" in
 let DeleteOrder := "DeleteOrder" in
 let sDelete := "Delete" in
 let Find := "Find" in
 let Enumerate := "Enumerate" in
 let GetTitles := "GetTitles" in
 let NumOrders := "NumOrders" in
       let Index := @icons NamedSchema
             (fun ns : NamedSchema =>
              SearchUpdateTerms (schemaHeading (relSchema ns)))
             (relation sBOOKS has BookSchema')%NamedSchema
             [relation sORDERS has (schema <sISBN :: nat,
                                              sDATE :: nat>)%NamedSchema]
             BooksSearchTerm
             (@icons NamedSchema
                (fun ns : NamedSchema =>
                 SearchUpdateTerms (schemaHeading (relSchema ns)))
                relation sORDERS has (schema <sISBN :: nat,
                                                sDATE :: nat>)%NamedSchema
                []
                OrderSearchTerm

                (@inil NamedSchema
                   (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))))
        : @ilist NamedSchema
            (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns)))
            [relation sBOOKS
             has BookSchema'%NamedSchema;
            relation sORDERS has (schema <sISBN :: nat,
                                            sDATE :: nat>)%NamedSchema] in
 fun Rep (d : IndexedQueryStructure BookStoreSchema Index)
   (_ : forall
          DelegateImpls' : ilist
                             (fun ns : NamedADTSig =>
                              ComputationalADT.cADT (namedADTSig ns))
                             (Build_IndexedQueryStructure_Impl_Sigs Index),
        {d' : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls' &
        forall
          ValidImpl : forall
                        idx : BoundedIndex
                                (map ADTSigname
                                   (Build_IndexedQueryStructure_Impl_Sigs
                                      Index)),
                      refineADT
                        (ith_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Specs Index) idx)
                        (ComputationalADT.LiftcADT
                           (ith_Bounded ADTSigname DelegateImpls' idx)),
          Build_IndexedQueryStructure_Impl_AbsR' (qs_schema := BookStoreSchema) (Index := Index) ValidImpl d d'}) DelegateSigs cRep

 =>
   Notation_Friendly_SharpenFully
     (inil (consDef (Rep := Rep)))
     (inil (methDef (Rep := Rep)))
     (DelegateSigs := DelegateSigs)
     cRep)).

      Print Implicit Notation_Friendly_SharpenFully.
      Print GeneralBuildADTRefinements.
      Print Universes.

      Check Notation_Friendly_SharpenFully.
      Print refineConstructor.
      Check getConsDef.

      Variable bar1 : forall
         (RepT : Type
                 (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.2710 *))
         (consSigs : list consSig) (methSigs : list methSig)
         (consDefs : ilist consDef consSigs)
         (methDefs : ilist (@methDef RepT) methSigs)
         (DelegateSigs : list NamedADTSig)
         (rep : ilist
                  (fun nadt : NamedADTSig =>
                   ComputationalADT.cADT (namedADTSig nadt)) DelegateSigs ->
                Type
                (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.2735 *))
         (cConstructors : forall
                            DelegateImpl : ilist
                                             (fun nadt : NamedADTSig =>
                                              ComputationalADT.cADT
                                                (namedADTSig nadt))
                                             DelegateSigs,
                          ilist
                            (fun Sig : consSig =>
                             ComputationalADT.cConstructorType
                               (rep DelegateImpl) (consDom Sig)) consSigs)
         (cMethods : forall
                       DelegateImpl : ilist
                                        (fun nadt : NamedADTSig =>
                                         ComputationalADT.cADT
                                           (namedADTSig nadt)) DelegateSigs,
                     ilist
                       (fun Sig : methSig =>
                        ComputationalADT.cMethodType
                          (rep DelegateImpl) (methDom Sig)
                          (methCod Sig)) methSigs)
         (DelegateSpecs : ilist
                            (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                            DelegateSigs)
         (cAbsR : forall
                    DelegateImpl : ilist
                                     (fun nadt : NamedADTSig =>
                                      ComputationalADT.cADT
                                        (namedADTSig nadt)) DelegateSigs,
                  (forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                   refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                     (ComputationalADT.LiftcADT
                        (ith_Bounded ADTSigname DelegateImpl idx))) ->
                  RepT -> rep DelegateImpl -> Prop),
       (forall
          (DelegateImpl : ilist
                            (fun nadt : NamedADTSig =>
                             ComputationalADT.cADT (namedADTSig nadt))
                            DelegateSigs)
          (ValidImpl : forall
                         idx : BoundedIndex (map ADTSigname DelegateSigs),
                       refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                         (ComputationalADT.LiftcADT
                            (ith_Bounded ADTSigname DelegateImpl idx))),
        Iterate_Dep_Type_BoundedIndex
          (fun idx : BoundedIndex (map consID consSigs) =>
             forall d,
               exists r_o',
               cAbsR DelegateImpl ValidImpl r_o' (ith_Bounded consID (cConstructors DelegateImpl) idx d) /\
               computes_to ((getConsDef (Rep := RepT) consDefs idx d)) (*Bind (A := RepT) (getConsDef (Rep := RepT) consDefs idx d)
                                                                                                       (fun r_o' => {r_n | (cAbsR DelegateImpl ValidImpl) r_o' r_n})*) r_o'
          (**))) ->
       (forall (DelegateImpl : ilist (fun nadt  => ComputationalADT.cADT (namedADTSig nadt)) DelegateSigs)
              (ValidImpl :
                 (forall idx,
                    refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                              (ComputationalADT.LiftcADT (ith_Bounded ADTSigname DelegateImpl idx)))),
            Iterate_Dep_Type_BoundedIndex
              (fun idx =>
                 forall d r_o r_n,
                   cAbsR _ ValidImpl r_o r_n ->
                   exists r_o',
                     cAbsR _ ValidImpl r_o' (fst (ith_Bounded _ (cMethods DelegateImpl) idx r_n d)) /\
                     computes_to (getMethDef methDefs idx r_o d)
                                 (r_o',
                                  (snd (ith_Bounded _ (cMethods DelegateImpl) idx r_n d))))) ->

       Sharpened (BuildADT consDefs methDefs).

      Print Iterate_Dep_Type_BoundedIndex.

      Definition foo' :=  ((let Init := "Init" in
 let Empty := "Empty" in
 let DeleteOrder := "DeleteOrder" in
 let sDelete := "Delete" in
 let Find := "Find" in
 let Enumerate := "Enumerate" in
 let GetTitles := "GetTitles" in
 let NumOrders := "NumOrders" in
       let Index := @icons NamedSchema
             (fun ns : NamedSchema =>
              SearchUpdateTerms (schemaHeading (relSchema ns)))
             (relation sBOOKS has BookSchema')%NamedSchema
             [relation sORDERS has (schema <sISBN :: nat,
                                              sDATE :: nat>)%NamedSchema]
             BooksSearchTerm
             (@icons NamedSchema
                (fun ns : NamedSchema =>
                 SearchUpdateTerms (schemaHeading (relSchema ns)))
                relation sORDERS has (schema <sISBN :: nat,
                                                sDATE :: nat>)%NamedSchema
                []
                OrderSearchTerm

                (@inil NamedSchema
                   (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))))
        : @ilist NamedSchema
            (fun ns : NamedSchema =>
             SearchUpdateTerms (schemaHeading (relSchema ns)))
            [relation sBOOKS
             has BookSchema'%NamedSchema;
            relation sORDERS has (schema <sISBN :: nat,
                                  sDATE :: nat>)%NamedSchema] in
      fun (d : IndexedQueryStructure BookStoreSchema Index)
   (_ : forall
          DelegateImpls' : ilist
                             (fun ns : NamedADTSig =>
                              ComputationalADT.cADT (namedADTSig ns))
                             (Build_IndexedQueryStructure_Impl_Sigs Index),
        {d' : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls' &
        forall
          ValidImpl : forall
                        idx : BoundedIndex
                                (map ADTSigname
                                   (Build_IndexedQueryStructure_Impl_Sigs
                                      Index)),
                      refineADT
                        (ith_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Specs Index) idx)
                        (ComputationalADT.LiftcADT
                           (ith_Bounded ADTSigname DelegateImpls' idx)),
          Build_IndexedQueryStructure_Impl_AbsR' (qs_schema := BookStoreSchema) (Index := Index) ValidImpl d d'})
 =>
   @bar1
     (IndexedQueryStructure BookStoreSchema Index) nil nil
     (inil consDef)
     (inil methDef)
     (Build_IndexedQueryStructure_Impl_Sigs Index)
     (Build_IndexedQueryStructure_Impl_cRep Index))).
     (Build_IndexedQueryStructure_Impl_Specs Index))).
          )).
     _
     (Build_IndexedQueryStructure_Impl_cRep Index))).
   (fun
      c : ilist
            (fun nadt : NamedADTSig =>
             ComputationalADT.cADT (namedADTSig nadt))
            (Build_IndexedQueryStructure_Impl_Sigs Index) =>
    inil
      (fun Sig : consSig =>
       ComputationalADT.cConstructorType
         (Build_IndexedQueryStructure_Impl_cRep Index c)
         (consDom Sig)))
   (fun
      c : ilist
            (fun nadt : NamedADTSig =>
             ComputationalADT.cADT (namedADTSig nadt))
            (Build_IndexedQueryStructure_Impl_Sigs Index) =>
    inil
      (fun Sig : methSig =>
       ComputationalADT.cMethodType
         (Build_IndexedQueryStructure_Impl_cRep Index c)
         (methDom Sig) (methCod Sig)))
   (Build_IndexedQueryStructure_Impl_Specs Index)
   (Build_IndexedQueryStructure_Impl_AbsR' (qs_schema := BookStoreSchema)
                                           (Index := Index)))).
   (fun
      (DelegateImpl : ilist
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig Tuple
                                               (@BuildIndexSearchTerm
                                    <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                    [sAUTHOR; sISBN]%SchemaConstraints)
                                          (Tuple -> Tuple) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig Tuple
                                              (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                         (Tuple -> Tuple) |}])
      (_ : forall idx : BoundedIndex [sBOOKS; sORDERS],
           refineADT
             (ith_Bounded' ADTSigname
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig Tuple
                                       (@BuildIndexSearchTerm
                                          <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (Tuple -> Tuple) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig Tuple
                                      (@BuildIndexSearchTerm
                                         <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                    [sISBN]%SchemaConstraints)
                                 (Tuple -> Tuple) |}]
                (nth_error_map ADTSigname (ibound idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                              <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (boundi idx))
                (ith_error
                   _
                   (ibound idx)))
             (ComputationalADT.LiftcADT
                (ith_Bounded' ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                              <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                                [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (nth_error_map ADTSigname (ibound idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig Tuple
                                             (@BuildIndexSearchTerm
                                                 <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (Tuple -> Tuple) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig Tuple
                                            (@BuildIndexSearchTerm
                                               <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                                   [sISBN]%SchemaConstraints)
                                       (Tuple -> Tuple) |}]
                      (boundi idx)) (ith_error DelegateImpl (ibound idx))))) =>
    ())
   (fun
      (DelegateImpl : ilist
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig Tuple
                                               (@BuildIndexSearchTerm
                                                   <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                             [sAUTHOR; sISBN]%SchemaConstraints)
                                          (Tuple -> Tuple) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig Tuple
                                              (@BuildIndexSearchTerm
                                                 <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                            [sISBN]%SchemaConstraints)
                                         (Tuple -> Tuple) |}])
      (_ : forall idx : BoundedIndex [sBOOKS; sORDERS],
           refineADT
             (ith_Bounded' ADTSigname
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig Tuple
                                       (@BuildIndexSearchTerm
                                          <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (Tuple -> Tuple) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig Tuple
                                      (@BuildIndexSearchTerm
                                         <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                    [sISBN]%SchemaConstraints)
                                 (Tuple -> Tuple) |}]
                (nth_error_map ADTSigname (ibound idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                             <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (boundi idx))
                (ith_error
                   _
                   (ibound idx)))
             (ComputationalADT.LiftcADT
                (ith_Bounded' ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                                                                          <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                             <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (nth_error_map ADTSigname (ibound idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig Tuple
                                             (@BuildIndexSearchTerm
                                                                                             <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (Tuple -> Tuple) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig Tuple
                                            (@BuildIndexSearchTerm
                                                <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (Tuple -> Tuple) |}]
                      (boundi idx)) (ith_error DelegateImpl (ibound idx))))) =>
    ()))).

   Check

     RefCons
     RefMeths)).
)).
   (Build_IndexedQueryStructure_Impl_Specs Index))).

   (Build_IndexedQueryStructure_Impl_AbsR'  (qs_schema := BookStoreSchema) (Index:=Index))
   (fun
      (DelegateImpl : ilist
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig Tuple
                                               (@BuildIndexSearchTerm
                                    <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                    [sAUTHOR; sISBN]%SchemaConstraints)
                                          (Tuple -> Tuple) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig Tuple
                                              (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                         (Tuple -> Tuple) |}])
      (_ : forall idx : BoundedIndex [sBOOKS; sORDERS],
           refineADT
             (ith_Bounded' ADTSigname
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig Tuple
                                       (@BuildIndexSearchTerm
                                          <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (Tuple -> Tuple) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig Tuple
                                      (@BuildIndexSearchTerm
                                         <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                    [sISBN]%SchemaConstraints)
                                 (Tuple -> Tuple) |}]
                (nth_error_map ADTSigname (ibound idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                              <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (boundi idx))
                (ith_error
                   _
                   (ibound idx)))
             (ComputationalADT.LiftcADT
                (ith_Bounded' ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                              <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                                [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (nth_error_map ADTSigname (ibound idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig Tuple
                                             (@BuildIndexSearchTerm
                                                 <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (Tuple -> Tuple) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig Tuple
                                            (@BuildIndexSearchTerm
                                               <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                                   [sISBN]%SchemaConstraints)
                                       (Tuple -> Tuple) |}]
                      (boundi idx)) (ith_error DelegateImpl (ibound idx))))) =>
    ())
   (fun
      (DelegateImpl : ilist
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig Tuple
                                               (@BuildIndexSearchTerm
                                                   <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                             [sAUTHOR; sISBN]%SchemaConstraints)
                                          (Tuple -> Tuple) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig Tuple
                                              (@BuildIndexSearchTerm
                                                 <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                            [sISBN]%SchemaConstraints)
                                         (Tuple -> Tuple) |}])
      (_ : forall idx : BoundedIndex [sBOOKS; sORDERS],
           refineADT
             (ith_Bounded' ADTSigname
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig Tuple
                                       (@BuildIndexSearchTerm
                                          <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (Tuple -> Tuple) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig Tuple
                                      (@BuildIndexSearchTerm
                                         <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                    [sISBN]%SchemaConstraints)
                                 (Tuple -> Tuple) |}]
                (nth_error_map ADTSigname (ibound idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                             <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (boundi idx))
                (ith_error
                   _
                   (ibound idx)))
             (ComputationalADT.LiftcADT
                (ith_Bounded' ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                          (@BuildIndexSearchTerm
                                                                                          <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                         (@BuildIndexSearchTerm
                                             <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (nth_error_map ADTSigname (ibound idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig Tuple
                                             (@BuildIndexSearchTerm
                                                                                             <sAUTHOR :: string,
                                       sTITLE :: string,
                                       sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (Tuple -> Tuple) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig Tuple
                                            (@BuildIndexSearchTerm
                                                <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (Tuple -> Tuple) |}]
                      (boundi idx)) (ith_error DelegateImpl (ibound idx))))) =>
    ()))). *)

Set Printing Universes.

Definition Build_IndexedQueryStructure_Impl_Sigs :=
fix Build_IndexedQueryStructure_Impl_Sigs (indices : list NamedSchema)
                                          (Index :
                                           ilist
                                             (fun ns : NamedSchema =>
                                              SearchUpdateTerms
                                                (schemaHeading (relSchema ns)))
                                             indices) {struct indices} :
  list NamedADTSig :=
  match
    indices as indices0
    return
      (ilist
         (fun ns : NamedSchema =>
          SearchUpdateTerms (schemaHeading (relSchema ns))) indices0 ->
       list NamedADTSig)
  with
  | [] =>
      fun
        _ : ilist
              (fun ns : NamedSchema =>
               SearchUpdateTerms (schemaHeading (relSchema ns)))
              [] => []
  | ns :: indices' =>
      fun
        Index0 : ilist
                   (fun ns0 : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns0)))
                   (ns :: indices') =>
      {|
      ADTSigname := relName ns;
      namedADTSig := BagSig (@Tuple (schemaHeading (relSchema ns))) (BagSearchTermType (ilist_hd Index0))
                       (BagUpdateTermType (ilist_hd Index0)) |}
      :: Build_IndexedQueryStructure_Impl_Sigs indices' (ilist_tl Index0)
  end Index.

Definition IndexedQueryStructure :=
fun (qs_schema : QueryStructureSchema)
  (BagIndexKeys : ilist
                    (fun ns : NamedSchema =>
                     SearchUpdateTerms (schemaHeading (relSchema ns)))
                    (qschemaSchemas qs_schema)) =>
i2list
  (fun (ns : NamedSchema)
     (index : (fun ns0 : NamedSchema =>
               SearchUpdateTerms (schemaHeading (relSchema ns0))) ns) =>
   Rep (BagSpec (BagMatchSearchTerm index) (BagApplyUpdateTerm index)))
  BagIndexKeys.

Definition Build_IndexedQueryStructure_Impl_cRep
           (indices : list NamedSchema)
           (Index : ilist
                      (fun ns : NamedSchema =>
                         SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (DelegateReps : ilist2 (fun ns : NamedADTSig => Type) (Build_IndexedQueryStructure_Impl_Sigs Index)) :=
  i2list2 (fun (ns : NamedADTSig) T => T) DelegateReps.

Print Notation_Friendly_SharpenFully.

Definition Notation_Friendly_SharpenFully :=
fun
  (RepT : Type
          (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.3152 *))
  (consSigs : list consSig) (methSigs : list methSig)
  (consDefs : ilist (consDef (Rep := RepT)) consSigs)
  (methDefs : ilist.ilist (methDef (Rep := RepT)) methSigs) (DelegateSigs : list NamedADTSig)
  (rep : ilist
           (fun _ : NamedADTSig =>
            Type
            (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.3175 *))
           DelegateSigs ->
         Type
         (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.3177 *))
 => True.

Check ((let Init := "Init" in
 let Empty := "Empty" in
 let DeleteOrder := "DeleteOrder" in
 let sDelete := "Delete" in
 let Find := "Find" in
 let Enumerate := "Enumerate" in
 let GetTitles := "GetTitles" in
 let NumOrders := "NumOrders" in
 let Index :=
   @icons NamedSchema
     (fun ns : NamedSchema =>
      SearchUpdateTerms (schemaHeading (relSchema ns)))
     relation sBOOKS has (BookSchema')%NamedSchema
     [relation sORDERS has (schema <sISBN :: nat, sDATE :: nat>)%NamedSchema]
     BooksSearchTerm
     (@icons NamedSchema
        (fun ns : NamedSchema =>
         SearchUpdateTerms (schemaHeading (relSchema ns)))
        relation sORDERS has (schema <sISBN :: nat,
                                        sDATE :: nat>)%NamedSchema
        [] OrderSearchTerm
        (@inil NamedSchema
           (fun ns : NamedSchema =>
            SearchUpdateTerms (schemaHeading (relSchema ns))))) in
 @Notation_Friendly_SharpenFully
   (IndexedQueryStructure BookStoreSchema Index) []
   []
   (@inil consSig (@consDef (IndexedQueryStructure BookStoreSchema Index)))
   (@ilist.inil methSig (@methDef (IndexedQueryStructure BookStoreSchema Index)))
   (@Build_IndexedQueryStructure_Impl_Sigs
      [relation sBOOKS has (BookSchema')%NamedSchema;
      relation sORDERS has (schema <sISBN :: nat, sDATE :: nat>)%NamedSchema]
      Index)
   (@Build_IndexedQueryStructure_Impl_cRep
      [relation sBOOKS has (BookSchema')%NamedSchema;
      relation sORDERS has (schema <sISBN :: nat, sDATE :: nat>)%NamedSchema]
      Index))).

(*
   (fun
      c : @ilist NamedADTSig
            (fun nadt : NamedADTSig =>
             ComputationalADT.cADT (namedADTSig nadt))
            (@Build_IndexedQueryStructure_Impl_Sigs
               [relation sBOOKS has (BookSchema')%NamedSchema;
               relation sORDERS has (schema <sISBN :: nat,
                                               sDATE :: nat>)%NamedSchema]
               Index) =>
    @inil consSig
      (fun Sig : consSig =>
       ComputationalADT.cConstructorType
         (@Build_IndexedQueryStructure_Impl_cRep
            [relation sBOOKS has (BookSchema')%NamedSchema;
            relation sORDERS has (schema <sISBN :: nat,
                                            sDATE :: nat>)%NamedSchema] Index
            c) (consDom Sig)))
   (fun
      c : @ilist NamedADTSig
            (fun nadt : NamedADTSig =>
             ComputationalADT.cADT (namedADTSig nadt))
            (@Build_IndexedQueryStructure_Impl_Sigs
               [relation sBOOKS has (BookSchema')%NamedSchema;
               relation sORDERS has (schema <sISBN :: nat,
                                               sDATE :: nat>)%NamedSchema]
               Index) =>
    @inil methSig
      (fun Sig : methSig =>
       ComputationalADT.cMethodType
         (@Build_IndexedQueryStructure_Impl_cRep
            [relation sBOOKS has (BookSchema')%NamedSchema;
            relation sORDERS has (schema <sISBN :: nat,
                                            sDATE :: nat>)%NamedSchema] Index
            c) (methDom Sig) (methCod Sig)))
   (@Build_IndexedQueryStructure_Impl_Specs
      [relation sBOOKS has (BookSchema')%NamedSchema;
      relation sORDERS has (schema <sISBN :: nat, sDATE :: nat>)%NamedSchema]
      Index) (@Build_IndexedQueryStructure_Impl_AbsR' BookStoreSchema Index)
   (fun
      (DelegateImpl : @ilist NamedADTSig
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig
                                          (@Tuple
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading)
                                          (@BuildIndexSearchTerm
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading
                                             [sAUTHOR; sISBN]%SchemaConstraints)
                                          (@Tuple
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading ->
                                           @Tuple
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig
                                         (@Tuple
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading)
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading
                                            [sISBN]%SchemaConstraints)
                                         (@Tuple
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading ->
                                          @Tuple
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading) |}])
      (_ : forall idx : @BoundedIndex string [sBOOKS; sORDERS],
           @refineADT
             (namedADTSig
                (@nth_Bounded NamedADTSig string ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}] idx))
             (@ith_Bounded' NamedADTSig string ADTSigname
                (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig
                                  (@Tuple
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading)
                                  (@BuildIndexSearchTerm
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (@Tuple
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading ->
                                   @Tuple
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig
                                 (@Tuple <sISBN :: nat,
                                            sDATE :: nat>%Heading)
                                 (@BuildIndexSearchTerm
                                    <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                    [sISBN]%SchemaConstraints)
                                 (@Tuple <sISBN :: nat,
                                            sDATE :: nat>%Heading ->
                                  @Tuple <sISBN :: nat,
                                            sDATE :: nat>%Heading) |}]
                (@bindex string [sBOOKS; sORDERS] idx)
                (@nth_error NamedADTSig
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx))
                (@nth_error_map NamedADTSig string ADTSigname
                   (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@Some string (@bindex string [sBOOKS; sORDERS] idx))
                   (@boundi string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx))
                (@ith_error NamedADTSig
                   (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@icons NamedADTSig
                      (fun ns : NamedADTSig => ADT (namedADTSig ns))
                      {|
                      ADTSigname := sBOOKS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading
                                          [sAUTHOR; sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading ->
                                        @Tuple
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading) |}
                      [{|
                       ADTSigname := sORDERS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading
                                           [sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading ->
                                         @Tuple
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading) |}]
                      (@BagSpec
                         (@Tuple
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading)
                         (@BuildIndexSearchTerm
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading
                            [sAUTHOR; sISBN]%SchemaConstraints)
                         (@Tuple
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading ->
                          @Tuple
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading)
                         (@MatchIndexSearchTerm
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading
                            [sAUTHOR; sISBN]%SchemaConstraints
                            (@icons (@BoundedString [sAUTHOR; sTITLE; sISBN])
                               (fun
                                  attr : @BoundedString
                                           [sAUTHOR; sTITLE; sISBN] =>
                                Query_eq
                                  (attrType
                                     (@nth_Bounded Attribute string attrName
                                        [(sAUTHOR :: string)%Attribute;
                                        (sTITLE :: string)%Attribute;
                                        (sISBN :: nat)%Attribute] attr)))
                               ``(sAUTHOR) [sISBN]%SchemaConstraints
                               Astring_eq
                               (@icons
                                  (@BoundedString [sAUTHOR; sTITLE; sISBN])
                                  (fun
                                     attr : @BoundedString
                                              [sAUTHOR; sTITLE; sISBN] =>
                                   Query_eq
                                     (attrType
                                        (@nth_Bounded Attribute string
                                           attrName
                                           [(sAUTHOR :: string)%Attribute;
                                           (sTITLE :: string)%Attribute;
                                           (sISBN :: nat)%Attribute] attr)))
                                  ``(sISBN) [] Anat_eq
                                  (@inil
                                     (@BoundedString [sAUTHOR; sTITLE; sISBN])
                                     (fun
                                        attr : @BoundedString
                                                 [sAUTHOR; sTITLE; sISBN] =>
                                      Query_eq
                                        (attrType
                                           (@nth_Bounded Attribute string
                                              attrName
                                              [(sAUTHOR :: string)%Attribute;
                                              (sTITLE :: string)%Attribute;
                                              (sISBN :: nat)%Attribute] attr)))))))
                         (fun
                            z : @Tuple
                                  <sAUTHOR :: string,
                                     sTITLE :: string,
                                     sISBN :: nat>%Heading ->
                                @Tuple
                                  <sAUTHOR :: string,
                                     sTITLE :: string,
                                     sISBN :: nat>%Heading => z))
                      (@icons NamedADTSig
                         (fun ns : NamedADTSig => ADT (namedADTSig ns))
                         {|
                         ADTSigname := sORDERS;
                         namedADTSig := BagSig
                                          (@Tuple
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading)
                                          (@BuildIndexSearchTerm
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading
                                             [sISBN]%SchemaConstraints)
                                          (@Tuple
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading ->
                                           @Tuple
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading) |}
                         []
                         (@BagSpec
                            (@Tuple <sISBN :: nat,
                                       sDATE :: nat>%Heading)
                            (@BuildIndexSearchTerm
                               <sISBN :: nat, sDATE :: nat>%Heading
                               [sISBN]%SchemaConstraints)
                            (@Tuple <sISBN :: nat,
                                       sDATE :: nat>%Heading ->
                             @Tuple <sISBN :: nat,
                                       sDATE :: nat>%Heading)
                            (@MatchIndexSearchTerm
                               <sISBN :: nat, sDATE :: nat>%Heading
                               [sISBN]%SchemaConstraints
                               (@icons (@BoundedString [sISBN; sDATE])
                                  (fun attr : @BoundedString [sISBN; sDATE] =>
                                   Query_eq
                                     (attrType
                                        (@nth_Bounded Attribute string
                                           attrName
                                           [(sISBN :: nat)%Attribute;
                                           (sDATE :: nat)%Attribute] attr)))
                                  ``(sISBN) [] Anat_eq
                                  (@inil (@BoundedString [sISBN; sDATE])
                                     (fun
                                        attr : @BoundedString [sISBN; sDATE] =>
                                      Query_eq
                                        (attrType
                                           (@nth_Bounded Attribute string
                                              attrName
                                              [(sISBN :: nat)%Attribute;
                                              (sDATE :: nat)%Attribute] attr))))))
                            (fun
                               z : @Tuple
                                     <sISBN :: nat,
                                        sDATE :: nat>%Heading ->
                                   @Tuple
                                     <sISBN :: nat,
                                        sDATE :: nat>%Heading => z))
                         (@inil NamedADTSig
                            (fun ns : NamedADTSig => ADT (namedADTSig ns)))))
                   (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx)))
             (@ComputationalADT.LiftcADT
                (namedADTSig
                   (@nth_Bounded NamedADTSig string ADTSigname
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}] idx))
                (@ith_Bounded' NamedADTSig string ADTSigname
                   (fun nadt : NamedADTSig =>
                    ComputationalADT.cADT (namedADTSig nadt))
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@bindex string [sBOOKS; sORDERS] idx)
                   (@nth_error NamedADTSig
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}]
                      (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx))
                   (@nth_error_map NamedADTSig string ADTSigname
                      (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}]
                      (@Some string (@bindex string [sBOOKS; sORDERS] idx))
                      (@boundi string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx))
                   (@ith_error NamedADTSig
                      (fun nadt : NamedADTSig =>
                       ComputationalADT.cADT (namedADTSig nadt))
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}]
                      DelegateImpl
                      (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx))))) =>
    ())
   (fun
      (DelegateImpl : @ilist NamedADTSig
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig
                                          (@Tuple
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading)
                                          (@BuildIndexSearchTerm
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading
                                             [sAUTHOR; sISBN]%SchemaConstraints)
                                          (@Tuple
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading ->
                                           @Tuple
                                             <sAUTHOR :: string,
                                                sTITLE :: string,
                                                sISBN :: nat>%Heading) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig
                                         (@Tuple
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading)
                                         (@BuildIndexSearchTerm
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading
                                            [sISBN]%SchemaConstraints)
                                         (@Tuple
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading ->
                                          @Tuple
                                            <sISBN :: nat,
                                               sDATE :: nat>%Heading) |}])
      (_ : forall idx : @BoundedIndex string [sBOOKS; sORDERS],
           @refineADT
             (namedADTSig
                (@nth_Bounded NamedADTSig string ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}] idx))
             (@ith_Bounded' NamedADTSig string ADTSigname
                (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig
                                  (@Tuple
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading)
                                  (@BuildIndexSearchTerm
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (@Tuple
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading ->
                                   @Tuple
                                     <sAUTHOR :: string,
                                        sTITLE :: string,
                                        sISBN :: nat>%Heading) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig
                                 (@Tuple <sISBN :: nat,
                                            sDATE :: nat>%Heading)
                                 (@BuildIndexSearchTerm
                                    <sISBN :: nat,
                                       sDATE :: nat>%Heading
                                    [sISBN]%SchemaConstraints)
                                 (@Tuple <sISBN :: nat,
                                            sDATE :: nat>%Heading ->
                                  @Tuple <sISBN :: nat,
                                            sDATE :: nat>%Heading) |}]
                (@bindex string [sBOOKS; sORDERS] idx)
                (@nth_error NamedADTSig
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx))
                (@nth_error_map NamedADTSig string ADTSigname
                   (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@Some string (@bindex string [sBOOKS; sORDERS] idx))
                   (@boundi string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx))
                (@ith_error NamedADTSig
                   (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@icons NamedADTSig
                      (fun ns : NamedADTSig => ADT (namedADTSig ns))
                      {|
                      ADTSigname := sBOOKS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading
                                          [sAUTHOR; sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading ->
                                        @Tuple
                                          <sAUTHOR :: string,
                                             sTITLE :: string,
                                             sISBN :: nat>%Heading) |}
                      [{|
                       ADTSigname := sORDERS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading
                                           [sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading ->
                                         @Tuple
                                           <sISBN :: nat,
                                              sDATE :: nat>%Heading) |}]
                      (@BagSpec
                         (@Tuple
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading)
                         (@BuildIndexSearchTerm
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading
                            [sAUTHOR; sISBN]%SchemaConstraints)
                         (@Tuple
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading ->
                          @Tuple
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading)
                         (@MatchIndexSearchTerm
                            <sAUTHOR :: string, sTITLE :: string,
                               sISBN :: nat>%Heading
                            [sAUTHOR; sISBN]%SchemaConstraints
                            (@icons (@BoundedString [sAUTHOR; sTITLE; sISBN])
                               (fun
                                  attr : @BoundedString
                                           [sAUTHOR; sTITLE; sISBN] =>
                                Query_eq
                                  (attrType
                                     (@nth_Bounded Attribute string attrName
                                        [(sAUTHOR :: string)%Attribute;
                                        (sTITLE :: string)%Attribute;
                                        (sISBN :: nat)%Attribute] attr)))
                               ``(sAUTHOR) [sISBN]%SchemaConstraints
                               Astring_eq
                               (@icons
                                  (@BoundedString [sAUTHOR; sTITLE; sISBN])
                                  (fun
                                     attr : @BoundedString
                                              [sAUTHOR; sTITLE; sISBN] =>
                                   Query_eq
                                     (attrType
                                        (@nth_Bounded Attribute string
                                           attrName
                                           [(sAUTHOR :: string)%Attribute;
                                           (sTITLE :: string)%Attribute;
                                           (sISBN :: nat)%Attribute] attr)))
                                  ``(sISBN) [] Anat_eq
                                  (@inil
                                     (@BoundedString [sAUTHOR; sTITLE; sISBN])
                                     (fun
                                        attr : @BoundedString
                                                 [sAUTHOR; sTITLE; sISBN] =>
                                      Query_eq
                                        (attrType
                                           (@nth_Bounded Attribute string
                                              attrName
                                              [(sAUTHOR :: string)%Attribute;
                                              (sTITLE :: string)%Attribute;
                                              (sISBN :: nat)%Attribute] attr)))))))
                         (fun
                            z : @Tuple
                                  <sAUTHOR :: string,
                                     sTITLE :: string,
                                     sISBN :: nat>%Heading ->
                                @Tuple
                                  <sAUTHOR :: string,
                                     sTITLE :: string,
                                     sISBN :: nat>%Heading => z))
                      (@icons NamedADTSig
                         (fun ns : NamedADTSig => ADT (namedADTSig ns))
                         {|
                         ADTSigname := sORDERS;
                         namedADTSig := BagSig
                                          (@Tuple
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading)
                                          (@BuildIndexSearchTerm
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading
                                             [sISBN]%SchemaConstraints)
                                          (@Tuple
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading ->
                                           @Tuple
                                             <sISBN :: nat,
                                                sDATE :: nat>%Heading) |}
                         []
                         (@BagSpec
                            (@Tuple <sISBN :: nat,
                                       sDATE :: nat>%Heading)
                            (@BuildIndexSearchTerm
                               <sISBN :: nat, sDATE :: nat>%Heading
                               [sISBN]%SchemaConstraints)
                            (@Tuple <sISBN :: nat,
                                       sDATE :: nat>%Heading ->
                             @Tuple <sISBN :: nat,
                                       sDATE :: nat>%Heading)
                            (@MatchIndexSearchTerm
                               <sISBN :: nat, sDATE :: nat>%Heading
                               [sISBN]%SchemaConstraints
                               (@icons (@BoundedString [sISBN; sDATE])
                                  (fun attr : @BoundedString [sISBN; sDATE] =>
                                   Query_eq
                                     (attrType
                                        (@nth_Bounded Attribute string
                                           attrName
                                           [(sISBN :: nat)%Attribute;
                                           (sDATE :: nat)%Attribute] attr)))
                                  ``(sISBN) [] Anat_eq
                                  (@inil (@BoundedString [sISBN; sDATE])
                                     (fun
                                        attr : @BoundedString [sISBN; sDATE] =>
                                      Query_eq
                                        (attrType
                                           (@nth_Bounded Attribute string
                                              attrName
                                              [(sISBN :: nat)%Attribute;
                                              (sDATE :: nat)%Attribute] attr))))))
                            (fun
                               z : @Tuple
                                     <sISBN :: nat,
                                        sDATE :: nat>%Heading ->
                                   @Tuple
                                     <sISBN :: nat,
                                        sDATE :: nat>%Heading => z))
                         (@inil NamedADTSig
                            (fun ns : NamedADTSig => ADT (namedADTSig ns)))))
                   (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                      [sBOOKS; sORDERS] idx)))
             (@ComputationalADT.LiftcADT
                (namedADTSig
                   (@nth_Bounded NamedADTSig string ADTSigname
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}] idx))
                (@ith_Bounded' NamedADTSig string ADTSigname
                   (fun nadt : NamedADTSig =>
                    ComputationalADT.cADT (namedADTSig nadt))
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading)
                                     (@BuildIndexSearchTerm
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (@Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading ->
                                      @Tuple
                                        <sAUTHOR :: string,
                                           sTITLE :: string,
                                           sISBN :: nat>%Heading) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading)
                                    (@BuildIndexSearchTerm
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading
                                       [sISBN]%SchemaConstraints)
                                    (@Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading ->
                                     @Tuple
                                       <sISBN :: nat,
                                          sDATE :: nat>%Heading) |}]
                   (@bindex string [sBOOKS; sORDERS] idx)
                   (@nth_error NamedADTSig
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}]
                      (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx))
                   (@nth_error_map NamedADTSig string ADTSigname
                      (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}]
                      (@Some string (@bindex string [sBOOKS; sORDERS] idx))
                      (@boundi string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx))
                   (@ith_error NamedADTSig
                      (fun nadt : NamedADTSig =>
                       ComputationalADT.cADT (namedADTSig nadt))
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading)
                                        (@BuildIndexSearchTerm
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (@Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading ->
                                         @Tuple
                                           <sAUTHOR :: string,
                                              sTITLE :: string,
                                              sISBN :: nat>%Heading) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading)
                                       (@BuildIndexSearchTerm
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading
                                          [sISBN]%SchemaConstraints)
                                       (@Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading ->
                                        @Tuple
                                          <sISBN :: nat,
                                             sDATE :: nat>%Heading) |}]
                      DelegateImpl
                      (@ibound string (@bindex string [sBOOKS; sORDERS] idx)
                         [sBOOKS; sORDERS] idx))))) =>
    ()))).

       (let Init := "Init" in
 let Empty := "Empty" in
 let DeleteOrder := "DeleteOrder" in
 let sDelete := "Delete" in
 let Find := "Find" in
 let Enumerate := "Enumerate" in
 let GetTitles := "GetTitles" in
 let NumOrders := "NumOrders" in
 let Index :=
   icons BooksSearchTerm
     (icons OrderSearchTerm
        (inil
           (fun ns : NamedSchema =>
            SearchUpdateTerms (schemaHeading (relSchema ns))))) in
 fun (d : IndexedQueryStructure BookStoreSchema Index)
   (_ : forall
          DelegateImpls' : ilist
                             (fun ns : NamedADTSig =>
                              ComputationalADT.cADT (namedADTSig ns))
                             (Build_IndexedQueryStructure_Impl_Sigs Index),
        {d' : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls' &
        forall
          ValidImpl : forall
                        idx : BoundedIndex
                                (map ADTSigname
                                   (Build_IndexedQueryStructure_Impl_Sigs
                                      Index)),
                      refineADT
                        (ith_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Specs Index) idx)
                        (ComputationalADT.LiftcADT
                           (ith_Bounded ADTSigname DelegateImpls' idx)),
        Build_IndexedQueryStructure_Impl_AbsR' ValidImpl d d'}) =>
 Notation_Friendly_SharpenFully (inil consDef) (inil methDef)
   (Build_IndexedQueryStructure_Impl_cRep Index)
   (fun
      c : ilist
            (fun nadt : NamedADTSig =>
             ComputationalADT.cADT (namedADTSig nadt))
            (Build_IndexedQueryStructure_Impl_Sigs Index) =>
    inil
      (fun Sig : consSig =>
       ComputationalADT.cConstructorType
         (Build_IndexedQueryStructure_Impl_cRep Index c)
         (consDom Sig)))
   (fun
      c : ilist
            (fun nadt : NamedADTSig =>
             ComputationalADT.cADT (namedADTSig nadt))
            (Build_IndexedQueryStructure_Impl_Sigs Index) =>
    inil
      (fun Sig : methSig =>
       ComputationalADT.cMethodType
         (Build_IndexedQueryStructure_Impl_cRep Index c)
         (methDom Sig) (methCod Sig)))
   (Build_IndexedQueryStructure_Impl_Specs Index)
   (Build_IndexedQueryStructure_Impl_AbsR' (Index:=Index))
   (fun
      (DelegateImpl : ilist
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig Tuple
                                          (BuildIndexSearchTerm
                                             [sAUTHOR; sISBN]%SchemaConstraints)
                                          (Tuple -> Tuple) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig Tuple
                                         (BuildIndexSearchTerm
                                            [sISBN]%SchemaConstraints)
                                         (Tuple -> Tuple) |}])
      (_ : forall idx : BoundedIndex [sBOOKS; sORDERS],
           refineADT
             (ith_Bounded' ADTSigname
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig Tuple
                                  (BuildIndexSearchTerm
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (Tuple -> Tuple) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig Tuple
                                 (BuildIndexSearchTerm
                                    [sISBN]%SchemaConstraints)
                                 (Tuple -> Tuple) |}]
                (nth_error_map ADTSigname (ibound idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                     (BuildIndexSearchTerm
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                    (BuildIndexSearchTerm
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (boundi idx))
                (ith_error
                   (icons
                      (BagSpec MatchIndexSearchTerm
                         (fun z : Tuple -> Tuple => z))
                      (icons
                         (BagSpec MatchIndexSearchTerm
                            (fun z : Tuple -> Tuple => z))
                         (inil (fun ns : NamedADTSig => ADT (namedADTSig ns)))))
                   (ibound idx)))
             (ComputationalADT.LiftcADT
                (ith_Bounded' ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                     (BuildIndexSearchTerm
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                    (BuildIndexSearchTerm
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (nth_error_map ADTSigname (ibound idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig Tuple
                                        (BuildIndexSearchTerm
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (Tuple -> Tuple) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig Tuple
                                       (BuildIndexSearchTerm
                                          [sISBN]%SchemaConstraints)
                                       (Tuple -> Tuple) |}]
                      (boundi idx)) (ith_error DelegateImpl (ibound idx))))) =>
    ())
   (fun
      (DelegateImpl : ilist
                        (fun nadt : NamedADTSig =>
                         ComputationalADT.cADT (namedADTSig nadt))
                        [{|
                         ADTSigname := sBOOKS;
                         namedADTSig := BagSig Tuple
                                          (BuildIndexSearchTerm
                                             [sAUTHOR; sISBN]%SchemaConstraints)
                                          (Tuple -> Tuple) |};
                        {|
                        ADTSigname := sORDERS;
                        namedADTSig := BagSig Tuple
                                         (BuildIndexSearchTerm
                                            [sISBN]%SchemaConstraints)
                                         (Tuple -> Tuple) |}])
      (_ : forall idx : BoundedIndex [sBOOKS; sORDERS],
           refineADT
             (ith_Bounded' ADTSigname
                [{|
                 ADTSigname := sBOOKS;
                 namedADTSig := BagSig Tuple
                                  (BuildIndexSearchTerm
                                     [sAUTHOR; sISBN]%SchemaConstraints)
                                  (Tuple -> Tuple) |};
                {|
                ADTSigname := sORDERS;
                namedADTSig := BagSig Tuple
                                 (BuildIndexSearchTerm
                                    [sISBN]%SchemaConstraints)
                                 (Tuple -> Tuple) |}]
                (nth_error_map ADTSigname (ibound idx)
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                     (BuildIndexSearchTerm
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                    (BuildIndexSearchTerm
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (boundi idx))
                (ith_error
                   (icons
                      (BagSpec MatchIndexSearchTerm
                         (fun z : Tuple -> Tuple => z))
                      (icons
                         (BagSpec MatchIndexSearchTerm
                            (fun z : Tuple -> Tuple => z))
                         (inil (fun ns : NamedADTSig => ADT (namedADTSig ns)))))
                   (ibound idx)))
             (ComputationalADT.LiftcADT
                (ith_Bounded' ADTSigname
                   [{|
                    ADTSigname := sBOOKS;
                    namedADTSig := BagSig Tuple
                                     (BuildIndexSearchTerm
                                        [sAUTHOR; sISBN]%SchemaConstraints)
                                     (Tuple -> Tuple) |};
                   {|
                   ADTSigname := sORDERS;
                   namedADTSig := BagSig Tuple
                                    (BuildIndexSearchTerm
                                       [sISBN]%SchemaConstraints)
                                    (Tuple -> Tuple) |}]
                   (nth_error_map ADTSigname (ibound idx)
                      [{|
                       ADTSigname := sBOOKS;
                       namedADTSig := BagSig Tuple
                                        (BuildIndexSearchTerm
                                           [sAUTHOR; sISBN]%SchemaConstraints)
                                        (Tuple -> Tuple) |};
                      {|
                      ADTSigname := sORDERS;
                      namedADTSig := BagSig Tuple
                                       (BuildIndexSearchTerm
                                          [sISBN]%SchemaConstraints)
                                       (Tuple -> Tuple) |}]
                      (boundi idx)) (ith_error DelegateImpl (ibound idx))))) =>
    ()))).

   Print Universes.
 Defined. *)

Theorem BookStoreManual :
  Sharpened BookStoreSpec.
Proof.

  unfold BookStoreSpec.

  (* First, we unfold various definitions and drop constraints *)
  start honing QueryStructure.

  make simple indexes using [[sAUTHOR; sISBN]; [sISBN]].

  hone constructor "Init".
  {
    simplify with monad laws.
    rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure.
    simpl.
    finish honing.
  }

  hone method "NumOrders".
  {
    simplify with monad laws.
    implement_In.
    setoid_rewrite refine_Join_Enumerate_Swap; eauto.
    convert_Where_to_search_term.

    find_equivalent_search_term 1 find_simple_search_term.
    find_equivalent_search_term_pair 1 0 find_simple_search_term_dep.

    convert_filter_to_find.
    Implement_Aggregates.
    commit.
    finish honing.
  }

  hone method "GetTitles".
  {
    simplify with monad laws.
    implement_In.
    convert_Where_to_search_term.
    find_equivalent_search_term 0 find_simple_search_term.
    convert_filter_to_find.
    Implement_Aggregates.
    commit.
    finish honing.
}

  hone method "DeleteOrder".
  {
    implement_QSDeletedTuples find_simple_search_term.
    simplify with monad laws; cbv beta; simpl.
    implement_EnsembleDelete_AbsR find_simple_search_term.
    simplify with monad laws.
    finish honing.
  }

  (* At this point our implementation is fully computational: we're done! *)

Ltac ilist_of_dep_evar C D B As k :=
  match As with
    | nil => k (fun (c : C) (d : D c) => inil (B c d))
    | cons ?a ?As' =>
      makeEvar (forall c (d : D c), B c d a)
               ltac:(fun b =>
                       ilist_of_dep_evar
                         C D B As'
                         ltac:(fun Bs' => k (fun c (d : D c) => @icons _ _ a As' (b c d) (Bs' c d))))
  end.

  Check Build_IndexedQueryStructure_Impl_AbsR''.

Definition Build_IndexedQueryStructure_Impl_AbsR''
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : ilist (fun nadt : NamedADTSig => Type)
                                 (Build_IndexedQueryStructure_Impl_Sigs Index))
           (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
         (ValidImpls :
              forall idx : BoundedIndex (map relName (qschemaSchemas qs_schema)),
                refineADT (ith_Bounded ADTSigname
                                       (Build_IndexedQueryStructure_Impl_Specs Index) (map_IndexedQS_idx' Index idx))
                          (ComputationalADT.LiftcADT
                             (existT _ _ (i2th_Bounded ADTSigname DelegateImpls (map_IndexedQS_idx' Index idx)))))
           (r_o : IndexedQueryStructure qs_schema Index)
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
: Prop.
  assert (forall idx, ith_Bounded ADTSigname r_n (map_IndexedQS_idx' Index idx) = Rep
    (ComputationalADT.LiftcADT
       (existT
          (fun rep : Type (* ADTSynthesis.ADT.ComputationalADT.10 *) =>
           ComputationalADT.pcADT
             (namedADTSig
                (nth_Bounded ADTSigname
                   (Build_IndexedQueryStructure_Impl_Sigs Index)
                   (map_IndexedQS_idx' Index idx))) rep)
          (ith_Bounded ADTSigname DelegateReps (map_IndexedQS_idx' Index idx))
          (i2th_Bounded ADTSigname DelegateImpls
             (map_IndexedQS_idx' Index idx))))).
  simpl.
  unfold Build_IndexedQueryStructure_Impl_cRep in r_n.
  unfold DelegateReps.
  refine (forall idx : BoundedIndex (map relName (qschemaSchemas qs_schema)),
    AbsR (ValidImpls idx)
         (map_IndexedQS_Rep'' Index idx (GetIndexedRelation r_o idx))
         (ith_Bounded ADTSigname r_n (map_IndexedQS_idx' Index idx))).

Definition Build_IndexedQueryStructure_Impl_AbsR'
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                  (Build_IndexedQueryStructure_Impl_Sigs Index))
           (ValidImpl :
              forall idx,
                refineADT (ith_Bounded ADTSigname
                                       (Build_IndexedQueryStructure_Impl_Specs Index) idx)
                          (LiftcADT (ith_Bounded ADTSigname DelegateImpls idx)))
           (r_o : IndexedQueryStructure qs_schema Index)
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
: Prop :=
  @Build_IndexedQueryStructure_Impl_AbsR''
    qs_schema Index DelegateImpls
    (fun idx => ValidImpl (map_IndexedQS_idx' Index idx))
    r_o
    r_n.

Ltac FullySharpenQueryStructure qs_schema Index :=
  let delegateSigs := constr:(Build_IndexedQueryStructure_Impl_Sigs Index) in
  let delegateSpecs := constr:(Build_IndexedQueryStructure_Impl_Specs Index) in
  let cRep' := constr:(Build_IndexedQueryStructure_Impl_cRep Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR' qs_schema Index) in
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_dep_evar
        (ilist (fun nadt => Type) delegateSigs)
        (fun DelegateImpls => i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) (As := delegateSigs) DelegateImpls)
        (fun DelegateReps
             (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
             Sig => ComputationalADT.cMethodType (cRep' DelegateReps) (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_dep_evar
                  (ilist (fun nadt => Type) delegateSigs)
                  (fun DelegateImpls => i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) (As := delegateSigs) DelegateImpls)
                  (fun DelegateReps
                       (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
                       Sig => ComputationalADT.cConstructorType (cRep' DelegateReps) (consDom Sig))
                  consSigs
                  ltac:(fun cCons =>
                          eapply
                              (@Notation_Friendly_SharpenFully
                               _
                               consSigs
                               methSigs
                               consDefs
                               methDefs
                               delegateSigs
                               cRep'
                               cCons
                               cMeths
                               delegateSpecs)));
        unfold Dep_Type_BoundedIndex_app_comm_cons
  end; simpl; intros;
  [ repeat split; intros; try exact tt; implement_bag_constructors
  | repeat split; intros; try exact tt; implement_bag_methods ].

  Unset Ltac Debug.

  FullySharpenQueryStructure BookStoreSchema Index.

Defined.

Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl.
