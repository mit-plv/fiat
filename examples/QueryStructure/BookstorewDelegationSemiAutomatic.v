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
      (*Method "DeleteOrder" : rep x nat -> rep x list Order, *)
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

    (*update "DeleteOrder" ( oid : nat ) : list Order :=
      Delete o from sORDERS where o!sISBN = oid, *)

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

(*Definition BooksSearchTerm :=
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
 Defined. *) *)

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

  (*hone method "DeleteOrder".
  {
    implement_QSDeletedTuples find_simple_search_term.
    simplify with monad laws; cbv beta; simpl.
    implement_EnsembleDelete_AbsR find_simple_search_term.
    simplify with monad laws.
    finish honing.
  } *)

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

  Ltac FullySharpenQueryStructure qs_schema Index :=
  let delegateSigs := constr:(Build_IndexedQueryStructure_Impl_Sigs Index) in
  let delegateSpecs := constr:(Build_IndexedQueryStructure_Impl_Specs Index) in
  let cRep' := constr:(Build_IndexedQueryStructure_Impl_cRep Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let DelegateIDs := constr:(map relName (qschemaSchemas qs_schema)) in
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_dep_evar
        (@BoundedString DelegateIDs -> Type)
        (fun D =>
           forall idx,
             ComputationalADT.pcADT (delegateSigs idx) (D idx))
        (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
             (DelegateImpls : forall idx,
                                ComputationalADT.pcADT (delegateSigs idx) (DelegateReps idx))
             (Sig : methSig) => ComputationalADT.cMethodType (cRep' DelegateReps)
                                                             (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_dep_evar
                  (@BoundedString DelegateIDs -> Type)
                  (fun D =>
                     forall idx,
                       ComputationalADT.pcADT (delegateSigs idx) (D idx))
                  (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
                       (DelegateImpls : forall idx,
                                          ComputationalADT.pcADT (delegateSigs idx) (DelegateReps idx))
                       (Sig : consSig) =>
                     ComputationalADT.cConstructorType (cRep' DelegateReps) (consDom Sig))
                  consSigs
                  ltac:(fun cCons =>
                          eapply
                              (@Notation_Friendly_SharpenFully'
                               _
                               consSigs
                               methSigs
                               consDefs
                               methDefs
                               DelegateIDs
                               delegateSigs
                               cRep'
                               cCons
                               cMeths
                               delegateSpecs
                               cAbsR'
                              )));
        unfold Dep_Type_BoundedIndex_app_comm_cons
  end; simpl; intros.

  FullySharpenQueryStructure BookStoreSchema Index.

  Definition Initialize_IndexedQueryStructureImpls'
         {indices}
         Index
         (DelegateReps : @BoundedString (map relName indices) -> Type)
         (DelegateImpls : forall idx,
                            ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
: @Build_IndexedQueryStructure_Impl_cRep _ Index DelegateReps :=
    (fun idx => ComputationalADT.pcConstructors (DelegateImpls idx)
                                                {| bindex := "Empty" |} ()).

Ltac higher_order_1_reflexivity'' :=
  let x := match goal with |- ?R (ret ?x) (ret (?f ?a)) => constr:(x) end in
  let f := match goal with |- ?R (ret ?x) (ret (?f ?a)) => constr:(f) end in
  let a := match goal with |- ?R (ret ?x) (ret (?f ?a)) => constr:(a) end in
  let x' := (eval pattern a in x) in
  let f' := match x' with ?f' _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_2_reflexivity'' :=
  let x := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(x) end in
  let f := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(f) end in
  let a := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(a) end in
  let b := match goal with |- ?R (ret ?x) (ret (?f ?a ?b)) => constr:(b) end in
  let x' := (eval pattern a, b in x) in
  let f' := match x' with ?f' _ _ => constr:(f') end in
  unify f f';
    cbv beta;
    solve [apply reflexivity].

Definition CallBagImplMethod
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx midx
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps) :=
  ComputationalADT.pcMethods (DelegateImpls idx) midx (r_n idx).

Definition CallBagImplConstructor
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx cidx :=
  ComputationalADT.pcConstructors (DelegateImpls idx) cidx.

Lemma refine_BagImplConstructor
      {qs_schema : QueryStructureSchema}
      (indices := qschemaSchemas qs_schema)
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
      (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
      (DelegateImpls : forall idx,
                         ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
      (ValidImpls
       : forall idx,
           refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
:  forall (ridx : BoundedIndex (map relName (qschemaSchemas qs_schema))) cidx d,
   exists r_o' ,
     refine (@CallBagConstructor _ (bindex ridx) (ith_Bounded relName Index ridx) cidx d)
            (ret r_o') /\
         AbsR (ValidImpls ridx) r_o' (CallBagImplConstructor DelegateReps DelegateImpls cidx d).
Proof.
  intros.
  pose proof (ADTRefinementPreservesConstructors (ValidImpls ridx) cidx d (ReturnComputes _)).
  inversion_by computes_to_inv; subst.
  exists x;
    unfold CallBagImplConstructor; simpl in *.
  split; simpl.
  - intros v Comp_v; inversion_by computes_to_inv; subst.
    generalize d v H0; clear.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H cidx).
    simpl; intuition.
  - eapply H1.
Qed.

Ltac implement_bag_constructors :=
  repeat match goal with
           | |- context[ Pick (fun r_n : @Build_IndexedQueryStructure_Impl_cRep ?qs_schema ?Index ?DelegateReps =>
                                 @Build_IndexedQueryStructure_Impl_AbsR
                                   _ _ ?DelegateReps ?DelegateImpls
                                   ?ValidImpls ?r_o r_n)] =>
             refine pick val (@Initialize_IndexedQueryStructureImpls' qs_schema Index DelegateReps DelegateImpls);
               [ higher_order_2_reflexivity'' |
                 unfold Build_IndexedQueryStructure_Impl_AbsR;
                   eapply Iterate_Dep_Type_BoundedIndex_equiv_1; simpl; intuition ]
           | |- context[CallBagConstructor ?ridx ?cidx ?d] =>
             match goal with
                 |- appcontext[@Build_IndexedQueryStructure_Impl_AbsR
                                 ?qs_schema ?Index
                                 ?DelegateReps ?DelegateImpls ?ValidImpls] =>
                 let r_o' := fresh "r_o'" in
                 let AbsR_r_o' := fresh "AbsR_r_o'" in
                 let refines_r_o' := fresh "refines_r_o'" in
                 destruct (@refine_BagImplConstructor
                             qs_schema Index DelegateReps DelegateImpls ValidImpls
                             {|bindex := ridx |} cidx d) as [r_o' [refines_r_o' AbsR_r_o']];
                   setoid_rewrite refines_r_o'; simpl in *; simplify with monad laws; simpl
             end
         end.
repeat split; intros; try exact tt; implement_bag_constructors.
repeat split; intros; try exact tt.

Definition Join_Lists'
           {A : Type} {f : A -> Type} {As : list A} {a : A}
           (l : list (ilist f As)) (c : ilist f As -> list (f a))
  := flatten (map
                (fun l' => map (fun fa : f a => icons fa l') (c l')) l).

Lemma Join_Lists_Impl {A : Type} {f : A -> Type} {As : list A} {a : A}
: forall (l : list (ilist f As))
         (c : ilist f As -> Comp (list (f a)))
         (c' : ilist f As -> list (f a)),
    (forall a', refine (c a') (ret (c' a')))
    -> refine (Join_Lists l c) (ret (Join_Lists' l c')).
Proof.
  induction l; unfold Join_Lists, Join_Lists'; simpl; intros.
  - reflexivity.
  - rewrite H; simplify with monad laws.
    setoid_rewrite IHl; eauto; simplify with monad laws.
    reflexivity.
Qed.

Lemma refine_BagImplMethods
      {qs_schema : QueryStructureSchema}
      (indices := qschemaSchemas qs_schema)
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
      (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
      (DelegateImpls : forall idx,
                         ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
      (ValidImpls
       : forall idx,
           refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
:  forall (r_o : IndexedQueryStructure qs_schema Index)
          (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
          ridx,
     Build_IndexedQueryStructure_Impl_AbsR DelegateImpls ValidImpls r_o r_n ->
     forall midx
            d,
       exists r_o',
         refine (CallBagMethod ridx midx r_o d)
                (ret (r_o',
                      (snd (CallBagImplMethod DelegateImpls midx r_n d))))
         /\ AbsR (ValidImpls ridx) r_o' (fst (CallBagImplMethod DelegateImpls midx r_n d)).
Proof.
  intros.
  pose proof (ADTRefinementPreservesMethods (ValidImpls ridx) midx
                                            (GetIndexedRelation r_o ridx)
                                            (r_n ridx) d (H ridx) (ReturnComputes _)).
  inversion_by computes_to_inv; subst.
  exists (fst x);
    unfold CallBagImplMethod; simpl in *.
  split; simpl.
  - pose proof (f_equal snd H3) as eq_x; simpl in eq_x.
    assert (refine (CallBagMethod ridx midx r_o d)
                   (ret (fst x, snd x)));
      [ | rewrite eq_x in H3;
          unfold ComputationalADT.cMethods in eq_x; simpl in *; rewrite <- eq_x; eapply H0].
    intros v Comp_v; simpl in *; inversion_by computes_to_inv; subst.
    destruct x; simpl @fst in *; simpl @snd in *.
    generalize d i m H1 H2; clear.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H midx).
    simpl; intuition.
  - unfold ComputationalADT.cMethods in H3; simpl in *; rewrite <- H3; eapply H2.
Qed.

Ltac implement_bag_methods :=
  repeat
    match goal with
      | |- refine (ret _) (ret (?f ?a ?b)) => higher_order_2_reflexivity''
      | |- refine (ret _) (ret (?f ?a)) => higher_order_1_reflexivity''
      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- context[
               { r_n' | @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o r_n'}
                ] => refine pick val _;
           [ simplify with monad laws |
             eapply H]

      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- context[CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?d] =>
        let r_o' := fresh "r_o'" in
        let AbsR_r_o' := fresh "AbsR_r_o'" in
        let refines_r_o' := fresh "refines_r_o'" in
        destruct (@refine_BagImplMethods qs_schema Index' DelegateReps DelegateImpls ValidImpls r_o r_n ridx H midx d) as [r_o' [refines_r_o' AbsR_r_o']];
          simpl in refines_r_o', AbsR_r_o';
          setoid_rewrite refines_r_o'; simpl in *; simplify with monad laws; simpl

      | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                   ?ValidImpls ?r_o ?r_n
        |- context[Join_Lists (As := ?As) (f := ?f) (a := ?a) ?l ?c ] =>
        makeEvar (ilist f As -> list (f a))
                 ltac:(fun c' =>
                         let refines_c' := fresh in
                         assert (forall a', refine (c a') (ret (c' a'))) as refines_c';
                       [intros; try implement_bag_methods
                       | setoid_rewrite (Join_Lists_Impl l c c' refines_c');
                         simpl in *; setoid_rewrite (refineEquiv_bind_unit);
                         implement_bag_methods
                       ])

    end.

implement_bag_methods.
implement_bag_methods.

Defined.

Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl.
