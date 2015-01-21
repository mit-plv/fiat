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

Record SharpenedUnderDelegates' (Sig : ADTSig)
  : Type
  := Build_SharpenedUnderDelegates
       { Sharpened_DelegateSigs : list NamedADTSig;
         Sharpened_Implementation :
           forall (DelegateReps : ilist (fun nadt : NamedADTSig => Type) Sharpened_DelegateSigs)
                  (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
             ComputationalADT.cADT Sig;
         Sharpened_DelegateSpecs : ilist (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                                         Sharpened_DelegateSigs }.

Definition FullySharpenedUnderDelegates'
           (Sig : ADTSig) (spec : ADT Sig) (adt : SharpenedUnderDelegates' Sig)
  := forall (DelegateReps : ilist (fun nadt : NamedADTSig => Type) (Sharpened_DelegateSigs adt))
            (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
            (ValidImpls : forall idx : BoundedIndex (map ADTSigname (Sharpened_DelegateSigs adt)),
                            refineADT (ith_Bounded ADTSigname (Sharpened_DelegateSpecs adt) idx)
                                      (ComputationalADT.LiftcADT
                                         (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))), 
  refineADT spec
            (ComputationalADT.LiftcADT (Sharpened_Implementation adt DelegateImpls)).

Definition Notation_Friendly_BuildMostlySharpenedcADT'
           (consSigs : list consSig) (methSigs : list methSig)
           (DelegateSigs : list NamedADTSig)
           (rep : ilist (fun nadt : NamedADTSig => Type) DelegateSigs ->
                  Type
           (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.2502 *))
           (cConstructors :
              forall
                (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
                ilist
                  (fun Sig : consSig =>
                     ComputationalADT.cConstructorType (rep DelegateReps) (consDom Sig))
                  consSigs)
           (cMethods :
              forall                
                (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
        ilist
          (fun Sig : methSig =>
           ComputationalADT.cMethodType (rep DelegateReps) 
                                        (methDom Sig) (methCod Sig)) methSigs)
           (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
           (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
: ComputationalADT.cADT (BuildADTSig consSigs methSigs) :=
  BuildcADT
  (imap cConsDef (Build_cConsDef (Rep:=rep DelegateReps))
     (cConstructors DelegateReps DelegateImpls))
  (imap cMethDef (Build_cMethDef (Rep:=rep DelegateReps))
     (cMethods DelegateReps DelegateImpls)).

Variable Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT'
     : forall
         (RepT : Type
                 (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.2538 *))
         (consSigs : list consSig) (methSigs : list methSig)
         (consDefs : ilist consDef consSigs)
         (methDefs : ilist methDef methSigs)
         (DelegateSigs : list NamedADTSig)
         (rep : ilist (fun nadt : NamedADTSig => Type) DelegateSigs ->
                Type
                (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.2563 *))
         (cConstructors : forall
                            (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                            (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),                          
                          ilist
                            (fun Sig : consSig =>
                             ComputationalADT.cConstructorType
                               (rep DelegateReps) (consDom Sig)) consSigs)
         (cMethods : forall
                       (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                       (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
                     ilist
                       (fun Sig : methSig =>
                        ComputationalADT.cMethodType 
                          (rep DelegateReps) (methDom Sig) 
                          (methCod Sig)) methSigs)
         (DelegateSpecs : ilist
                            (fun (nadt : NamedADTSig) => ADT (namedADTSig nadt))
                            DelegateSigs)
         (cAbsR : forall
                    (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                    (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
                    (forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                       refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT
                                    (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))) ->
                    RepT -> rep DelegateReps -> Prop),
         (forall
             (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
             (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
             (ValidImpls : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                          (ComputationalADT.LiftcADT
                             (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
        Iterate_Dep_Type_BoundedIndex
          (fun idx : BoundedIndex (map consID consSigs) =>
           forall d : consDom (nth_Bounded consID consSigs idx),
           exists r_o' : RepT,
             cAbsR DelegateReps DelegateImpls ValidImpls r_o'
               (ith_Bounded consID (cConstructors DelegateReps DelegateImpls) idx d) /\
             getConsDef consDefs idx d ↝ r_o')) ->
         (forall
             (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
             (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
             (ValidImpls : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                          (ComputationalADT.LiftcADT
                             (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
        Iterate_Dep_Type_BoundedIndex
          (fun idx : BoundedIndex (map methID methSigs) =>
           forall (d : methDom (nth_Bounded methID methSigs idx))
             (r_o : RepT) (r_n : rep DelegateReps),
           cAbsR DelegateReps DelegateImpls ValidImpls r_o r_n ->
           exists r_o' : RepT,
             cAbsR DelegateReps DelegateImpls ValidImpls r_o'
               (fst (ith_Bounded methID (cMethods DelegateReps DelegateImpls) idx r_n d)) /\
             getMethDef methDefs idx r_o d
             ↝ (r_o',
                snd (ith_Bounded methID (cMethods DelegateReps DelegateImpls) idx r_n d)))) -> 
       FullySharpenedUnderDelegates' (BuildADT consDefs methDefs)
         {|
         Sharpened_DelegateSigs := DelegateSigs;
         Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT'
                                       rep cConstructors cMethods;
         Sharpened_DelegateSpecs := DelegateSpecs |}.

Print Sharpened.

Definition Notation_Friendly_SharpenFully'
         (RepT : Type
                 (* ADTSynthesis.ADTRefinement.GeneralBuildADTRefinements.3049 *))
         (consSigs : list consSig) (methSigs : list methSig)
         (consDefs : ilist consDef consSigs)
         (methDefs : ilist methDef methSigs)
         (DelegateSigs : list NamedADTSig)
         (rep : ilist (fun nadt : NamedADTSig => Type) DelegateSigs -> Type)
         (cConstructors :
            forall
              (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
              (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
              ilist
                (fun Sig : consSig =>
                   ComputationalADT.cConstructorType
                     (rep DelegateReps) (consDom Sig)) consSigs)
         (cMethods :
            forall
              (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
              (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
              ilist
                (fun Sig : methSig =>
                   ComputationalADT.cMethodType 
                     (rep DelegateReps) (methDom Sig) 
                     (methCod Sig)) methSigs)
         (DelegateSpecs : ilist
                            (fun nadt : NamedADTSig => ADT (namedADTSig nadt))
                            DelegateSigs)
         (cAbsR : forall
                    (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
                    (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps),
                    (forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                       refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                                 (ComputationalADT.LiftcADT
                                    (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))) ->
                    RepT -> rep DelegateReps -> Prop)
         (cConstructorsRefinesSpec :
            forall
              (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
              (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
              (ValidImpls : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                              refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                                        (ComputationalADT.LiftcADT
                                           (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
              Iterate_Dep_Type_BoundedIndex
                (fun idx : BoundedIndex (map consID consSigs) =>
                   forall d : consDom (nth_Bounded consID consSigs idx),
                   exists r_o' : RepT,
                     cAbsR DelegateReps DelegateImpls ValidImpls r_o'
                           (ith_Bounded consID (cConstructors DelegateReps DelegateImpls) idx d) /\
                     getConsDef consDefs idx d ↝ r_o')) 
         (cMethodsRefinesSpec :
            forall
              (DelegateReps : ilist (fun nadt : NamedADTSig => Type) DelegateSigs)
              (DelegateImpls : i2list (fun (nadt : NamedADTSig) rep => ComputationalADT.pcADT (namedADTSig nadt) rep) DelegateReps)
              (ValidImpls : forall idx : BoundedIndex (map ADTSigname DelegateSigs),
                              refineADT (ith_Bounded ADTSigname DelegateSpecs idx)
                                        (ComputationalADT.LiftcADT
                                           (existT _ _ (i2th_Bounded ADTSigname DelegateImpls idx)))),
              Iterate_Dep_Type_BoundedIndex
                (fun idx : BoundedIndex (map methID methSigs) =>
                   forall (d : methDom (nth_Bounded methID methSigs idx))
                          (r_o : RepT) (r_n : rep DelegateReps),
                     cAbsR DelegateReps DelegateImpls ValidImpls r_o r_n ->
                     exists r_o' : RepT,
                       cAbsR DelegateReps DelegateImpls ValidImpls r_o'
                             (fst (ith_Bounded methID (cMethods DelegateReps DelegateImpls) idx r_n d)) /\
                       getMethDef methDefs idx r_o d
                                  ↝ (r_o',
                                     snd (ith_Bounded methID (cMethods DelegateReps DelegateImpls) idx r_n d))))
       : (sigT (fun adt => FullySharpenedUnderDelegates' (BuildADT consDefs methDefs) adt))  :=
  existT (FullySharpenedUnderDelegates' (BuildADT consDefs methDefs))
  {|
  Sharpened_DelegateSigs := DelegateSigs;
  Sharpened_Implementation := Notation_Friendly_BuildMostlySharpenedcADT' rep
                                cConstructors cMethods;
  Sharpened_DelegateSpecs := DelegateSpecs |}
  (Notation_Friendly_FullySharpened_BuildMostlySharpenedcADT' consDefs
     methDefs rep cConstructors cMethods DelegateSpecs cAbsR
     cConstructorsRefinesSpec cMethodsRefinesSpec).

Print Universes.

Print Build_IndexedQueryStructure_Impl_cRep.

Definition Build_IndexedQueryStructure_Impl_cRep 
           (indices : list NamedSchema)
           (Index : ilist
                      (fun ns : NamedSchema =>
                         SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (DelegateReps : ilist (fun ns : NamedADTSig => Type) (Build_IndexedQueryStructure_Impl_Sigs Index)) :=
  ilist
    (fun (ns : NamedADTSig) (index : ComputationalADT.cADT (namedADTSig ns)) =>
       ComputationalADT.cRep index) DelegateReps.

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
 forall cReps, @Notation_Friendly_SharpenFully'
   (IndexedQueryStructure BookStoreSchema Index) []
   []
   (@inil consSig (@consDef (IndexedQueryStructure BookStoreSchema Index)))
   (@inil methSig (@methDef (IndexedQueryStructure BookStoreSchema Index)))
   (@Build_IndexedQueryStructure_Impl_Sigs
      [relation sBOOKS has (BookSchema')%NamedSchema;
      relation sORDERS has (schema <sISBN :: nat, sDATE :: nat>)%NamedSchema]
      Index)
   (@Build_IndexedQueryStructure_Impl_cRep
      [relation sBOOKS has (BookSchema')%NamedSchema;
      relation sORDERS has (schema <sISBN :: nat, sDATE :: nat>)%NamedSchema]
      Index))).


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
 Defined.

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

  Set Printing Universes.

  Print unroll_ilist.
  Check @Build_IndexedQueryStructure_Impl_cRep.
  Print Universes.
  Print Computation.Core.
  FullySharpenQueryStructure BookStoreSchema Index.

Defined.

Definition BookStoreImpl : ComputationalADT.cADT BookStoreSig.
  extract implementation of BookStoreManual using (inil _).
Defined.

Print BookStoreImpl.
