Require Import Coq.Lists.List Coq.Program.Program
        Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.Arith.Arith
        Fiat.Common.ilist3
        Fiat.Common.i3list
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Computation
        Fiat.ADT
        Fiat.ADTRefinement
        Fiat.ADTNotation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.QueryStructureSchema
        Fiat.QueryStructure.Specification.Representation.QueryStructure
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT.

Require Export Fiat.Common.ilist3_pair
        Fiat.Common.ilist3
        Fiat.Common.i3list2
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagImplementation.

Ltac list_of_evar B As k :=
  match As with
    | nil => k (@nil B)
    | cons ?a ?As' =>
      makeEvar B ltac:(fun b =>
                         list_of_evar
                           B As' ltac:(fun Bs => k (cons b Bs)))
  end.

Lemma ValidUpdateCorrect
  : forall (A : Prop), false = true -> A.
Proof.
  intros; discriminate.
Qed.


  Definition foo := (SharpenedBagImpl
                             (fun
                                _ : IndexedTreeUpdateTermType
                                      {|
                                      NumAttr := 2;
                                      AttrList := [nat : Type; nat : Type]%NamedSchema |} =>
                              false)
                             (NatTreeBag.IndexedBagAsCorrectBag
                                (CountingListAsBag
                                   (IndexedTreebupdate_transform
                                      {|
                                      NumAttr := 2;
                                      AttrList := [nat : Type; nat : Type]%NamedSchema |}))
                                CountingList_RepInv CountingList_ValidUpdate
                                (CountingListAsCorrectBag
                                   (IndexedTreebupdate_transform
                                      {|
                                      NumAttr := 2;
                                      AttrList := [nat : Type; nat : Type]%NamedSchema |}))
                                (fun x : RawTuple => GetAttributeRaw x Fin.F1))
                             (fun
                                (a : IndexedTreeUpdateTermType
                                       {|
                                       NumAttr := 2;
                                       AttrList := [nat : Type; nat : Type]%NamedSchema |})
                                (b : false = true) =>
                              ValidUpdateCorrect
                                (NatTreeBag.IndexedBag_ValidUpdate
                                   (CountingListAsBag
                                      (IndexedTreebupdate_transform
                                         {|
                                         NumAttr := 2;
                                         AttrList := [nat : Type; nat : Type]%NamedSchema |}))
                                   CountingList_ValidUpdate
                                   (fun x : RawTuple =>
                                    GetAttributeRaw x Fin.F1) a) b)).

Section QueryStructureImplementation.

  Variable qs_schema : RawQueryStructureSchema.

  (* Build an index requires search terms and matchers for each schema,
     and update terms and updaters for each schema. *)

  Record SearchUpdateTerms (heading : RawHeading) :=
    {  BagSearchTermType : Type;
       BagMatchSearchTerm : BagSearchTermType -> @RawTuple heading -> bool;
       BagUpdateTermType : Type;
       BagApplyUpdateTerm : BagUpdateTermType -> @RawTuple heading -> @RawTuple heading }.

  Variable BagIndexKeys :
    ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns))
      (qschemaSchemas qs_schema).

  Definition IndexedQueryStructure
    := i3list  (fun ns index => Rep (BagSpec (BagMatchSearchTerm index)
                                             (BagApplyUpdateTerm index)))
               BagIndexKeys.

  Definition GetIndexedRelation (r_n : IndexedQueryStructure) idx
    := i3th r_n idx.

  Definition BagEmpty
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (ConstructorIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := ConstructorNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index))) {| bindex := "Empty" |}).

  Definition BagEnumerate
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
      {| bindex := "Enumerate" |}).

  Definition BagFind
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
      {| bindex := "Find" |}).

  Definition BagCount
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index))) {| bindex := "Count" |}).

  Definition BagInsert
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Insert" |}).

  Definition BagUpdate
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Update" |}).

  Definition BagDelete
             {heading : RawHeading} {index : SearchUpdateTerms heading}
  : (MethodIndex (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
    := ibound (indexb (Bound := MethodNames (BagSig (@RawTuple heading) (BagSearchTermType index) (BagUpdateTermType index)))
                      {| bindex := "Delete" |}).

  Definition CallBagMethod idx midx r_n :=
    Methods (BagSpec (BagMatchSearchTerm (ith3 BagIndexKeys idx))
                     (BagApplyUpdateTerm (ith3 BagIndexKeys idx)))
            midx
            (GetIndexedRelation r_n idx).

  Definition CallBagConstructor {heading} index cidx :=
    Constructors (BagSpec (BagMatchSearchTerm (heading := heading) index)
                          (BagApplyUpdateTerm index))
            cidx.

  Definition DelegateToBag_AbsR
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : IndexedQueryStructure) :=
    (*forall idx, GetUnConstrRelation r_o idx = GetIndexedRelation r_n idx*)
    (* This invariant allows us to justify refinements which drop
       unused method calls by showing that they are implementable. *)
    (forall idx,
        exists l, EnsembleIndexedListEquivalence (GetUnConstrRelation r_o idx) l /\
                  EnsembleIndexedListEquivalence (GetIndexedRelation r_n idx) l).

  Fixpoint Initialize_IndexedQueryStructure
           {n}
          (ns : Vector.t RawSchema n)
          (indices' : ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns)) ns)
          {struct ns}
    : Comp (i3list (fun ns index => Rep (BagSpec (BagMatchSearchTerm index)
                                                 (BagApplyUpdateTerm index))) indices').
  Proof.
      refine (match ns in (Vector.t _ n) return
             forall indices' : ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns)) ns,
             Comp (i3list (fun ns index =>
                    Rep (BagSpec (BagMatchSearchTerm index)
                                  (BagApplyUpdateTerm index))) indices') with
      | Vector.nil => fun il => ret i3nil
      | Vector.cons sch _ ns' =>
        fun il =>
          c <- _;
          cs <- (@Initialize_IndexedQueryStructure _ ns' (ilist3_tl il) );
          ret (i3cons c cs)
    end indices').
      exact (CallBagConstructor (ilist3_hd il) BagEmpty tt).
      Grab Existential Variables.
      exact (fun ns index =>
               Rep (BagSpec (BagMatchSearchTerm (heading := ns) index)
                            (BagApplyUpdateTerm index))).
  Defined.

End QueryStructureImplementation.

Opaque CallBagMethod.
Arguments CallBagMethod : simpl never.
Arguments CallBagMethod [_ _] _ _ _ _ _.
Opaque CallBagConstructor.
Arguments CallBagConstructor : simpl never.
Arguments GetIndexedRelation [_ _ ] _ _ _.
Arguments DelegateToBag_AbsR [_ _] _ _.
