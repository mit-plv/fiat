Require Import Coq.Lists.List Coq.Program.Program
        Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.Arith.Arith
        Fiat.Common.ilist2
        Fiat.Common.i2list
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
    ilist2 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns))
      (qschemaSchemas qs_schema).

  Definition IndexedQueryStructure
    := i2list  (fun ns index => Rep (BagSpec (BagMatchSearchTerm index)
                                             (BagApplyUpdateTerm index)))
              BagIndexKeys.

  Definition GetIndexedRelation (r_n : IndexedQueryStructure) idx
    := i2th r_n idx.

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
    Methods (BagSpec (BagMatchSearchTerm (ith2 BagIndexKeys idx))
                     (BagApplyUpdateTerm (ith2 BagIndexKeys idx)))
            midx
            (GetIndexedRelation r_n idx).

  Definition CallBagConstructor {heading} index cidx :=
    Constructors (BagSpec (BagMatchSearchTerm (heading := heading) index)
                          (BagApplyUpdateTerm index))
            cidx.

  Definition DelegateToBag_AbsR
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : IndexedQueryStructure) :=
    (forall idx, GetUnConstrRelation r_o idx = GetIndexedRelation r_n idx)
    (* This invariant allows us to justify refinements which drop
       unused method calls by showing that they are implementable. *)
    /\ (forall idx,
        exists l, EnsembleIndexedListEquivalence (GetUnConstrRelation r_o idx) l).

  Fixpoint Initialize_IndexedQueryStructure
           {n}
          (ns : Vector.t RawSchema n)
          (indices' : ilist2 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns)) ns)
          {struct ns}
  : Comp (i2list (fun ns index =>
                    Rep (BagSpec (BagMatchSearchTerm index)
                                  (BagApplyUpdateTerm index))) indices').
      refine (match ns in (Vector.t _ n) return
             forall indices' : ilist2 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns)) ns,
             Comp (i2list (fun ns index =>
                    Rep (BagSpec (BagMatchSearchTerm index)
                                  (BagApplyUpdateTerm index))) indices') with
      | Vector.nil => fun il => ret i2nil
      | Vector.cons sch _ ns' =>
        fun il =>
          c <- _;
          cs <- (@Initialize_IndexedQueryStructure _ ns' (ilist2_tl il) );
          ret (i2cons c cs)
    end indices').
      exact (CallBagConstructor (ilist2_hd il) BagEmpty tt).
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
