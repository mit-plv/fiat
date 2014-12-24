Require Import Coq.Lists.List Coq.Program.Program
        Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.Arith.Arith
        ADTSynthesis.Common.ilist
        ADTSynthesis.Common.i2list
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Computation
        ADTSynthesis.ADT
        ADTSynthesis.ADTRefinement
        ADTSynthesis.ADTNotation
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureSchema
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructure
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT.

Section QueryStructureImplementation.

  Variable qs_schema : QueryStructureSchema.

  (* Build an index requires search terms and matchers for each schema,
     and update terms and updaters for each schema. *)

  Record SearchUpdateTerms (heading : Heading) :=
    {  BagSearchTermType : Type;
       BagMatchSearchTerm : BagSearchTermType -> @Tuple heading -> bool;
       BagUpdateTermType : Type;
       BagApplyUpdateTerm : BagUpdateTermType -> @Tuple heading -> @Tuple heading }.

  Variable BagIndexKeys :
    ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
      (qschemaSchemas qs_schema).

  Definition IndexedQueryStructure
    := i2list (A := NamedSchema)
              (fun ns index => Rep (BagSpec (BagMatchSearchTerm index)
                                            (BagApplyUpdateTerm index)))
              BagIndexKeys.

  Definition GetIndexedRelation (r_n : IndexedQueryStructure) idx
    := i2th_Bounded relName r_n idx.

  Definition CallBagMethod idx midx r_n :=
    Methods (BagSpec (BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx))
                     (BagApplyUpdateTerm (ith_Bounded relName BagIndexKeys idx)))
            midx
            (GetIndexedRelation r_n idx).

  Definition CallBagConstructor {heading} (name : string) index cidx :=
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
          (ns : list NamedSchema)
          (indices' : ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns))) ns)
          {struct indices'}
  : Comp (i2list (fun ns index =>
                    Rep (BagSpec (BagMatchSearchTerm index)
                                  (BagApplyUpdateTerm index))) indices')
    := match indices' return Comp (i2list _ indices') with
      | inil => ret (i2nil _ _)
      | icons ns ns' index indices'' =>
        c <- (CallBagConstructor (relName ns) index {|bindex := "Empty" |} tt);
          cs <- (@Initialize_IndexedQueryStructure ns' indices'');
          ret (i2cons (icons ns index indices'') c cs)
    end.

End QueryStructureImplementation.

Opaque CallBagMethod.
Arguments CallBagMethod : simpl never.
Opaque CallBagConstructor.
Arguments CallBagConstructor : simpl never.
