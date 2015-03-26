Require Export Coq.Bool.Bool Coq.Strings.String Coq.Strings.Ascii.
Open Scope string.
Require Export ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.List.ListMorphisms
        ADTSynthesis.Common.List.ListFacts
        ADTSynthesis.Common.BoolFacts
        ADTSynthesis.Common.LogicFacts
        ADTSynthesis.Common.List.FlattenList
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListInclusion
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListPrefix
        ADTSynthesis.QueryStructure.Specification.SearchTerms.InRange
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        ADTSynthesis.QueryStructure.Automation.General.QueryAutomation
        ADTSynthesis.QueryStructure.Automation.General.InsertAutomation
        ADTSynthesis.QueryStructure.Automation.General.DeleteAutomation
        ADTSynthesis.QueryStructure.Automation.General.QueryStructureAutomation
        ADTSynthesis.QueryStructure.Automation.Constraints.TrivialConstraintAutomation
        ADTSynthesis.QueryStructure.Automation.Constraints.FunctionalDependencyAutomation
        ADTSynthesis.QueryStructure.Automation.Constraints.ForeignKeyAutomation
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagImplementation
        ADTSynthesis.QueryStructure.Implementation.ListImplementation
        ADTSynthesis.QueryStructure.Specification.Constraints.tupleAgree
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Implementation.Operations.BagADT.Refinements
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        ADTSynthesis.QueryStructure.Automation.SearchTerms.InvertedSearchTerms
        ADTSynthesis.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        ADTSynthesis.QueryStructure.Automation.SearchTerms.RangeSearchTerms.

Require Export ADTSynthesis.QueryStructure.Implementation.Operations.

Require Import ADTSynthesis.ADTNotation.BuildComputationalADT.
Require Import ADTSynthesis.ADT.ComputationalADT.
Require Import Coq.Logic.Eqdep_dec.

Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- eq_N_dec_bool_true_iff;
  try setoid_rewrite <- eq_Z_dec_bool_true_iff;
  try setoid_rewrite <- string_dec_bool_true_iff;
  try setoid_rewrite <- ascii_dec_bool_true_iff;
  setoid_rewrite and_True;
  repeat progress (
           try setoid_rewrite <- andb_true_iff;
           try setoid_rewrite not_true_iff_false;
           try setoid_rewrite <- negb_true_iff);
  rewrite bool_equiv_true;
  reflexivity.

Hint Extern 100 (DecideableEnsemble _) => prove_decidability_for_functional_dependencies : typeclass_instances.

Ltac lmap A f seq :=
  let rec aux seq :=
      match seq with
        | nil => constr:(@nil A)
        | ?h :: ?t =>
          let h' := f h in
          let t' := aux t in
          constr:(h' :: t')
      end
  in aux seq.

Ltac FullySharpenEachMethod delegateSigs delegateSpecs cRep' cAbsR' :=
  match goal with
      |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
      ilist_of_evar
        (ilist (fun nadt => ComputationalADT.cADT (namedADTSig nadt)) delegateSigs)
        (fun DelegateImpl Sig => ComputationalADT.cMethodType (cRep' DelegateImpl) (methDom Sig) (methCod Sig))
        methSigs
        ltac:(fun cMeths =>
                ilist_of_evar
                  (ilist (fun nadt => ComputationalADT.cADT (namedADTSig nadt)) delegateSigs)
                  (fun DelegateImpl Sig => ComputationalADT.cConstructorType (cRep' DelegateImpl) (consDom Sig))
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
                               delegateSpecs
                               cAbsR')))
  end; simpl; repeat split.

Definition Build_IndexedQueryStructure_Impl_Sigs
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (idx : @BoundedString (map relName indices))
: ADTSig :=
  BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices idx))))
         (BagSearchTermType (ith_Bounded _ Index idx))
         (BagUpdateTermType (ith_Bounded _ Index idx)).

Definition Build_IndexedQueryStructure_Impl_Specs
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (idx : @BoundedString (map relName indices))
: ADT (@Build_IndexedQueryStructure_Impl_Sigs indices Index idx) :=
  @BagSpec (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices idx))))
           (BagSearchTermType (ith_Bounded _ Index idx))
           (BagUpdateTermType (ith_Bounded _ Index idx))
           (BagMatchSearchTerm (ith_Bounded _ Index idx))
           (BagApplyUpdateTerm (ith_Bounded _ Index idx)).

Definition
  Build_IndexedQueryStructure_Impl_cRep
  (indices : list NamedSchema)
  (Index : ilist
             (fun ns : NamedSchema =>
                SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
  (DelegateReps : @BoundedString (map relName indices) -> Type)
: Type :=
  Iterate_Dep_Type_BoundedIndex DelegateReps.

Definition
  GetIndexedQueryStructureRelation
  {indices : list NamedSchema}
  {Index : ilist
             (fun ns : NamedSchema =>
                SearchUpdateTerms (schemaHeading (relSchema ns))) indices}
  {DelegateReps : @BoundedString (map relName indices) -> Type}
  (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
  idx
: DelegateReps idx :=
  match idx with
      {|bindex := idx;
        indexb := {| ibound := n;
                     boundi := nth_n |} |} =>
      Lookup_Iterate_Dep_Type string_dec DelegateReps r_n n nth_n
  end.

Definition Build_IndexedQueryStructure_Impl_AbsR
           {qs_schema : QueryStructureSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
           (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           (ValidImpls
            : forall idx,
                refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                          (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
           (r_o : IndexedQueryStructure qs_schema Index)
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
: Prop :=
  forall idx : @BoundedString (map relName (qschemaSchemas qs_schema)),
    AbsR (ValidImpls idx)
         (GetIndexedRelation r_o idx) (GetIndexedQueryStructureRelation r_n idx).

Definition CallBagImplMethod
           {schemas : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (schemas))
           (DelegateReps : @BoundedString (map relName schemas) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx midx
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps) :=
  ComputationalADT.pcMethods (DelegateImpls idx) midx (GetIndexedQueryStructureRelation r_n idx).

Definition CallBagImplConstructor
           {schemas : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) schemas )
           (DelegateReps : @BoundedString (map relName schemas) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx cidx :=
  ComputationalADT.pcConstructors (DelegateImpls idx) cidx.

Lemma refine_BagImplConstructor
      {schemas : list NamedSchema}
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) schemas )
      (DelegateReps : @BoundedString (map relName schemas) -> Type)
      (DelegateImpls : forall idx,
                         ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
      (ValidImpls
       : forall idx,
           refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                     (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
:  forall (ridx : BoundedIndex (map relName schemas)) cidx d,
   exists r_o' ,
     refine (@CallBagConstructor _ (bindex ridx) (ith_Bounded relName Index ridx) cidx d)
            (ret r_o') /\
     AbsR (ValidImpls ridx) r_o' (CallBagImplConstructor DelegateReps DelegateImpls cidx d).
Proof.
  intros.
  pose proof (ADTRefinementPreservesConstructors (ValidImpls ridx) cidx d _ (ReturnComputes _)).
   computes_to_inv; subst.
  exists v;
    unfold CallBagImplConstructor in *; simpl in *.
  split; simpl.
  - intros v' Comp_v;  computes_to_inv; subst.
    generalize d v' H; clear.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H cidx).
    simpl; intuition.
  - eapply H'.
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
     Build_IndexedQueryStructure_Impl_AbsR DelegateReps DelegateImpls ValidImpls r_o r_n ->
     forall midx
            d,
     exists r_o',
       refine (CallBagMethod ridx midx r_o d)
              (ret (r_o',
                    (snd (CallBagImplMethod DelegateReps DelegateImpls midx r_n d))))
       /\ AbsR (ValidImpls ridx) r_o' (fst (CallBagImplMethod DelegateReps DelegateImpls midx r_n d)).
Proof.
  intros.
  pose proof (ADTRefinementPreservesMethods (ValidImpls ridx) midx
                                            (GetIndexedRelation r_o ridx)
                                            (GetIndexedQueryStructureRelation r_n ridx) d (H ridx) _ (ReturnComputes _)).
   computes_to_inv; subst.
  exists (fst v);
    unfold CallBagImplMethod; simpl in *.
  split; simpl.
  - pose proof (f_equal snd H0'') as eq_x; simpl in eq_x.
    assert (refine (CallBagMethod ridx midx r_o d)
                   (ret (fst v, snd v)));
      [ | rewrite eq_x in H0'';
          unfold ComputationalADT.cMethods in eq_x; simpl in *; rewrite <- eq_x].
    intros v' Comp_v; simpl in *;  computes_to_inv; subst.
    destruct v; simpl @fst in *; simpl @snd in *.
    generalize d i m H H0; clear.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H midx).
    simpl; intuition.
    eassumption.
  - unfold ComputationalADT.cMethods in *; simpl in *; rewrite <- H0''; eapply H0'.
Qed.

Definition Initialize_IndexedQueryStructureImpls'
           {schemas}
           Index
           (DelegateReps : @BoundedString (map relName schemas) -> Type)
           (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
: @Build_IndexedQueryStructure_Impl_cRep _ Index DelegateReps :=
  Iterate_Dep_Type_equiv'
    string_dec
    (fun idx : @BoundedString (map relName schemas) =>
       DelegateReps idx)
    (fun idx : @BoundedString (map relName schemas) =>
       CallBagImplConstructor DelegateReps DelegateImpls BagEmpty ()).

Lemma Initialize_IndexedQueryStructureImpls_AbsR
      {qs_schema : QueryStructureSchema}
: forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
         (DelegateReps : @BoundedString (map relName (qschemaSchemas qs_schema)) -> Type)
         (DelegateImpls : forall idx,
                            ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
         (ValidImpls
          : forall idx,
              refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                        (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
    refine (r_o <- @Initialize_IndexedQueryStructure _ Index;
           {r_n | Build_IndexedQueryStructure_Impl_AbsR DelegateReps DelegateImpls ValidImpls r_o r_n})
           (ret (Initialize_IndexedQueryStructureImpls' DelegateReps DelegateImpls)).
Proof.
  destruct qs_schema.
  unfold Build_IndexedQueryStructure_Impl_AbsR, GetIndexedRelation.
  simpl; clear qschemaConstraints.
  induction qschemaSchemas; intros;
  pose proof (ilist_invert Index) as H'; simpl in H'; subst.
  - simpl; simplify with monad laws.
    computes_to_econstructor;  computes_to_inv; subst.
    eapply (fun P H => Iterate_Dep_Type_BoundedIndex_equiv_1 P H); simpl.
    econstructor.
  - destruct H' as [idx' [Index' Index_eq]]; subst.
    simpl; simplify with monad laws.
    pose proof (IHqschemaSchemas
                  Index'
                  (fun idx : @BoundedString (map relName qschemaSchemas) =>
                     (DelegateReps {|bindex := bindex idx;
                                     indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}))
                  (fun idx : @BoundedString (map relName qschemaSchemas) =>
                     (DelegateImpls {|bindex := bindex idx;
                                     indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}))
                  (fun idx : @BoundedString (map relName qschemaSchemas)=>
                     (ValidImpls {|bindex := bindex idx;
                                   indexb := @IndexBound_tail _ _ _ _ (indexb idx) |}))
               _ (ReturnComputes _)).
    unfold refine; intros;  computes_to_inv; subst.
    computes_to_econstructor; eauto.
    computes_to_econstructor.
    intros.
    pose proof (fun d => @refine_BagImplConstructor
                        _ _  DelegateReps DelegateImpls ValidImpls idx BagEmpty d).
    intros; destruct idx as [idx [n nth_n]].
    destruct n; simpl in *.
    + unfold i2th_Bounded, ith_Bounded_rect; simpl.
      destruct (H0 ()) as [r_o' [refines_r_o' AbsR_r_o']].
      pose proof (refines_r_o' _ (ReturnComputes _)).
      unfold CallBagConstructor in H1; simpl in H1;  computes_to_inv; subst.
      revert AbsR_r_o'; clear.
      unfold Dep_Type_BoundedIndex_nth_eq, eq_rect_r, eq_rect, eq_sym.
      pose eq_proofs_unicity.
      injection nth_n; intros; subst.
      match goal with
          |- context [indexb_ibound_eq ?a ?a' ?eq'] =>
          pose a; pose a'; pose eq'
      end.
      pose proof (fun H => eq_proofs_unicity H (indexb_ibound_eq b b0 e0) eq_refl).
      revert H; unfold b, b0, e0; intros.
      rewrite H.
      revert AbsR_r_o'; clear.
      match goal with
          |- context [eq_proofs_unicity_Opt_A ?string_dec ?nth_n ?nth_n'] =>
          destruct (eq_proofs_unicity_Opt_A string_dec nth_n nth_n');
            rewrite (@eq_proof_unicity_eq _ string_dec ((relName a) :: map relName qschemaSchemas) (relName a) 0 nth_n nth_n eq_refl); eauto
      end.
      intros; destruct (string_dec x y); intuition.
    + apply (H' {| bindex := idx;
                  indexb := {| ibound := n;
                               boundi := nth_n |} |}).
Qed.

Definition Update_Build_IndexedQueryStructure_Impl_cRep
           qs_schema Index DelegateReps
           (r_n : Build_IndexedQueryStructure_Impl_cRep (indices := qs_schema) Index DelegateReps)
           TableID (r_n' : DelegateReps TableID)
: Build_IndexedQueryStructure_Impl_cRep Index DelegateReps :=
  match TableID return DelegateReps TableID -> _ with
      {|bindex := idx;
        indexb := {| ibound := n;
                     boundi := nth_n |} |} =>
      Update_Iterate_Dep_Type string_dec DelegateReps r_n n nth_n
  end r_n'.

Lemma Update_Build_IndexedQueryStructure_Impl_AbsR
: forall qs_schema Index DelegateReps DelegateImpls
         ValidImpls r_o r_n TableID r_o' r_n',
    @Build_IndexedQueryStructure_Impl_AbsR qs_schema Index DelegateReps DelegateImpls
                                           ValidImpls r_o r_n
    -> AbsR (ValidImpls TableID) r_o' r_n'
    -> @Build_IndexedQueryStructure_Impl_AbsR
         qs_schema Index DelegateReps DelegateImpls
         ValidImpls (UpdateIndexedRelation r_o TableID r_o')
         (Update_Build_IndexedQueryStructure_Impl_cRep _ _ r_n TableID r_n').
Proof.
  unfold Build_IndexedQueryStructure_Impl_AbsR,
  Update_Build_IndexedQueryStructure_Impl_cRep; intros.
  destruct (BoundedString_eq_dec TableID idx); subst.
  - destruct idx as [idx [n nth_n]]; simpl.
    erewrite Lookup_Update_Iterate_Dep_Type_eq.
    unfold UpdateIndexedRelation, GetIndexedRelation;
      rewrite i2th_replace_BoundIndex_eq; eassumption.
  - destruct TableID as [TableID' [t' nth_t']]; simpl.
    unfold UpdateIndexedRelation, GetIndexedRelation;
      rewrite i2th_replace_BoundIndex_neq; eauto using string_dec.
    destruct idx as [idx [n' nth_n']]; simpl.
    erewrite Lookup_Update_Iterate_Dep_Type_neq.
    apply H.
    clear r_o' r_n' H0.
    unfold not; intros; subst; eapply n.
    apply idx_ibound_eq; simpl; eauto using string_dec.
Qed.


Arguments BuildIndexSearchTerm : simpl never.
Arguments MatchIndexSearchTerm : simpl never.
Opaque Initialize_IndexedQueryStructure.

Ltac fields storage :=
  match eval cbv delta [storage] in storage with
    | let src := ?X in _ => X
  end.

Ltac prove_extensional_eq :=
  clear;
  unfold ExtensionalEq;
  destruct_ifs; first [ solve [intuition] | solve [exfalso; intuition] | idtac ].

(* That's it for indexes! *)

Record KindName
  := { KindNameKind : string;
       KindNameName : string }.

(* Recurse over [fds] to find an attribute matching s *)
Ltac findMatchingTerm fds kind s k :=
  match fds with
    | ({| KindNameKind := ?IndexType;
          KindNameName := ?fd |}, ?X) =>
      (* Check if this field name is equal to s; process [X] with [k] if so. *)
      let H := fresh in
      assert (H : s = fd) by reflexivity; clear H;
      assert (H : kind = IndexType) by reflexivity; clear H;
      k X
    | (?fds1, ?fds2) => findMatchingTerm fds1 kind s k || findMatchingTerm fds2 kind s k
  end.

Ltac createLastInclusionTerm f fds tail fs kind s k :=
  match kind with
    | "InclusionIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k {| IndexSearchTerm := X;
                             ItemSearchTerm := tail |}))
        || k {| IndexSearchTerm := nil;
                ItemSearchTerm := tail |}
  end.

Ltac createLastPrefixTerm f fds tail fs kind s k :=
  match kind with
    | "FindPrefixIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k {| FindPrefixIndexSearchTerm := Some X;
                             FindPrefixItemSearchTerm := tail |}))
        || k {| FindPrefixIndexSearchTerm := None;
                FindPrefixItemSearchTerm := tail |}
end.

Ltac createLastRangeTerm f fds tail fs kind s k :=
  match kind with
    | "RangeIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k {| RangeIndexSearchTerm := Some X;
                             RangeItemSearchTerm := tail |}))
        || k {| RangeIndexSearchTerm := None;
                RangeItemSearchTerm := tail |}
end.

Ltac createEarlyInclusionTerm f fds tail fs kind EarlyIndex LastIndex rest s k :=
  match kind with
    | "InclusionIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (X, rest)))
        || k (@nil string, rest)
  end.

Ltac createEarlyPrefixTerm f fds tail fs kind EarlyIndex LastIndex rest s k :=
  match kind with
    | "FindPrefixIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (Some X, rest)))
        || k (@None (list ascii), rest)
  end.

Ltac createEarlyRangeTerm f fds tail fs kind EarlyIndex LastIndex rest s k :=
  match kind with
    | "RangeIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (Some X, rest)))
        || k (@None (nat * nat), rest)
  end.

(* Recurse over the list of search term indexes [fs],
 consulting the list of attribute name and value pairs in [fds] to
 find matching search terms via [findMatchingTerm].
 *)

Ltac createTerm f fds tail fs EarlyIndex LastIndex k :=
  match fs with
    | [{| KindNameKind := ?kind;
          KindNameName := ?s|} ] =>
      (* *)
      match kind with
        | "EqualityIndex" =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (Some X, tail)))
            || k (@None (Domain f {| bindex := s |} ), tail)
        | _ => LastIndex f fds tail fs kind s k
      end
    | {| KindNameKind := ?kind;
         KindNameName := ?s|} :: ?fs' =>
      createTerm
        f fds tail fs' EarlyIndex LastIndex
        ltac:(fun rest =>
                match kind with
                  | "EqualityIndex" =>
                    (findMatchingTerm
                       fds kind s
                       ltac:(fun X => k (Some X, rest)))
                      || k (@None (Domain f {| bindex := s |} ), rest)
                  | _ => EarlyIndex f fds tail fs EarlyIndex LastIndex kind rest s k
                end)
  end.

      (* Using a list of search term attributes [fs],
   a list of attribute name and value pairs [fds],
   use [createTerm] to recurse over [fs]
   using the schema for [SC]
       *)
Ltac makeTerm fs SC fds tail EarlyIndex LastIndex k :=
  match eval hnf in SC with
    | Build_Heading ?f =>
      createTerm (Build_Heading f) fds tail fs EarlyIndex LastIndex k
  end.

(* Given a storage schema [SC], a filter [F],
   a list of indexed attributes [search_attrs] and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]). *)

Ltac InclusionIndexUse SC F indexed_attrs f k :=
     match type of f with
       (* Inclusion Search Terms *)
       | forall a, {IncludedIn ?X (_!?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "InclusionIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {IncludedIn ?X (_``?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "InclusionIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
     end.

Ltac PrefixIndexUse SC F indexed_attrs f k :=
     match type of f with
(* FindPrefix Search Terms *)
| forall a, {IsPrefix (_!?fd) ?X} + {_} =>
  let H := fresh in
  assert (List.In {| KindNameKind := "FindPrefixIndex";
                     KindNameName := fd|} indexed_attrs) as H
      by (clear; simpl; intuition eauto); clear H;
  k ({| KindNameKind := "FindPrefixIndex";
        KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
| forall a, {IsPrefix (_``?fd) ?X} + {_} =>
  let H := fresh in
  assert (List.In {| KindNameKind := "FindPrefixIndex";
                     KindNameName := fd|} indexed_attrs) as H
      by (clear; simpl; intuition eauto); clear H;
  k ({| KindNameKind := FindPrefixIndex;
        KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
     end.

Ltac RangeIndexUse SC F indexed_attrs f k :=
match type of f with
        (* Range Search Terms *)
        | forall a, {InRange (_!?fd) ?X} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "RangeIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {InRange (_!``?fd) ?X} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "RangeIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
end.

Ltac findGoodTerm SC F indexed_attrs ClauseMatch k :=
  match F with
    | fun a => ?[@?f a] =>
      match type of f with
        (* Equality Search Terms *)
        | forall a, {?X = _!?fd} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          k ({| KindNameKind := "EqualityIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {_!?fd = ?X} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "EqualityIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {?X = _``?fd} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "EqualityIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
        | forall a, {_``?fd = ?X} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            k ({| KindNameKind := "EqualityIndex";
                  KindNameName := fd|}, X) (fun _ : @Tuple SC => true)

        | _ => ClauseMatch  SC F indexed_attrs f k

      end
    | fun a => (@?f a) && (@?g a) =>
      findGoodTerm SC f indexed_attrs
                   ltac:(fun fds1 tail1 =>
                           findGoodTerm SC g indexed_attrs
                                        ltac:(fun fds2 tail2 =>
                                                k (fds1, fds2) (fun tup : @Tuple SC => (tail1 tup) && (tail2 tup))))
    | _ => k tt F
  end.

Ltac find_simple_search_term
     ClauseMatch EarlyIndex LastIndex
     qs_schema idx filter_dec search_term :=
  match type of search_term with
    | BuildIndexSearchTerm ?indexed_attrs =>
      let indexed_attrs' :=
          eval simpl in (map (fun kidx =>
                                {| KindNameKind := KindIndexKind kidx;
                                   KindNameName := @bindex string _ (KindIndexIndex kidx) |}) indexed_attrs) in
          let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
          findGoodTerm SC filter_dec indexed_attrs' ClauseMatch
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm indexed_attrs' SC fds tail EarlyIndex LastIndex ltac:(fun tm => try unify tm search_term;
                                                                                                                              unfold ExtensionalEq, MatchIndexSearchTerm;
                                                                                                                              simpl; intro; try prove_extensional_eq
                                                                                                                             )) end.

Ltac implement_QSDeletedTuples find_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[Pick (QSDeletedTuples ?r_o ?idx ?DeletedTuples)] ] =>
      let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                      makeEvar search_term_type
                               ltac: (fun search_term =>
                                        let eqv := fresh in
                                        assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                      [ find_search_term qs_schema idx filter_dec search_term
                                      | let H' := fresh in
                                        pose (@refine_BagADT_QSDelete_fst _ _ r_o r_n H idx DeletedTuples _ search_term) as H';
                                          setoid_rewrite (H' eqv); clear H' eqv])
  end.

Ltac implement_EnsembleDelete_AbsR find_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[{r_n' | DelegateToBag_AbsR
                             (UpdateUnConstrRelation ?r_o ?idx
                                                     (EnsembleDelete (GetUnConstrRelation ?r_o ?idx)
                                                                     ?DeletedTuples)) r_n'}]] =>
      let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                      makeEvar search_term_type
                               ltac:(fun search_term =>
                                       let eqv := fresh in
                                       assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                     [ find_search_term qs_schema idx filter_dec search_term
                                     | let H' := fresh in
                                       pose (@refine_BagADT_QSDelete_snd _ _ r_o r_n H idx DeletedTuples _ search_term) as H';
                                         setoid_rewrite (H' eqv); clear H' eqv] )
  end.

Ltac implement_Enumerate_filter find_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[For (l <- CallBagMethod ?idx BagEmpty ?r_n0 ();
                        (List_Query_In (filter (@DecideableEnsembles.dec _ ?DeletedTuples _) (snd l))
                                       ?resultComp))]] =>
      let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                      makeEvar search_term_type
                               ltac:(fun search_term =>
                                       let eqv := fresh in
                                       assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                     [ find_search_term qs_schema idx filter_dec search_term
                                     | let H' := fresh in
                                       pose (@refine_Query_For_In_Find _ _ string _ _ H idx filter_dec
                                                                       search_term resultComp) as H';
                                         setoid_rewrite (H' eqv); clear H'])
  end.

Ltac implement_Pick_DelegateToBag_AbsR_observer :=
  match goal with
      [H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
       |- context[{r_n' : IndexedQueryStructure ?qs_schema ?indices | DelegateToBag_AbsR ?r_o r_n'}] ]
      => setoid_rewrite (refine_pick_val (@DelegateToBag_AbsR qs_schema indices r_o) H)
  end.

(* implement_In' implements [UnConstrQuery_In] in a variety of contexts. *)
Ltac implement_In' :=
  match goal with
    (* Implement a List_Query_In of a list [l] applied to a UnConstrQuery_In [idx]
        by enumerating [idx] with a method call and joining the result with [l] *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (List_Query_In ?l (fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b) )) _ ] =>
      etransitivity;
        [ let H' := eval simpl in (refine_Join_Query_In_Enumerate' H idx f l) in
              apply H'
        |  apply refine_under_bind; intros; implement_In' ]

    (* Implement a 'naked' UnConstrQuery_In as a call to enumerate *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
      etransitivity;
        [ let H' := eval simpl in (refine_Query_In_Enumerate H (idx := idx) f) in
              apply H'
        | apply refine_under_bind; intros; implement_In' ]
    | |- _ =>  higher_order_reflexivity
  (* Implement a UnConstrQuery_In under a single binder as a call to enumerate
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b) ] ] =>
      let H' := eval simpl in
      (fun b => @refine_Query_In_Enumerate qs_schema indexes _ r_o r_n H idx (f b)) in
          setoid_rewrite H' *)
  end.
Ltac implement_In :=
  etransitivity;
  [ implement_In' | ]; cbv beta; simpl.

Lemma ExtensionalEq_andb {A} :
  forall (f g f' g' : A -> bool),
    ExtensionalEq f f'
    -> ExtensionalEq g g'
    -> ExtensionalEq (fun a => f a && g a) (fun a => f' a && g' a).
Proof.
  unfold ExtensionalEq; intros; congruence.
Qed.

Lemma ExtensionalEq_andb_true {A} :
  forall (f f' : A -> bool),
    ExtensionalEq f f'
    -> ExtensionalEq f (fun a => f' a && (fun _ => true) a).
Proof.
  unfold ExtensionalEq; intros.
  rewrite andb_true_r; apply H.
Qed.

Ltac split_filters k :=
  match goal with
    | |- ExtensionalEq (fun a => (@?f a) && (@?g a)) ?b =>
      let fT := type of f in
      let gT := type of g in
      makeEvar
        fT
        ltac:(fun f' =>
                makeEvar gT ltac:(fun g' =>
                                    apply (@ExtensionalEq_andb _ f g f' g');
                                  [ first [split_filters | k ] | first [split_filters | k]] ))
    | |- ExtensionalEq (fun a => (@?f a)) ?b => k
  end.

(* Convert List_Query_In Where Clauses into a filter using search terms. *)

Ltac convert_Where_to_search_term :=
  (* First replace the Where clause with a test function. *)
  simpl;
  match goal with
      |- context[List_Query_In _ (fun b : ?QueryT => Where (@?P b) (@?resultComp b))]
      =>
      let P_dec := fresh in
      setoid_rewrite (fun l => @refine_List_Query_In_Where QueryT _ l P resultComp _)
  end; simpl;
  (* Find search term replacements for the function. *)
  match goal with
      |- context [List_Query_In (filter ?f _) _] =>
      let T := type of f in
      makeEvar T
               ltac:(fun g =>
                       let eqv := fresh in
                       assert (ExtensionalEq f g) as eqv;
                     [ apply ExtensionalEq_andb_true
                     | setoid_rewrite (filter_by_equiv f g eqv)])
  end.

Ltac convert_filter_to_search_term :=
  (* Find search term replacements for filter functions. *)
  match goal with
      |- refine (l <- Join_Filtered_Comp_Lists ?l1 ?l2 ?f; _) _
      =>  let T := type of f in
          makeEvar T
                   ltac:(fun g =>
                           let eqv := fresh in
                           assert (ExtensionalEq f g) as eqv;
                         [ try apply ExtensionalEq_andb_true
                         | rewrite (@Join_Filtered_Comp_Lists_ExtensionalEq_filters _ _ _ _ l1 l2 f g eqv); clear eqv ])
  end.

Ltac convert_Where_to_filter :=
  (* First replace the Where clause with a filter function. *)
  simpl;
  match goal with
      |- context[List_Query_In _ (fun b : ?QueryT => Where (@?P b) (@?resultComp b))]
      =>
      let P_dec := fresh in
      setoid_rewrite (fun l => @refine_List_Query_In_Where QueryT _ l P resultComp _)
  end; simpl.

Ltac equate X Y := let H := fresh in assert (H : X = Y) by reflexivity; clear H.

Definition unit_Heading := BuildHeading [].

Definition unit_Tuple : @Tuple unit_Heading := BuildTuple (inil _).

Ltac get_ithDefault f n k :=
  match type of f with
    | ilist (@Tuple) ?A -> ?C =>
      let G := fresh "G" in
      let p := fresh "p" in
      let H := fresh "H" in
      let proj := fresh "proj" in
      let proj := eval simpl in
      (fun b : ilist (@Tuple) A => ith_default unit_Heading unit_Tuple b n) in
          evar (G : @Tuple (nth_default unit_Heading A n) -> C);
        assert (H : forall p,
                      f p = G (proj p)) by
          (subst G; intro p;
           let p' := eval simpl in (proj p) in
               pattern p';
           match goal with
             | [ |- (fun t => @?f t = @?g t) _ ] => equate g f; reflexivity
           end); clear H;
        let G' := eval unfold G in G in clear G; k G'
  end.

Ltac get_ithDefault_pair f m n k :=
  match type of f with
    | ilist (@Tuple) ?A -> ?C =>
      let G := fresh "G" in
      let p := fresh "p" in
      let H := fresh "H" in
      let proj1 := fresh "proj" in
      let proj2 := fresh "proj" in
      let proj1 := eval simpl in
      (fun b : ilist (@Tuple) A => ith_default unit_Heading unit_Tuple b m) in
          let proj2 := eval simpl in
          (fun b : ilist (@Tuple) A => ith_default unit_Heading unit_Tuple b n)
            in evar (G : @Tuple (nth_default unit_Heading A m)
                         -> @Tuple (nth_default unit_Heading A n)
                         -> C);
            assert (H : forall p,
                          f p = G (proj1 p) (proj2 p)) by
              ( subst G; intro p;
                let p1 := eval simpl in (proj1 p) in
                    let p2 := eval simpl in (proj2 p) in
                        pattern p1, p2;
                match goal with
                  | [ |- (fun t t' => @?f t t' = @?g t t') _ _ ] => equate f g; reflexivity
                end); clear H;
            let G' := eval unfold G in G in clear G; k G'
  end.

(* Build search a search term from the list of attribute + value pairs in fs. *)

Ltac createLastInclusionTerm_dep dom f fds tail fs kind rest s k :=
  match kind with
    | "InclusionIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (fun x : dom => {| IndexSearchTerm := X x;
                                             ItemSearchTerm := tail x |}))
                || k (fun x : dom => {| IndexSearchTerm := nil;
                                        ItemSearchTerm := tail x |}))
  end.

Ltac createLastPrefixTerm_dep dom f fds tail fs kind rest s k :=
  match kind with
    | "FindPrefixIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (fun x : dom => {| FindPrefixIndexSearchTerm := Some (X x);
                                             FindPrefixItemSearchTerm := tail x |}))
                || k (fun x : dom => {| FindPrefixIndexSearchTerm := None;
                                        FindPrefixItemSearchTerm := tail x |}))
  end.

Ltac createLastRangeTerm_dep dom f fds tail fs kind rest s k :=
  match kind with
    | "RangeIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (fun x : dom => {| RangeIndexSearchTerm := Some (X x);
                                             RangeItemSearchTerm := tail x |}))
                || k (fun x : dom => {| RangeIndexSearchTerm := None;
                                        RangeItemSearchTerm := tail x |}))
  end.

Ltac createTerm_dep dom f fds tail fs EarlyIndex LastIndex k :=
  match fs with
    | [{| KindNameKind := ?kind;
          KindNameName := ?s|} ] =>
      match kind with
        | "EqualityIndex" =>
          (try findMatchingTerm fds kind s
                           ltac:(fun X =>
                                   k (fun x : dom => (Some (X x), tail x))))
            || k (fun x : dom => (@None (Domain f {| bindex := s |} ), tail x))
        | _ => LastIndex dom f fds tail fs kind tail s k
      end
    | {| KindNameKind := ?kind;
          KindNameName := ?s|} :: ?fs' =>
      createTerm_dep dom f fds tail fs'
                     EarlyIndex LastIndex
                     ltac:(fun rest =>
                             findMatchingTerm fds kind s
                                              ltac:(fun X =>
                                                      match kind with
                                                        | "EqualityIndex" =>
                                                          k (fun x : dom => (Some (X x), rest x))
                                                      end)
                                                     ||
                                                     match kind with
                                                       | "EqualityIndex" =>
                                                         k (fun x : dom => (@None (Domain f {| bindex := s |} ), rest x))
                                                     end)
  end.

(* Get the heading of [SC] before building the search term. *)
Ltac makeTerm_dep dom fs SC fds tail EarlyIndex LastIndex k :=
  match eval hnf in SC with
    | Build_Heading ?f =>
      createTerm_dep dom (Build_Heading f) fds tail fs EarlyIndex LastIndex k
  end.

(* Given a storage schema [SC], a filter [F],
   a list of indexed attributes [search_attrs] and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]). *)

Ltac InclusionIndexUse_dep SC F indexed_attrs visited_attrs f T k :=
  match type of f with
    | forall a b, {IncludedIn (@?X a) (_!?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "InclusionIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {IncludedIn (@?X a) (_``?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "InclusionIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
  end.

      (* FindPrefix Search Terms *)
Ltac PrefixIndexUse_dep SC F indexed_attrs visited_attrs f T k :=
    match type of f with
        | forall a b, {IsPrefix (_!?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "FindPrefixIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "FindPrefixIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {IsPrefix (_``?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "FindPrefixIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "FindPrefixIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
end.

Ltac RangeIndexUse_dep SC F indexed_attrs visited_attrs f T k :=
    match type of f with
        (* Range Search Terms *)
        | forall a b, {InRange (_!?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "RangeIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {InRange (_``?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "RangeIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "RangeIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
    end.


      Ltac findGoodTerm_dep SC F indexed_attrs visited_attrs makeClause k :=
  match F with
    | fun (a : ?T) b => ?[@?f a b] =>
      match type of f with
        | forall a b, {@?X a = _!?fd} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "EqualityIndex";
                                 KindNameName := fd|}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
        | forall a b, {_!?fd = @?X a} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "EqualityIndex";
                               KindNameName := fd|}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
        | forall a b, {@?X a = _``?fd} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "EqualityIndex";
                                 KindNameName := fd|}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
        | forall a b, {_``?fd = @?X a} + {_} =>
          assert (List.In {| KindNameKind := "EqualityIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "EqualityIndex";
                               KindNameName := fd|}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end

        | _ => makeClause SC F indexed_attrs visited_attrs f T k


        | forall a b, {IncludedIn (@?X a) (_!?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "InclusionIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {IncludedIn (@?X a) (_``?fd)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "InclusionIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "InclusionIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
      end
    | fun (a : ?T) b => (@?f a b) && (@?g a b) =>
      findGoodTerm_dep
        SC f indexed_attrs visited_attrs makeClause
        ltac:(fun v fds1 tail1 =>
                findGoodTerm_dep
                  SC g indexed_attrs v makeClause
                  ltac:(fun v' fds2 tail2 =>
                          k v' (fds1, fds2) (fun (a : T) (tup : @Tuple SC) =>
                                               (tail1 a tup) && (tail2 a tup))))
    | _ => k visited_attrs tt F
  end.

Definition Dep_SearchTerm_Wrapper {A} {heading}
           (search_term_dep : @Tuple heading -> A)
           (tup : @Tuple heading) : A := search_term_dep tup.

      Ltac find_simple_search_term_dep
           makeClause EarlyIndex LastIndex
           qs_schema idx dom filter_dec search_term :=
  match type of search_term with
    | ?dom -> BuildIndexSearchTerm ?indexed_attrs  =>
      let indexed_attrs' :=
          eval simpl in (map (fun kidx =>
                                {| KindNameKind := KindIndexKind kidx;
                                   KindNameName := @bindex string _ (KindIndexIndex kidx) |}) indexed_attrs) in
          let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
          let filter_dec' := eval simpl in filter_dec in
              findGoodTerm_dep SC filter_dec' indexed_attrs' (@nil string)
                               makeClause
                               ltac:(fun v fds tail =>
                                       let tail := eval simpl in tail in
                                           makeTerm_dep dom indexed_attrs' SC fds tail
                                                        EarlyIndex LastIndex
                                                        ltac:(fun tm => pose tm;
                                                              (* unification fails if I don't pose tm first... *)
                                                              try unify tm search_term;
                                                              unfold ExtensionalEq, MatchIndexSearchTerm;
                                                              simpl; intros;
                                                              try prove_extensional_eq

                                                             )) end.

(* Find the name of a schema [schemas] with the same heading as [heading] *)
Ltac find_equivalent_tuple schemas heading k :=
  match schemas with
    | nil => fail
    | ?sch' :: ?schemas' =>
      (let H := fresh in
       assert (schemaHeading (relSchema sch') = heading) as H
           by reflexivity;
       clear H;  k (relName sch'))
        || find_equivalent_tuple schemas' heading k
  end.

(* Build pairs of fields + their values. *)
Ltac find_equivalent_search_term_pair build_search_term_dep :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- ExtensionalEq ?f _ ] =>
      match type of f with
        | ilist (@Tuple) (?heading :: ?headings) -> bool =>
          makeEvar (ilist (@Tuple) headings -> @Tuple heading -> bool)
                   ltac:(fun filter_dec =>
                           let eqv_f_dec := fresh in
                           assert (forall a : ilist (@Tuple) (heading :: headings),
                                     f a = filter_dec (ilist_tl a) (ilist_hd a));
                         [let a := fresh in
                          intro a; let f' := match goal with |- ?f = _ => f end in
                                   let f'' :=
                                       match eval pattern (ilist_tl a), (ilist_hd a) in f'
                                       with | ?f'' _ _ => f'' end
                                         in let f3 := eval simpl in f'' in
                                                unify f3 filter_dec; reflexivity
                                       | let dom := constr:(ilist (@Tuple) headings) in
                                         let schemas := eval simpl in (qschemaSchemas qs_schema) in
                                             find_equivalent_tuple schemas heading
                                                                   ltac:(fun id => let idx' := constr:({| bindex := id |} : BoundedIndex (map relName (qschemaSchemas qs_schema)))
                                                                                   in let idx := eval simpl in idx' in
                                                                                          let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
                                                                                              let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                                                  let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                                                      makeEvar (dom -> search_term_type)
                                                                                                               ltac: (fun search_term =>
                                                                                                                        let eqv := fresh in
                                                                                                                        assert (forall (a : ilist (@Tuple) (headings)) (b : @Tuple heading) ,
                                                                                                                                  filter_dec a b = search_term_matcher (search_term a) b) as eqv;
                                                                                                                      [ build_search_term_dep qs_schema idx dom filter_dec search_term
                                                                                                                      | match goal with
                                                                                                                            |- ExtensionalEq ?f ?search_term' =>
                                                                                                                            match type of f with
                                                                                                                              | ilist (@Tuple) (?A :: ?As) -> _ =>
                                                                                                                                unify search_term' (fun a : ilist (@Tuple) (A :: As) => search_term_matcher (search_term (ilist_tl a)) (ilist_hd a))
                                                                                                                            end
                                                                                                                        end;
                                                                                                                        unfold ExtensionalEq in *;
                                                                                                                        let a := fresh in intro a; eapply eqv


                                                                                                                      ]
                                                                                                                     )) ]) end
  end.

Ltac find_equivalent_search_term build_search_term :=
  match goal with
      [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- ExtensionalEq ?f _ ] =>
      get_ithDefault f 0
                     ltac:(fun filter_dec =>
                             let heading := match type of filter_dec with
                                              | @Tuple ?heading -> bool => constr:(heading)
                                            end in
                             let schemas := eval simpl in (qschemaSchemas qs_schema) in
                                 find_equivalent_tuple schemas heading
                                                       ltac:(fun id => let idx' := constr:({| bindex := id |} : BoundedIndex (map relName (qschemaSchemas qs_schema)))
                                                                       in let idx := eval simpl in idx' in
                                                                              let idx_search_update_term := eval simpl in (ith_Bounded relName indices idx) in
                                                                                  let search_term_type := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                                      let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                                          makeEvar (search_term_type)
                                                                                                   ltac: (fun search_term =>
                                                                                                            let eqv := fresh in
                                                                                                            assert (forall a, filter_dec a
                                                                                                                              = search_term_matcher search_term a) as eqv;
                                                                                                          [ build_search_term qs_schema idx
                                                                                                                              filter_dec search_term
                                                                                                          | match goal with
                                                                                                                |- ExtensionalEq ?f ?search_term' =>
                                                                                                                match type of f with
                                                                                                                  | ?A -> _ =>
                                                                                                                    unify search_term' (fun a : A => search_term_matcher search_term (ith_default unit_Heading unit_Tuple a 0))
                                                                                                                end
                                                                                                            end;
                                                                                                            unfold ExtensionalEq in *; intros;
                                                                                                            simpl in *; rewrite <- eqv; simpl; reflexivity
                                                                                                          ]))) end.


Ltac convert_filter_to_find' :=
  try match goal with
          |- context[filter (fun a => (_ && _) && true) _] =>
          setoid_rewrite <- andb_assoc; simpl
      end;
  match goal with
    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n

      |- context[l <- CallBagMethod ?idx BagEnumerate ?r_n ();
                  List_Query_In (filter (fun a => @?f a && @?filter_rest a)
                                        (Build_single_Tuple_list (snd l))) ?resultComp] =>
      match f with
        | fun a => ?MatchIndexSearchTerm ?st (ilist_hd a) =>
          let b := fresh in
          pose proof (@refine_Query_For_In_Find_single _ _ _ r_o r_n H idx st resultComp filter_rest) as b;
            simpl in b; setoid_rewrite b; clear b
      end

    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[l <- CallBagMethod ?idx BagEnumerate ?r_n ();
                  l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) ?cl;
                  List_Query_In (filter (fun a => @?f a && @?filter_rest a)
                                        l') ?resultComp] =>
      match f with
        | fun a => ?MatchIndexSearchTerm ?st (ilist_hd (ilist_tl a)) =>
          let b := fresh in
          pose proof (fun foo => @refine_Join_Comp_Lists_filter_search_term_fst _ _ _ r_n idx _ cl st resultComp foo filter_rest) as b;
            simpl in b; setoid_rewrite b;
            [ clear b
            | match goal with
                | |- context [CallBagMethod ?idx' BagEnumerate _ _] =>
                  intros; eapply (realizeable_Enumerate (r_o := r_o) (r_n := r_n) idx' H)
                | |- context [CallBagMethod ?idx' BagFind _ _] =>
                  intros; eapply (realizeable_Find (r_o := r_o) (r_n := r_n) idx' H)
              end]
      end

    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[l <- CallBagMethod ?idx BagFind ?r_n ?st;
                  l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l))
                     (fun _ : ilist (@Tuple) [?heading] =>
                        l <- CallBagMethod ?idx' BagEnumerate ?r_n ();
                      ret (snd l));
                  List_Query_In (filter (fun a => @?f a && @?filter_rest a) l') ?resultComp] =>
      match f with
        | fun a => ?MatchIndexSearchTerm (Dep_SearchTerm_Wrapper ?st' (ilist_hd (ilist_tl a)))
                    (ilist_hd a) =>
          let b := fresh in
          pose proof (@refine_Join_Comp_Lists_filter_filter_search_term_snd_dep' _ _ _ r_n idx idx'
                                                                                 (fun a => Dep_SearchTerm_Wrapper st' (ilist_hd a))
                                                                                 resultComp filter_rest st) as b;
            unfold Dep_SearchTerm_Wrapper in b; simpl in b; setoid_rewrite b; clear b
      end

    (* The final case replaces the last filter and the Return statement. *)
    | _ => setoid_rewrite filter_true; setoid_rewrite refine_List_Query_In_Return
  end.

Ltac convert_filter_to_find :=
  simpl; repeat convert_filter_to_find'.

(* This also implements Fors *)
Ltac Implement_Aggregates :=
  repeat
    match goal with
      | |- context[For _] => setoid_rewrite refine_For_List
      | |- context[Count _] => setoid_rewrite refine_Count
      | |- context[MaxN _] => setoid_rewrite refine_MaxN
      | |- context[SumN _] => setoid_rewrite refine_SumN
      | |- context[MaxZ _] => setoid_rewrite refine_MaxZ
      | |- context[SumZ _] => setoid_rewrite refine_SumZ
      | |- context[Max _] => setoid_rewrite refine_Max
      | |- context[Sum _] => setoid_rewrite refine_Sum
    end.

(* Commits the database at the end of a method call. *)
Ltac commit :=
  match goal with
    | [H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
       |- context[{r_n' : IndexedQueryStructure ?qs_schema ?indices | DelegateToBag_AbsR ?r_o r_n'}] ]
      => setoid_rewrite (refine_pick_val (@DelegateToBag_AbsR qs_schema indices r_o) H);
        simplify with monad laws
  end.

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

Definition Join_Comp_Lists'
           {A : Type} {f : A -> Type} {As : list A} {a : A}
           (l : list (ilist f As)) (c : ilist f As -> list (f a))
  := flatten (map
                (fun l' => map (fun fa : f a => icons _ fa l') (c l')) l).

Lemma Join_Comp_Lists_Impl {A : Type} {f : A -> Type} {As : list A} {a : A}
: forall (l : list (ilist f As))
         (c : ilist f As -> Comp (list (f a)))
         (c' : ilist f As -> list (f a)),
    (forall a', refine (c a') (ret (c' a')))
    -> refine (Join_Comp_Lists l c) (ret (Join_Comp_Lists' l c')).
Proof.
  induction l; unfold Join_Comp_Lists, Join_Comp_Lists'; simpl; intros.
  - reflexivity.
  - rewrite H; simplify with monad laws.
    setoid_rewrite IHl; eauto; simplify with monad laws.
    reflexivity.
Qed.

Arguments icons {A} {B} {a} {As} _ _.
Arguments CallBagConstructor {heading} name {index} cidx _ _.

Ltac implement_bag_constructors :=
  repeat match goal with
           | |- context[ Pick (fun r_n : @Build_IndexedQueryStructure_Impl_cRep ?qs_schema ?Index ?DelegateReps =>
                                 @Build_IndexedQueryStructure_Impl_AbsR
                                   _ _ ?DelegateReps ?DelegateImpls
                                   ?ValidImpls ?r_o r_n)] =>
             refine pick val (@Initialize_IndexedQueryStructureImpls' qs_schema Index DelegateReps DelegateImpls);
               [ higher_order_reflexivity |
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


Ltac Implement_Insert_Checks :=
    repeat first
         [setoid_rewrite FunctionalDependency_symmetry
         | cbv beta; simpl; simplify with monad laws
         | setoid_rewrite if_duplicate_cond_eq
         | fundepToQuery
         | foreignToQuery
         | setoid_rewrite refine_trivial_if_then_else
         ].

Ltac Implement_Bound_Join_Comp_Lists :=
  match goal with
    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (Bind (Join_Comp_Lists (As := ?As) (f := ?f) (a := ?a) ?l ?c) _) _ =>
      makeEvar (ilist f As -> list (f a))
               ltac:(fun c' =>
                       let refines_c' := fresh in
                       assert (forall a', refine (c a') (ret (c' a'))) as refines_c';
                     [intros
                     | etransitivity;
                       [apply refine_bind;
                         [ apply (Join_Comp_Lists_Impl l c c' refines_c')
                         | unfold pointwise_relation; intros; higher_order_reflexivity
                         ]
                       | etransitivity;
                         [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
                       ]]; cbv beta; simpl in * )
  end.

Ltac Implement_If_Then_Else :=
  match goal with
    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (If_Then_Else ?i (ret ?t) (ret ?e)) _ =>
      apply (refine_If_Then_Else_ret i t e)

    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (Bind (If ?i Then ?t Else ?e) ?k) _ =>
      etransitivity;
        [ apply (refine_If_Then_Else_Bind i t e k)
        | etransitivity;
          [ apply refine_If_Then_Else;
            [
              | ]
          | eapply refine_If_Then_Else_ret
          ]
        ]
  end.

Ltac Implement_If_Opt_Then_Else :=
  match goal with
    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (Ifopt ?i as a Then (ret (@?t a)) Else (ret ?e)) _ =>
      apply (refine_If_Opt_Then_Else_ret i t e)

    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (Bind (Ifopt ?i as a Then (@?t a) Else ?e) ?k) _ =>
      etransitivity;
        [ apply (refine_If_Opt_Then_Else_Bind i t e k)
        | etransitivity;
          [ apply refine_If_Opt_Then_Else;
            [ unfold pointwise_relation; intros
              | ]
          | eapply refine_If_Opt_Then_Else_ret
          ]
        ]
  end.

Ltac Implement_AbsR_Relation :=
  match goal with
    (* The case when a table has been updated *)
    | [H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                  ?ValidImpls ?r_o ?r_n,
           H2 : AbsR (?ValidImpls ?TableID) ?r_o' ?r_n'
       |- refine (Bind {r_n' | @Build_IndexedQueryStructure_Impl_AbsR
                                 ?qs_schema
                                 ?Index ?DelegateReps ?DelegateImpls
                                 ?ValidImpls (UpdateIndexedRelation ?r_o ?TableID ?r_o') r_n'} _) _]
      => etransitivity;
        [ apply refine_bind;
          [apply refine_pick_val;
            apply (@Update_Build_IndexedQueryStructure_Impl_AbsR
                     qs_schema Index DelegateReps DelegateImpls
                     ValidImpls r_o r_n TableID r_o' r_n' H H2)
          | unfold pointwise_relation; intros; higher_order_reflexivity
          ]
        | etransitivity;
          [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
        ]; cbv beta; simpl in *

    | [H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                  ?ValidImpls ?r_o ?r_n
       |- refine (Bind {r_n' | @Build_IndexedQueryStructure_Impl_AbsR
                                 ?qs_schema
                                 ?Index ?DelegateReps ?DelegateImpls
                                 ?ValidImpls ?r_o r_n'} _) _]
      => etransitivity;
        [ apply refine_bind;
          [apply refine_pick_val;
            apply H
          | unfold pointwise_relation; intros; higher_order_reflexivity
          ]
        | etransitivity;
          [ apply (proj1 (refineEquiv_bind_unit _ _)) | simpl]
        ]; cbv beta; simpl in *
  end.


Ltac implement_Delete_branches ClauseMatch EarlyIndex LastIndex :=
  repeat setoid_rewrite refine_If_Then_Else_Bind;
  match goal with
      |- context[If _ Then ?t Else ?e] =>
      let B := type of t in
      makeEvar
        B
        ltac:(fun t' =>
                makeEvar B
                         ltac:(fun e' =>
                                 setoidreplace (refine e e') idtac;
                               [ setoidreplace (refine t t') idtac
                               | ] ) )
  end;
  [
  | (* Refine the then branch *)
  implement_QSDeletedTuples ltac:(find_simple_search_term ClauseMatch EarlyIndex LastIndex) ;
    simplify with monad laws;
    cbv beta; simpl;
    implement_EnsembleDelete_AbsR ltac:(find_simple_search_term ClauseMatch EarlyIndex LastIndex);
    simplify with monad laws;
    reflexivity
  | (* Refine the else branch *)
  simplify with monad laws;
    simpl; commit; reflexivity
  ].

Ltac implement_Insert_branches :=
  repeat setoid_rewrite refine_If_Then_Else_Bind;
  repeat setoid_rewrite Bind_refine_If_Then_Else;
  repeat setoid_rewrite refineEquiv_bind_unit; simpl;
  match goal with
      |- context[If _ Then ?t Else ?e] =>
      let B := type of t in
      makeEvar
        B
        ltac:(fun t' =>
                makeEvar B
                         ltac:(fun e' =>
                                 setoidreplace (refine e e') idtac;
                               [ setoidreplace (refine t t') idtac
                               | ] ) )
  end;
  [
    | (* Refine the then branch *)
    repeat match goal with
             | [ H : DelegateToBag_AbsR ?r_o ?r_n
                 |- context[idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation ?r_o ?TableID) idx};
                             {r_n' |
                              DelegateToBag_AbsR
                                (UpdateUnConstrRelation ?r_o ?TableID
                                                        (EnsembleInsert
                                                           {| elementIndex := idx; indexedElement := ?tup |}
                                                           (GetUnConstrRelation ?r_o ?TableID))) r_n'}]]
               => setoid_rewrite (@refine_BagADT_QSInsert _ _ r_o r_n H TableID tup);
                 simplify with monad laws; reflexivity
             | |- _ => setoid_rewrite <- refineEquiv_bind_bind
           end
    | (* Refine the else branch *)
    repeat match goal with
             | [ H : DelegateToBag_AbsR ?r_o ?r_n
                 |- context[{idx | UnConstrFreshIdx (GetUnConstrRelation ?r_o ?TableID) idx};;
                                                                                            {r_n' | DelegateToBag_AbsR ?r_o r_n'}]]
               => let H' := fresh in
                  pose proof H as H';
                    destruct H' as [_ H'];
                    let l := fresh in
                    let bnd := fresh in
                    let fresh_bnd := fresh in
                    destruct (H' TableID) as [l [[bnd fresh_bnd] _]];
                      refine pick val bnd; eauto;
                      setoid_rewrite refineEquiv_bind_unit;
                      refine pick val r_n; eauto;
                      setoid_rewrite refineEquiv_bind_unit;
                      reflexivity
             | |- _ => setoid_rewrite <- refineEquiv_bind_bind
           end
  ].

Ltac remove_spurious_Dep_Type_BoundedIndex_nth_eq :=
  match goal with
    | |- context[Dep_Type_BoundedIndex_nth_eq ?A_eq_dec (As := ?As) ?P ?n ?nth ?nth ?p] =>
      rewrite (@Dep_Type_BoundedIndex_nth_eq_refl _ A_eq_dec As P _ n nth p)
    (* Handle the case when the two equalities are eq_refl, but one use the Specif.value
       and the other uses option. *)
    | |- context[Dep_Type_BoundedIndex_nth_eq ?A_eq_dec (As := ?As) ?P ?n eq_refl eq_refl ?p] =>
      unfold Specif.value; simpl;
      match goal with
        | |- context[Dep_Type_BoundedIndex_nth_eq ?A_eq_dec (As := As) ?P ?n ?nth ?nth ?p] =>
          rewrite (@Dep_Type_BoundedIndex_nth_eq_refl _ A_eq_dec As P _ n nth p)
      end
  end.

Ltac Implement_Bound_Bag_Call :=
  match goal with
    | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                                 ?ValidImpls ?r_o ?r_n
      |- refine (Bind (CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?d) _) _ =>
      let r_o' := fresh "r_o'" in
      let AbsR_r_o' := fresh "AbsR_r_o'" in
      let refines_r_o' := fresh "refines_r_o'" in
      destruct (@refine_BagImplMethods qs_schema Index' DelegateReps DelegateImpls ValidImpls r_o r_n ridx H midx d) as [r_o' [refines_r_o' AbsR_r_o']];
        simpl in refines_r_o', AbsR_r_o';
        etransitivity;
        [ apply refine_bind;
          [apply refines_r_o'
          | unfold pointwise_relation; intros; higher_order_reflexivity
          ]
        | etransitivity;
          [ (* Simplify [CallBagImplMethod], get rid of the spurious cast,
               and reduce the bound [ret] *)
            unfold CallBagImplMethod; cbv beta; simpl;
            remove_spurious_Dep_Type_BoundedIndex_nth_eq;
            apply (proj1 (refineEquiv_bind_unit _ _))
          | simpl]
        ]; cbv beta; simpl in *
  end.

Ltac implement_bag_methods :=
etransitivity;
    [ repeat first [
               simpl; simplify with monad laws
              | remove_spurious_Dep_Type_BoundedIndex_nth_eq
              | Implement_If_Then_Else
              | Implement_If_Opt_Then_Else
              | Implement_Bound_Bag_Call
              | Implement_Bound_Join_Comp_Lists
              | Implement_AbsR_Relation
              | match goal with
                    |- context[CallBagImplMethod _ _ _ _ _] =>
                    unfold CallBagImplMethod; cbv beta; simpl
                end
              | higher_order_reflexivity ] |];
    (* Clean up any leftover CallBagImplMethods *)
      repeat (cbv beta; simpl;
          match goal with
              |- appcontext[CallBagImplMethod] =>
              unfold CallBagImplMethod; cbv beta; simpl;
              try remove_spurious_Dep_Type_BoundedIndex_nth_eq
          end);
    higher_order_reflexivity.

Ltac FullySharpenQueryStructure' qs_schema Index :=
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
                            )))
  end; simpl; intros;
  [repeat split; intros; try exact tt; implement_bag_constructors
  | repeat split; intros; try exact tt; implement_bag_methods].

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
                            )))
  end; simpl; intros;
  [ repeat split; intros; try exact tt;
    try (etransitivity;
         [eapply (@Initialize_IndexedQueryStructureImpls_AbsR qs_schema Index)
         | ];
         cbv beta;
         unfold Initialize_IndexedQueryStructureImpls',
         CallBagImplConstructor; simpl;
         higher_order_reflexivity
        )
  | repeat split; intros; try exact tt
  ].


Ltac Focused_refine_Query :=
  match goal with

    | |- context[ Count (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_Count ResultT body') at 1;
                         clear refine_body' ] )

    | |- context[ MaxN (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_MaxN body') at 1;
                         clear refine_body' ] )

    | |- context[ SumN (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_SumN body') at 1;
                         clear refine_body' ] )

    | |- context[ MaxZ (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_MaxZ body') at 1;
                         clear refine_body' ] )

    | |- context[ SumZ (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_SumZ body') at 1;
                         clear refine_body' ] )

    | |- context[ Max (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_Max body') at 1;
                         clear refine_body' ] )

    | |- context[ Sum (@Query_For ?ResultT ?body) ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         setoid_rewrite (@refine_Sum body') at 1;
                         clear refine_body' ] )

    | |- context[ @Query_For ?ResultT ?body ] =>
      makeEvar (Comp (list ResultT))
               ltac:(fun body' =>
                       let refine_body' := fresh in
                       assert (refine body body') as refine_body';
                     [ |
                       setoid_rewrite refine_body';
                         setoid_rewrite (@refine_For_List ResultT body') at 1;
                         clear refine_body' ] )

  end.

Ltac find_equiv_tl a As f g :=
  (* Find an equivalent function on just the tail of an ilist*)
  let a := fresh in
  let H := fresh in
  assert (forall a : ilist _ (a :: As), f a = g (ilist_tl a)) as H;
    [let a := fresh in
     intro a;
       match goal with
           |- ?f = ?g (ilist_tl a)=>
           let f' :=  match eval pattern (ilist_tl a) in f
                      with ?f' (ilist_tl a) => eval simpl in f' end in
                   unify f' g
               end; reflexivity
             | clear H].

Ltac Realize_CallBagMethods :=
  match goal with
    | H : @DelegateToBag_AbsR ?qs_schema ?BagIndexKeys ?r_o ?r_n
      |- context [CallBagMethod ?idx' BagEnumerate _ _] =>
      generalize H; clear;
      intros; eapply (@realizeable_Enumerate qs_schema BagIndexKeys r_n r_o idx' H)

    | H : @DelegateToBag_AbsR ?qs_schema ?BagIndexKeys ?r_o ?r_n
      |- context [CallBagMethod ?idx' BagFind _ ?st] =>
      generalize H; clear;
      intros; eapply (@realizeable_Find qs_schema BagIndexKeys r_n r_o idx' st H)
  end.

Ltac distribute_filters_to_joins' :=
  match goal with
      |- refine
           (l <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond; _)
           _ =>
      etransitivity; (* Recursively drill under the binds *)
        [ apply refine_under_bind; intros; cbv beta; simpl; distribute_filters_to_joins'
        | cbv beta; simpl;
          match goal with
              |- refine (l' <- Join_Filtered_Comp_Lists _ _ _;
                         l'' <- Join_Filtered_Comp_Lists _ _ _;
                         _)
                        _ =>

              rewrite <- refineEquiv_bind_bind at 1;
                etransitivity;
                [ repeat match goal with
                             |- refine (Bind (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                              Join_Filtered_Comp_Lists
                                                (filter (fun a : ilist _ (?heading1 :: ?heading2 :: ?headings) =>
                                                           @?f a && @?g a) l') ?l2' ?cond2) _)
                                       _ => first (* No test case for this branch *)
                                              [ makeEvar (ilist (@Tuple) headings -> bool)
                                                         ltac:(fun f' =>
                                                                 find_equiv_tl heading1 headings f f';
                                                               let Comp_l2 := fresh in
                                                               assert
                                                                 (forall a : ilist (@Tuple) headings,
                                                                  exists v : list (@Tuple heading1),
                                                                    refine (l2 a) (ret v)) as Comp_l2
                                                                   by Realize_CallBagMethods;
                                                               etransitivity;
                                                               [ eapply refine_bind;
                                                                 [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb heading1 heading2 headings f' g l2 l2' cond1 cond2 Comp_l2 l1)
                                                                 | intro; higher_order_reflexivity ]
                                                               | ])
                                              | etransitivity;
                                                [ eapply refine_bind;
                                                  [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb heading1 heading2 headings f g l2 l2' cond1 cond2 l1)
                                                  | intro; higher_order_reflexivity ]
                                                | ]
                                              ]

                           | |- refine (Bind (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                              Join_Filtered_Comp_Lists (a := ?heading2)
                                                                       (@filter (ilist _ (?heading1 :: ?headings)) ?f l') ?l2' ?cond2) _)
                                       _ =>   first
                                                [ makeEvar (ilist (@Tuple) headings -> bool) (* No test case for this branch either *)
                                                           ltac:(fun f' =>
                                                                   find_equiv_tl heading1 headings f f';
                                                                 let Comp_l2 := fresh in
                                                                 assert
                                                                   (forall a : ilist (@Tuple) headings,
                                                                    exists v : list (@Tuple heading1),
                                                                      refine (l2 a) (ret v)) as Comp_l2
                                                                     by Realize_CallBagMethods;
                                                                 etransitivity;
                                                                 [ eapply refine_bind;
                                                                   [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_hd heading1 heading2 headings f' l2 l2' cond1 cond2 Comp_l2 l1)
                                                                   | intro; higher_order_reflexivity ]
                                                                 | ])
                                                | eapply refine_bind;
                                                  [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_tail heading1 heading2 headings f l2 l2' cond1 cond2 l1)
                                                  | intro; higher_order_reflexivity] ]
                           (* If there's no filter on the first list, we're done. *)
                           | |- refine (Bind (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                              Join_Filtered_Comp_Lists l' ?l2' ?cond2) _)
                                       _ => reflexivity


                         end
                | rewrite refineEquiv_bind_bind at 1; reflexivity ]

            | |- refine (l' <- Join_Filtered_Comp_Lists _ _ _;
                         List_Query_In _ _)
                        _ =>
              repeat match goal with
                         |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                                    List_Query_In (ResultT := ?ResultT)
                                                  (filter (fun a : ilist _ (?heading :: ?headings) =>
                                                             @?f a && @?g a) l') ?resultComp)
                                   _ =>
                         first [makeEvar (ilist (@Tuple) headings -> bool)
                                         ltac:(fun f' => find_equiv_tl heading headings f f';
                                               let Comp_l2 := fresh in
                                               assert
                                                 (forall a : ilist (@Tuple) headings,
                                                  exists v : list (@Tuple heading),
                                                    refine (l2 a) (ret v)) as Comp_l2
                                                   by Realize_CallBagMethods;
                                               etransitivity;
                                               [apply (@refine_Join_Filtered_Comp_Lists_filter_hd_andb heading headings f' g ResultT resultComp l2 cond' Comp_l2 l1)
                                               | ])
                               | etransitivity;
                                 [apply (@refine_Join_Filtered_Comp_Lists_filter_tail_andb heading headings f ResultT resultComp l2 ) | ] ]

                       | |- refine
                              (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                               List_Query_In (ResultT := ?ResultT)
                                             (@filter (ilist _ (?heading :: ?headings)) ?f l') ?resultComp)
                              _ =>
                         first [ makeEvar (ilist (@Tuple) headings -> bool)
                                          ltac:(fun f' => find_equiv_tl heading headings f f';
                                                let Comp_l2 := fresh in
                                                assert
                                                  (forall a : ilist (@Tuple) headings,
                                                   exists v : list (@Tuple heading),
                                                     refine (l2 a) (ret v)) as Comp_l2 by
                                                      Realize_CallBagMethods;
                                                apply (@refine_Join_Filtered_Comp_Lists_filter_hd heading headings f' ResultT resultComp l2 Comp_l2 l1))
                               | apply (@refine_Join_Filtered_Comp_Lists_filter_tail heading headings f ResultT resultComp l2 cond' l1) ]

                     end
          end
        ]
    | |- _ => higher_order_reflexivity

  end.

Ltac distribute_filters_to_joins :=
  etransitivity;
  [ distribute_filters_to_joins' | cbv beta; simpl ].

Ltac convert_filter_search_term_to_find :=
  match goal with
    | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- refine (l <- Join_Filtered_Comp_Lists (a := ?heading) (As := ?headings) ?l1
                   (fun _ => l' <- CallBagMethod ?idx BagEnumerate ?r_n ();
                    ret (snd l')) ?f;
                 _) _ =>
      match f with
        (* Try non-dependent search term first *)
        | fun a => (?MatchIndexSearchTerm ?st (ilist_hd a)) && true =>
          let r := fresh in
          pose proof (@refine_Join_Comp_Lists_To_Find _ _ r_o r_n H _ l1 idx st) as r;
            simpl in r; rewrite r; clear r
        (* Then do dependent search term  *)
        | fun a => (?MatchIndexSearchTerm (@?st a) (ilist_hd a)) && true =>
          let stT := type of st in
          match stT with _ -> ?stT =>
                         makeEvar (ilist (@Tuple) headings -> stT)
                                  ltac:(fun st_dep =>
                                          let eqv := fresh in
                                          let a := fresh in
                                          assert (forall (a : ilist _ (_ :: _)),
                                                    st a = st_dep (ilist_tl a) ) as eqv;
                                        [intro a; simpl;
                                         match goal with
                                             |- ?st' = _ =>

                                             let st'' := eval pattern (ilist_tl a) in st' in                                                     match st'' with | ?f (ilist_tl a) =>
                                                                                                                                                                   let f' := eval simpl in f in unify f' st_dep end
                                         end; simpl; reflexivity |
                                         let r := fresh in
                                         pose proof (refine_Join_Comp_Lists_To_Find_dep
                                                       H l1 idx
                                                       st_dep) as r;
                                           simpl in r; rewrite r; clear r eqv
                                        ]
                                       )
          end
            (* If we can't coerce [f] to a search term, leave it unchanged. *)
      end end.

Ltac implement_filters_with_find k k_dep:=
  repeat (try (convert_filter_to_search_term; (* This will fail if there's no filter on the join. *)
               [first [find_equivalent_search_term k
                      | find_equivalent_search_term_pair k_dep]
               | cbv beta; simpl; convert_filter_search_term_to_find]);
          apply refine_under_bind; intros);
  apply List_Query_In_Return.

Ltac implement_Query' k k_dep:=
  Focused_refine_Query;
  [ (* Step 1: Implement [In] by enumeration. *)
    implement_In;
    (* Step 2: Convert where clauses into compositions of filters. *)
    repeat convert_Where_to_filter;
    (* Step 3: Do some simplication.*)
    repeat setoid_rewrite <- filter_and;
    try setoid_rewrite andb_true_r;
    (* Step 4: Move filters to the outermost [Join_Comp_Lists] to which *)
    (* they can be applied. *)
    repeat setoid_rewrite Join_Filtered_Comp_Lists_id;
    distribute_filters_to_joins;
    (* Step 5: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep
  |
  ].

Ltac implement_Query CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  implement_Query'
    ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex)
           ltac:(find_simple_search_term_dep makeClause_dep EarlyIndex_dep LastIndex_dep).

Ltac cleanup_Count :=
  repeat first [ setoid_rewrite app_nil_r
               | setoid_rewrite filter_true
               | setoid_rewrite map_map
               | setoid_rewrite map_app
               | setoid_rewrite map_length
               ].

Ltac observer CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  implement_Query CreateTerm EarlyIndex LastIndex
                  makeClause_dep EarlyIndex_dep LastIndex_dep;
  simpl; simplify with monad laws;
  cbv beta; simpl; commit;
  cleanup_Count;
  finish honing.

Ltac initializer :=
  try simplify with monad laws;
  rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure;
  cbv beta; simpl;
  try simplify with monad laws;
  finish honing.

Ltac deletion CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
    try simplify with monad laws;
      etransitivity;
      [ repeat match goal with
                 | |- context[Query_For _] =>
                   implement_Query CreateTerm EarlyIndex LastIndex
                                   makeClause_dep EarlyIndex_dep LastIndex_dep;
                     eapply refine_under_bind; intros
               end;
        repeat setoid_rewrite refine_if_If at 1;
        repeat setoid_rewrite refine_If_Then_Else_Bind at 1;
        repeat setoid_rewrite Bind_refine_If_Then_Else at 1;
        repeat eapply refine_If_Then_Else;
        try simplify with monad laws; cbv beta; simpl;
        (
         (implement_QSDeletedTuples ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex);
         try simplify with monad laws;
         cbv beta; simpl;
         implement_EnsembleDelete_AbsR ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex);
         simplify with monad laws;
         reflexivity) ||

           (try simplify with monad laws;
          simpl; commit; reflexivity))
      | cbv beta; simpl; try simplify with monad laws; cleanup_Count; finish honing ].

Ltac insertion CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
      Implement_Insert_Checks;
    etransitivity;
      [ repeat match goal with
                 | |- context[Query_For _] =>
                   setoid_rewrite refineEquiv_swap_bind at 1;
                     implement_Query CreateTerm EarlyIndex LastIndex
                                     makeClause_dep EarlyIndex_dep LastIndex_dep;
                     eapply refine_under_bind; intros
               end;
        repeat setoid_rewrite refine_if_If at 1;
        repeat setoid_rewrite refine_If_Then_Else_Bind at 1;
        repeat setoid_rewrite Bind_refine_If_Then_Else at 1;
        repeat eapply refine_If_Then_Else;
        try simplify with monad laws; cbv beta; simpl;
        match goal with
          (* Implement the then branch *)
          | [ H : DelegateToBag_AbsR ?r_o ?r_n
              |- context[{r_n' |
                          DelegateToBag_AbsR
                            (UpdateUnConstrRelation ?r_o ?TableID
                                                    (EnsembleInsert
                                                       {| elementIndex := _; indexedElement := ?tup |}
                                                       (GetUnConstrRelation ?r_o ?TableID))) r_n'}]]
            => repeat setoid_rewrite <- refineEquiv_bind_bind;
              setoid_rewrite (@refine_BagADT_QSInsert _ _ r_o r_n H TableID tup);
              try (simplify with monad laws; higher_order_reflexivity)
          (* Implement the else branch *)
          | [ H : DelegateToBag_AbsR ?r_o ?r_n
              |- context[{r_n' | DelegateToBag_AbsR ?r_o r_n'}]] =>
            match goal with
            | |- context[{idx | UnConstrFreshIdx (GetUnConstrRelation r_o ?TableID) idx}] =>
              destruct ((proj2 H) TableID) as [l [[bnd fresh_bnd] _]];
                refine pick val bnd;
                [ simplify with monad laws;
                  refine pick val r_n;
                  [ simplify with monad laws;
                    higher_order_reflexivity
                  | eassumption ]
                | eassumption]
            end
        end
      | cbv beta; simpl; try simplify with monad laws; cleanup_Count; finish honing ].

Ltac method CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  match goal with
    | [ |- context[EnsembleInsert _ _]] =>
      insertion CreateTerm EarlyIndex LastIndex
                makeClause_dep EarlyIndex_dep LastIndex_dep
    | [ |- context[Query_For _]] =>
      observer CreateTerm EarlyIndex LastIndex
               makeClause_dep EarlyIndex_dep LastIndex_dep
    | [ |- context[EnsembleDelete _ _]] =>
      deletion CreateTerm EarlyIndex LastIndex
               makeClause_dep EarlyIndex_dep LastIndex_dep
  end.

Ltac honeOne CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  match goal with
    | [ |- context[@Build_consDef _ (Build_consSig ?id _) _] ] =>
      hone constructor id; [ initializer | ]
    | [ |- context[@Build_methDef _ (Build_methSig ?id _ _) _] ] =>
      hone method id; [ method CreateTerm EarlyIndex LastIndex
                               makeClause_dep EarlyIndex_dep LastIndex_dep | ]
  end.

Ltac plan CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  repeat (honeOne CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep).

(*Ltac planDefault :=
  plan default default default default default default. *)

Global Opaque CallBagMethod.
Global Opaque CallBagConstructor.
Global Opaque Initialize_IndexedQueryStructure.
