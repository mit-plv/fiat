Require Export Coq.Bool.Bool Coq.Strings.String Coq.Strings.Ascii.
Require Export Fiat.Common.DecideableEnsembles
        Fiat.Common.List.ListFacts
        Fiat.Common.BoolFacts
        Fiat.Common.LogicFacts
        Fiat.Common.List.FlattenList
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.IterateBoundedIndex
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Specification.SearchTerms.ListInclusion
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Specification.SearchTerms.InRange
        Fiat.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        Fiat.QueryStructure.Automation.General.QueryAutomation
        Fiat.QueryStructure.Automation.General.InsertAutomation
        Fiat.QueryStructure.Automation.General.DeleteAutomation
        Fiat.QueryStructure.Automation.General.QueryStructureAutomation
        Fiat.QueryStructure.Automation.Constraints.TrivialConstraintAutomation
        Fiat.QueryStructure.Automation.Constraints.FunctionalDependencyAutomation
        Fiat.QueryStructure.Automation.Constraints.ForeignKeyAutomation
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagImplementation
        Fiat.QueryStructure.Implementation.ListImplementation
        Fiat.QueryStructure.Specification.Constraints.tupleAgree
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        Fiat.QueryStructure.Implementation.Operations.BagADT.Refinements
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        Fiat.QueryStructure.Automation.SearchTerms.InclusionSearchTerms
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.SearchTerms.RangeSearchTerms
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Automation.Common
        Fiat.QueryStructure.Implementation.Operations.

Require Import Coq.Logic.Eqdep_dec
        Fiat.ADT.ComputationalADT
        Fiat.ADTNotation.BuildComputationalADT
        Fiat.ADTRefinement.GeneralBuildADTRefinements.

Export Lists.List.ListNotations.

Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  repeat setoid_rewrite <- (@query_eq_true_iff _ _);
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
           {n}
           {indices : Vector.t RawSchema n}
           (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) indices)
           (idx : Fin.t _)
  : ADTSig :=
  BagSig (@RawTuple (rawSchemaHeading (Vector.nth indices idx)))
         (BagSearchTermType (ith3 Index idx))
         (BagUpdateTermType (ith3 Index idx)).

Definition Build_IndexedQueryStructure_Impl_Specs
           {n}
           {indices : Vector.t RawSchema n}
           (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) indices)
           (idx : Fin.t _)
  : ADT (@Build_IndexedQueryStructure_Impl_Sigs n indices Index idx) :=
  @BagSpec (@RawTuple (rawSchemaHeading (Vector.nth indices idx)))
           (BagSearchTermType (ith3 Index idx))
           (BagUpdateTermType (ith3 Index idx))
           (BagMatchSearchTerm (ith3 Index idx))
           (BagApplyUpdateTerm (ith3 Index idx)).
Definition
  Build_IndexedQueryStructure_Impl_cRep
  {n}
  {indices : Vector.t RawSchema n}
  (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) indices)
  (DelegateReps : Fin.t n -> Type)
  : Type :=
  Iterate_Dep_Type_BoundedIndex DelegateReps.

Definition
  GetIndexedQueryStructureRelation
  {n}
  {indices : Vector.t RawSchema n}
  {Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) indices}
  {DelegateReps : Fin.t n -> Type}
  (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
  idx
  : DelegateReps idx :=
  Lookup_Iterate_Dep_Type DelegateReps r_n idx.

Definition Build_IndexedQueryStructure_Impl_AbsR
           {qs_schema : RawQueryStructureSchema}
           (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch))
                           (qschemaSchemas qs_schema))
           (DelegateReps : Fin.t _ -> Type)
           (DelegateImpls : forall idx,
               ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           (ValidImpls
            : forall idx,
               refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                         (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
           (r_o : IndexedQueryStructure qs_schema Index)
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps)
  : Prop :=
  forall idx : Fin.t _,
    AbsR (ValidImpls idx)
         (GetIndexedRelation r_o idx) (GetIndexedQueryStructureRelation r_n idx).

(* These are opaque aliases for pcConstructors and pcMethods which we use to *)
(* prevent Bag methods from being aggressively inlined in the final implementation. *)
Definition callConstructor := ComputationalADT.pcConstructors.
Definition callMethod := ComputationalADT.pcMethods.

Definition CallBagImplMethod
           {n}
           {schemas : Vector.t RawSchema n}
           (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
           (DelegateReps : Fin.t _ -> Type)
           (DelegateImpls : forall idx,
               ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx midx
           (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps) :=
  callMethod (DelegateImpls idx) midx (GetIndexedQueryStructureRelation r_n idx).

Definition CallBagImplConstructor
           {n}
           {schemas : Vector.t RawSchema n}
           (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
           (DelegateReps : Fin.t _ -> Type)
           (DelegateImpls : forall idx,
               ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
           idx cidx :=
  callConstructor (DelegateImpls idx) cidx.

Lemma refine_BagImplConstructor
      {n}
      {schemas : Vector.t RawSchema n}
      (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
      (DelegateReps : Fin.t _ -> Type)
      (DelegateImpls : forall idx,
          ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
      (ValidImpls
       : forall idx,
          refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                    (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx))))
  :  forall (ridx : Fin.t _) cidx,
    Lift_Constructor2P
      (ConstructorDom
         (BagSig RawTuple (BagSearchTermType (ith3 Index ridx))
                 (BagUpdateTermType (ith3 Index ridx))) cidx)
      (fun c c' =>
         exists r_o' ,
           refine c (ret r_o')
           /\ AbsR (ValidImpls ridx) r_o' c')
      (@CallBagConstructor _ (ith3 Index ridx) cidx)
      (CallBagImplConstructor DelegateReps DelegateImpls cidx).
Proof.
  intros.
  generalize (ADTRefinementPreservesConstructors (ValidImpls ridx) cidx).
  eapply (fun P H => Lookup_Iterate_Dep_Type P H cidx).
  simpl; split; intuition.
  unfold refine in *.
  specialize (H _ (ReturnComputes _));
    computes_to_inv; subst.
  eexists;
    unfold CallBagImplConstructor in *; simpl in *.
  split; simpl.
  - intros v' Comp_v;  computes_to_inv; subst.
    unfold CallBagConstructor; simpl; computes_to_econstructor.
  - eapply H'.
Qed.

Lemma refine_BagImplMethods
      {qs_schema : RawQueryStructureSchema}
      (schemas := qschemaSchemas qs_schema)
      (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
      (DelegateReps : Fin.t _ -> Type)
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
    forall midx,
      Lift_Method2P
        (fst (MethodDomCod
                (BagSig RawTuple (BagSearchTermType (ith3 Index ridx))
                        (BagUpdateTermType (ith3 Index ridx))) midx))
        (snd (MethodDomCod
                (BagSig RawTuple (BagSearchTermType (ith3 Index ridx))
                        (BagUpdateTermType (ith3 Index ridx))) midx))
        (fun cod m m' =>
           exists r_o',
             refine m (ret (r_o', snd m'))
             /\ AbsR (ValidImpls ridx) r_o' (fst m'))
        (fun m m' =>
           exists r_o',
             refine m (ret r_o')
             /\ AbsR (ValidImpls ridx) r_o' m')
        (CallBagMethod ridx midx r_o)
        (CallBagImplMethod DelegateReps DelegateImpls midx r_n)
.
Proof.
  intros.
  generalize (ADTRefinementPreservesMethods (ValidImpls ridx) midx
                                            (GetIndexedRelation r_o ridx)
                                            (GetIndexedQueryStructureRelation r_n ridx)
                                            (H ridx)).
  eapply (fun P H => Lookup_Iterate_Dep_Type P H midx);
    simpl in *; intuition.
  - specialize (H0 t _ (ReturnComputes _)); computes_to_inv; subst;
    unfold CallBagImplMethod, CallBagMethod in *; simpl in *.
    unfold cMethods, callMethod in *; simpl in *; rewrite <- H0''; simpl.
    eexists; split; eauto.
    intros v Comp_v; computes_to_inv; subst.
    repeat computes_to_econstructor; eauto.
  - specialize (H0 _ (ReturnComputes _)); computes_to_inv; subst;
    unfold CallBagImplMethod, CallBagMethod in *; simpl in *.
    unfold cMethods, callMethod in *; simpl in *; rewrite <- H0''; simpl.
    eexists; split; eauto.
    intros v Comp_v; computes_to_inv; subst.
    repeat computes_to_econstructor; eauto.
  - specialize (H0 t _ (ReturnComputes _)); computes_to_inv; subst;
    unfold CallBagImplMethod, CallBagMethod in *; simpl in *.
    unfold cMethods in H0'; simpl in *.
    eexists; split; eauto.
    intros v Comp_v; computes_to_inv; subst.
    repeat computes_to_econstructor; eauto.
  - specialize (H0 t _ (ReturnComputes _)); computes_to_inv; subst;
    unfold CallBagImplMethod, CallBagMethod in *; simpl in *.
    unfold cMethods, callMethod in *; simpl in *; rewrite <- H0''; simpl.
    eexists; split; eauto.
    intros v Comp_v; computes_to_inv; subst.
    repeat computes_to_econstructor; eauto.
  - specialize (H0 t _ (ReturnComputes _)); computes_to_inv; subst;
    unfold CallBagImplMethod, CallBagMethod in *; simpl in *.
    unfold cMethods, callMethod in *; simpl in *; rewrite <- H0''; simpl.
    eexists; split; eauto.
    intros v Comp_v; computes_to_inv; subst.
    repeat computes_to_econstructor; eauto.
  - specialize (H0 t t0 _ (ReturnComputes _)); computes_to_inv; subst;
    unfold CallBagImplMethod, CallBagMethod in *; simpl in *.
    unfold cMethods, callMethod in *; simpl in *; rewrite <- H0''; simpl.
    eexists; split; eauto.
    intros v Comp_v; computes_to_inv; subst.
    repeat computes_to_econstructor; eauto.
Qed.

Definition Initialize_IndexedQueryStructureImpls'
           {n}
           {schemas}
           (Index : ilist3 (n := n) (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch)) schemas)
           (DelegateReps : Fin.t _ -> Type)
           (DelegateImpls : forall idx,
               ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
  : @Build_IndexedQueryStructure_Impl_cRep _ _ Index DelegateReps :=
  Iterate_Dep_Type_equiv''
    DelegateReps
    (fun idx  =>
       CallBagImplConstructor DelegateReps DelegateImpls BagEmpty ).

Lemma Initialize_IndexedQueryStructureImpls_AbsR
      {qs_schema : RawQueryStructureSchema}
  : forall
    (Index : ilist3 (B := fun sch => SearchUpdateTerms (rawSchemaHeading sch))
                    (qschemaSchemas qs_schema))
    (DelegateReps : Fin.t _ -> Type)
    (DelegateImpls : forall idx,
        ComputationalADT.pcADT (Build_IndexedQueryStructure_Impl_Sigs Index idx) (DelegateReps idx))
    (ValidImpls
     : forall idx,
        refineADT (Build_IndexedQueryStructure_Impl_Specs Index idx)
                  (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
    refine (r_o <- @Initialize_IndexedQueryStructure _ _ Index;
            {r_n | Build_IndexedQueryStructure_Impl_AbsR DelegateReps DelegateImpls ValidImpls r_o r_n})
           (ret (Initialize_IndexedQueryStructureImpls' DelegateReps DelegateImpls)).
Proof.
  destruct qs_schema.
  unfold Build_IndexedQueryStructure_Impl_AbsR, GetIndexedRelation.
  simpl; clear qschemaConstraints.
  induction qschemaSchemas; intros;
  pose proof (ilist3_invert _ Index) as H'; simpl in H'; subst.
  - simpl; simplify with monad laws.
    computes_to_econstructor;  computes_to_inv; subst.
    eapply (Lookup_Iterate_Dep_Type); simpl.
    econstructor.
  - destruct H' as [idx' [Index' Index_eq] ]; subst.
    simpl; unfold CallBagConstructor; simpl; simplify with monad laws.
    pose proof (IHqschemaSchemas
                  Index'
                  (fun idx => DelegateReps (Fin.FS idx))
                  (fun idx => DelegateImpls (Fin.FS idx))
                  (fun idx => ValidImpls (Fin.FS idx))
                  _ (ReturnComputes _)).
    unfold refine; intros;  computes_to_inv; subst.
    computes_to_econstructor; eauto.
    computes_to_econstructor.
    intro idx.
    pose proof (@refine_BagImplConstructor
                  _ _  _ DelegateReps DelegateImpls ValidImpls idx BagEmpty).
    revert qschemaSchemas IHqschemaSchemas DelegateReps idx' Index' DelegateImpls ValidImpls
           v0 H H' H0.
    pattern n, idx; apply Fin.caseS; simpl; intros.
    + destruct (H0) as [r_o' [refines_r_o' AbsR_r_o'] ].
      pose proof (refines_r_o' _ (ReturnComputes _)).
      unfold CallBagConstructor in *; simpl in *;  computes_to_inv; subst.
      apply AbsR_r_o'.
    + eapply H'.
Qed.

Definition Update_Build_IndexedQueryStructure_Impl_cRep
           qs_schema Index DelegateReps
           (r_n : Build_IndexedQueryStructure_Impl_cRep (indices := qschemaSchemas qs_schema) Index DelegateReps)
           TableID (r_n' : DelegateReps TableID)
  : Build_IndexedQueryStructure_Impl_cRep Index DelegateReps :=
  Update_Iterate_Dep_Type TableID _ r_n r_n'.

Lemma Update_Build_IndexedQueryStructure_Impl_AbsR
  : forall qs_schema Index DelegateReps DelegateImpls
           ValidImpls r_o r_n TableID r_o' r_n',
    @Build_IndexedQueryStructure_Impl_AbsR qs_schema Index DelegateReps DelegateImpls
                                           ValidImpls r_o r_n
    -> AbsR (ValidImpls TableID) r_o' r_n'
    -> @Build_IndexedQueryStructure_Impl_AbsR
         qs_schema Index DelegateReps DelegateImpls
         ValidImpls (UpdateIndexedRelation _ _ r_o TableID r_o')
         (Update_Build_IndexedQueryStructure_Impl_cRep _ _ _ r_n TableID r_n').
Proof.
  unfold Build_IndexedQueryStructure_Impl_AbsR,
  Update_Build_IndexedQueryStructure_Impl_cRep,
  UpdateIndexedRelation; intros.
  destruct (fin_eq_dec idx TableID); subst; simpl.
  - unfold GetIndexedQueryStructureRelation,
    GetIndexedRelation.
    erewrite Lookup_Update_Iterate_Dep_Type_eq.
    rewrite i3th_replace_Index_eq; eassumption.
  - unfold GetIndexedQueryStructureRelation,
    GetIndexedRelation.
    rewrite i3th_replace_Index_neq,
    Lookup_Update_Iterate_Dep_Type_neq; eauto.
Qed.

Arguments BuildIndexSearchTerm : simpl never.
Arguments MatchIndexSearchTerm : simpl never.
Opaque Initialize_IndexedQueryStructure.

Ltac fields storage :=
  match eval cbv delta [storage] in storage with
  | let src := ?X in _ => X
  end.

Lemma bool_dec_simpl : forall b,
    ?[bool_dec b true] = b.
Proof.
  intros; find_if_inside; destruct b; congruence.
Qed.

Ltac prove_extensional_eq :=
  clear;
  try rewrite !bool_dec_simpl;
  try rewrite !andb_true_r;
  unfold ExtensionalEq;
  repeat find_if_inside; first [ solve [intuition] | solve [exfalso; intuition] | idtac ].

(* Default tactics for handling *)

(* Recurse over the list of search term indexes [fs],
 consulting the list of attribute name and value pairs in [fds] to
 find matching search terms via [findMatchingTerm].
 *)

Ltac createTerm f fds tail fs EarlyIndex LastIndex k :=
  match fs with
  | [ ] => k tail
  | [{| KindIndexKind := ?kind;
        KindIndexIndex := ?s|} ] =>
    (* *)
    let is_equality := eval compute in (string_dec kind EqualityIndex) in
        match is_equality with
        | left _ =>
          (findMatchingTerm
             fds kind s
             ltac:(fun X => k (Some X, tail)))
            || k (@None (Domain f s), tail)
        | right _ => LastIndex f fds tail fs kind s k
        end
  | {| KindIndexKind := ?kind;
       KindIndexIndex := ?s|} :: ?fs' =>
    createTerm
      f fds tail fs' EarlyIndex LastIndex
      ltac:(fun rest =>
              let is_equality := eval compute in (string_dec kind EqualityIndex) in
                  match is_equality with
                  | left _  =>
                    (findMatchingTerm
                       fds kind s
                       ltac:(fun X => k (Some X, rest)))
                      || k (@None (Domain f s), rest)
                  | right _ => EarlyIndex f fds tail fs kind EarlyIndex LastIndex rest s k
                  end)
  end.


(* Using a list of search term attributes [fs],
   a list of attribute name and value pairs [fds],
   use [createTerm] to recurse over [fs]
   using the schema for [SC]
 *)
Ltac makeTerm fs SC fds tail EarlyIndex LastIndex k :=
  createTerm SC fds tail fs EarlyIndex LastIndex k.

(* Given a storage schema [SC], a filter [F],
   a list of indexed attributes [search_attrs] and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]). *)

Ltac findGoodTerm SC F indexed_attrs ClauseMatch k :=
  (* F needs to have the shape fun a => ?[f a] for the recursive ClauseMatch to fire.*)
  match F with
  | fun a => ?[@?f a] =>
    match type of f with
    (* Equality Search Terms *)
    | forall a, {?X = GetAttributeRaw _ ?fd} + {_} =>
      let H := fresh in
      assert (List.In (@Build_KindIndex SC EqualityIndex fd) indexed_attrs) as H
          by (clear; subst_all; simpl; intuition eauto); clear H;
      k ((@Build_KindIndex SC EqualityIndex fd), X) (fun _ : @RawTuple SC => true)
    | forall a, {GetAttributeRaw _ ?fd = ?X} + {_} =>
      let H := fresh in
      assert (List.In (@Build_KindIndex SC EqualityIndex fd) indexed_attrs) as H
          by (clear; subst_all; simpl; intuition eauto); clear H;
      k ((@Build_KindIndex SC EqualityIndex fd), X) (fun _ : @RawTuple SC => true)
    | forall a, {?X = GetAttribute _ ?fd} + {_} =>
      let H := fresh in
      let fd' := (eval simpl in (ibound (indexb fd))) in
      assert (List.In (@Build_KindIndex SC EqualityIndex fd') indexed_attrs) as H
          by (clear; subst_all; simpl; intuition eauto); clear H;
      k ((@Build_KindIndex SC EqualityIndex fd'), X) (fun _ : @RawTuple SC => true)
    | forall a, {GetAttribute _ ?fd = ?X} + {_} =>
      let H := fresh in
      let fd' := (eval simpl in (ibound (indexb fd))) in
      assert (List.In (@Build_KindIndex SC EqualityIndex fd') indexed_attrs) as H
          by (clear; subst_all; simpl; intuition eauto); clear H;
      k ((@Build_KindIndex SC EqualityIndex fd'), X) (fun _ : @RawTuple SC => true)


    | _ => ClauseMatch SC F indexed_attrs f k

    end
  | fun a => (@?f a) && (@?g a) =>
    findGoodTerm SC f indexed_attrs ClauseMatch
                 ltac:(fun fds1 tail1 =>
                         findGoodTerm SC g indexed_attrs ClauseMatch
                                      ltac:(fun fds2 tail2 =>
                                              k (fds1, fds2) (fun tup : @RawTuple SC => (tail1 tup) && (tail2 tup))))
  | _ => k tt F
  end.

Ltac find_simple_search_term
     ClauseMatch EarlyIndex LastIndex
     qs_schema idx filter_dec search_term :=
  match type of search_term with
  | BuildIndexSearchTerm ?indexed_attrs =>
    let SC := constr:(GetNRelSchemaHeading (qschemaSchemas qs_schema) idx) in
    findGoodTerm SC filter_dec indexed_attrs ClauseMatch
                 ltac:(fun fds tail =>
                         let tail := eval simpl in tail in
                             makeTerm indexed_attrs SC fds tail EarlyIndex LastIndex ltac:(fun tm => unify tm search_term;
                                                                                           unfold ExtensionalEq, MatchIndexSearchTerm;
                                                                                           simpl; intro; try prove_extensional_eq
                      )) end.

Ltac implement_QSDeletedTuples find_search_term :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[Pick (QSDeletedTuples ?r_o ?idx ?DeletedTuples)] ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                    [ find_search_term qs_schema idx filter_dec search_term
                                    | let H' := fresh in
                                      pose (@refine_BagADT_QSDelete_fst _ _ r_o r_n H idx DeletedTuples _ search_term) as H';
                                        fold_string_hyps_in H'; fold_heading_hyps_in H';
                                        setoid_rewrite (H' eqv); clear H' eqv])
  end.

    Ltac implement_Count find_search_term :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- refine (Bind (Count For (UnConstrQuery_In _ ?idx (fun tup => Where (@?P tup) Return (@?f tup))))
                 _) _ ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ P _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                      [ find_search_term qs_schema idx filter_dec search_term
                                      |
                                      let H' := fresh in
                                      pose proof (@refine_BagFindBagCount
                                                    _
                                                   qs_schema indices
                                                   idx r_o r_n search_term P f H eqv) as H';
                                      fold_string_hyps_in H'; fold_heading_hyps_in H';
                                      rewrite H'; clear H' eqv
                                   ])
  | [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- refine (Bind (Count For (UnConstrQuery_In _ ?idx (fun tup => Where (@?P tup) Return _)))
                 _) _ ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ P _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                      [ find_search_term qs_schema idx filter_dec search_term
                                      |
                                      let H' := fresh in
                                      pose proof (@refine_BagFindBagCount unit
                                                   qs_schema indices
                                                   idx r_o r_n search_term P (fun _ => tt) _ H eqv) as H';
                                      fold_string_hyps_in H'; fold_heading_hyps_in H';
                                      rewrite H'; clear H' eqv
                                      ])
  end.

Ltac implement_simple_For find_search_term :=
         match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- refine (Bind (For (UnConstrQuery_In _ ?idx (fun tup => Where (@?P tup) Return (@?f tup))))
                 _) _ ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ P _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                      [ find_search_term qs_schema idx filter_dec search_term
                                      |
                                      let H' := fresh in
                                      pose proof (@refine_BagFindBag_single _
                                                   qs_schema indices
                                                   idx r_o r_n search_term P f _ H eqv) as H';
                                      fold_string_hyps_in H'; fold_heading_hyps_in H';
                                      rewrite H'; clear H' eqv
                                   ])
         | [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
             |- refine (For (UnConstrQuery_In _ ?idx (fun tup => Where (@?P tup) Return (@?f tup))))
                       _ ] =>
           let filter_dec := eval simpl in (@DecideableEnsembles.dec _ P _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                      [ find_search_term qs_schema idx filter_dec search_term
                                      |
                                      let H' := fresh in
                                      pose proof (@refine_BagFindBag_single _
                                                   qs_schema indices
                                                   idx r_o r_n search_term P f _ H eqv) as H';
                                      fold_string_hyps_in H'; fold_heading_hyps_in H';
                                      rewrite H'; clear H' eqv
                                      ])
  end.


Ltac implement_EnsembleDelete_AbsR find_search_term :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[{r_n' | DelegateToBag_AbsR
                           (UpdateUnConstrRelation ?r_o ?idx
                                                   (EnsembleDelete (GetUnConstrRelation ?r_o ?idx)
                                                                   ?DeletedTuples)) r_n'}] ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac:(fun search_term =>
                                     let eqv := fresh in
                                     assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                   [ find_search_term qs_schema idx filter_dec search_term
                                   | let H' := fresh in
                                     pose (@refine_BagADT_QSDelete_snd _ _ r_o r_n H idx DeletedTuples _ search_term eqv) as H';
                                       simpl in H';
                                       fold_string_hyps; fold_heading_hyps;
                                       fold_string_hyps_in H'; fold_heading_hyps_in H';
                                       setoid_rewrite H'; clear H'
                                  ] )
  end.


Ltac implement_Enumerate_filter find_search_term :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- context[For (l <- CallBagMethod ?idx BagEmpty ?r_n0 ();
                      (List_Query_In (filter (@DecideableEnsembles.dec _ ?DeletedTuples _) (snd l))
                                     ?resultComp))] ] =>
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
                                [ first [split_filters | k ] | first [split_filters | k] ] ))
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
                       | rewrite (@Join_Filtered_Comp_Lists_ExtensionalEq_filters _ _ _ _ _ l1 l2 f g eqv); clear eqv ])
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

Definition unit_Heading : RawHeading := {| AttrList := Vector.nil _ |}.

Definition unit_Tuple : @RawTuple unit_Heading := inil2.

Ltac get_ithDefault f n k :=
  match type of f with
  | ilist2 (B := @RawTuple) ?A -> ?C =>
    let G := fresh "G" in
    let p := fresh "p" in
    let H := fresh "H" in
    let proj := fresh "proj" in
    let proj := eval simpl in
    (fun b : ilist2 (B := @RawTuple) A => ith2 b n) in
        evar (G : @RawTuple (Vector.nth A n) -> C);
      assert (H : forall p, f p = G (proj p)) by
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
  | ilist2 (B := @RawTuple) ?A -> ?C =>
    let G := fresh "G" in
    let p := fresh "p" in
    let H := fresh "H" in
    let proj1 := fresh "proj" in
    let proj2 := fresh "proj" in
    let proj1 := eval simpl in
    (fun b : ilist2 (B := @RawTuple) A => ith2 unit_Tuple b m) in
        let proj2 := eval simpl in
        (fun b : ilist (@RawTuple) A => ith2 unit_Tuple b n)
          in evar (G : @RawTuple (nth_default unit_Heading A m)
                       -> @RawTuple (nth_default unit_Heading A n)
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

Ltac createTerm_dep dom f fds tail fs EarlyIndex LastIndex k :=
  match fs with
  | [{| KindIndexKind := ?kind;
        KindIndexIndex := ?s|} ] =>
    let is_equality := eval compute in (string_dec kind EqualityIndex) in
        match is_equality with
        | left _ =>
          (try findMatchingTerm fds kind s
               ltac:(fun X =>
                       k (fun x : dom => (Some (X x), tail x))))
            || k (fun x : dom => (@None (Domain f s), tail x))
        | right _ => LastIndex dom f fds tail fs kind s k
        end
  | {| KindIndexKind := ?kind;
       KindIndexIndex := ?s|} :: ?fs' =>
    createTerm_dep dom f fds tail fs'
                   EarlyIndex LastIndex
                   ltac:(fun rest =>
                           findMatchingTerm fds kind s
                                            ltac:(fun X =>
                                                    let is_equality := eval compute in (string_dec kind EqualityIndex) in
                                                        match is_equality with
                                                        | left _ =>
                                                          k (fun x : dom => (Some (X x), rest x))
                                                        end)
                                                   ||
                                                   let is_equality := eval compute in (string_dec kind EqualityIndex) in
                                                       match is_equality with
                                                       | left _ =>
                                                         k (fun x : dom => (@None (Domain f s), rest x))
                                                       end)
  end.

(* Legacy tactic-- should remove. *)
Ltac makeTerm_dep dom fs SC fds tail EarlyIndex LastIndex k :=
  createTerm_dep dom SC fds tail fs EarlyIndex LastIndex k.

(* Given a storage schema [SC], a filter [F],
   a list of indexed attributes [search_attrs] and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]). *)

Ltac findGoodTerm_dep SC F indexed_attrs visited_attrs makeClause k :=
  match F with
  | fun (a : ?T) b => ?[@?f a b] =>
    match type of f with
    | forall a b, {@?X a = GetAttributeRaw _ ?fd'} + {_} =>
      let H := fresh in
      assert (List.In (@Build_KindIndex SC EqualityIndex fd') indexed_attrs) as H
          by (clear; subst_all; simpl; intuition eauto); clear H;
      match eval simpl in
            (in_dec fin_eq_dec fd' visited_attrs) with
      | right _ => k (fd' :: visited_attrs)
                     (@Build_KindIndex SC EqualityIndex fd', X)
                     (fun (a : T) (_ : @RawTuple SC) => true)
      | left _ => k visited_attrs tt F
      end
    | forall a b, {GetAttributeRaw _ ?fd' = @?X a} + {_} =>
      let H := fresh in
      assert (List.In (@Build_KindIndex SC EqualityIndex fd') indexed_attrs) as H
          by (clear; subst_all; simpl; intuition eauto); clear H;
      match eval simpl in
            (in_dec fin_eq_dec fd' visited_attrs) with
      | right _ => k (fd' :: visited_attrs)
                     (@Build_KindIndex SC EqualityIndex fd', X)
                     (fun (a : T) (_ : @RawTuple SC) => true)
      | left _ => k visited_attrs tt F
      end

    | _ => makeClause SC F indexed_attrs visited_attrs f T k

    end
  | fun (a : ?T) b => (@?f a b) && (@?g a b) =>
    findGoodTerm_dep
      SC f indexed_attrs visited_attrs makeClause
      ltac:(fun v fds1 tail1 =>
              findGoodTerm_dep
                SC g indexed_attrs v makeClause
                ltac:(fun v' fds2 tail2 =>
                        k v' (fds1, fds2) (fun (a : T) (tup : @RawTuple SC) =>
                                             (tail1 a tup) && (tail2 a tup))))
  | _ => k visited_attrs tt F
  end.

Definition Dep_SearchTerm_Wrapper {A} {heading}
           (search_term_dep : @RawTuple heading -> A)
           (tup : @RawTuple heading) : A := search_term_dep tup.

Ltac find_simple_search_term_dep
     makeClause EarlyIndex LastIndex
     qs_schema idx dom filter_dec search_term :=
  match type of search_term with
  | ?dom -> BuildIndexSearchTerm ?indexed_attrs  =>
    let SC := constr:(GetNRelSchemaHeading (qschemaSchemas qs_schema) idx) in
    let filter_dec' := eval simpl in filter_dec in
        findGoodTerm_dep SC filter_dec' indexed_attrs (@nil (Attributes SC))
                         makeClause
                         ltac:(fun v fds tail =>
                                 makeTerm_dep dom indexed_attrs SC fds tail
                                              EarlyIndex LastIndex
                                              ltac:(fun tm => pose tm;
                                                    (* unification fails if I don't pose tm first... *)
                                                    unify tm search_term;
                                                    unfold ExtensionalEq, MatchIndexSearchTerm;
                                                    simpl; intros;
                                                    try prove_extensional_eq

                              )) end.

(* Find the name of a schema [schemas] with the same heading as [heading] *)
Ltac find_equivalent_tuple schemas heading k :=
  match schemas with
  | Vector.nil _ => fail
  | Vector.cons _ ?sch' ?n ?schemas' =>
    (let H := fresh in
     unify (rawSchemaHeading sch') heading;
     k (@Fin.F1 n))
      || find_equivalent_tuple schemas' heading
      ltac:(fun i => k (Fin.FS i))
  end.

(* Build pairs of fields + their values. *)
Ltac find_equivalent_search_term_pair build_search_term_dep :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- ExtensionalEq ?f _ ] =>
    match type of f with
    | ilist2 (B := @RawTuple) (Vector.cons _ ?heading _ ?headings) -> bool =>
      makeEvar (ilist2 (B := @RawTuple) headings -> @RawTuple heading -> bool)
               ltac:(fun filter_dec =>
                       let eqv_f_dec := fresh in
                       assert (forall a : ilist2 (B := @RawTuple) (Vector.cons _ heading _ headings),
                                  f a = filter_dec (ilist2_tl a) (ilist2_hd a));
                     [let a := fresh in
                      intro a; let f' := match goal with |- ?f = _ => f end in
                               let f'' :=
                                   match eval pattern (ilist2_tl a), (ilist2_hd a) in f'
                                   with | ?f'' _ _ => f'' end
                                     in let f3 := eval simpl in f'' in
                                            unify f3 filter_dec; reflexivity
                                   | let dom := constr:(ilist2 (B := @RawTuple) headings) in
                                     let schemas := eval simpl in (qschemaSchemas qs_schema) in
                                         find_equivalent_tuple schemas heading
                                                               ltac:(fun idx' =>                                                                            let idx := eval simpl in idx' in
                                                                                                                                                                let idx_search_update_term := eval simpl in (ith3 indices idx) in
                                                                                                                                                                    let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                                                                                                                        let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                                                                                                                            let search_term_type := search_term_type' in
                                                                                                                                                                            makeEvar (dom -> search_term_type)
                                                                                                                                                                                     ltac: (fun search_term =>
                                                                                                                                                                                              let eqv := fresh in
                                                                                                                                                                                              assert (forall (a : ilist2 (B:= @RawTuple) (headings)) (b : @RawTuple heading) ,
                                                                                                                                                                                                         filter_dec a b = search_term_matcher (search_term a) b) as eqv;                                                                   [ build_search_term_dep qs_schema idx dom filter_dec search_term
                                                                                                                                                                                                                                                                                                                                           | match goal with
                                                                                                                                                                                                                                                                                                                                               |- ExtensionalEq ?f ?search_term' =>
                                                                                                                                                                                                                                                                                                                                               match type of f with
                                                                                                                                                                                                                                                                                                                                               | ilist2 (B := @RawTuple) (Vector.cons ?T ?A ?n ?As) -> _ =>
                                                                                                                                                                                                                                                                                                                                                 unify search_term' (fun a : ilist2 (B := @RawTuple) (Vector.cons T A n As) => search_term_matcher (search_term (ilist2_tl a)) (ilist2_hd a))
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
    let n := match type of f with (ilist2 (n := S ?n) _ -> _) => n end in
    get_ithDefault f (@Fin.F1 n)
                   ltac:(fun filter_dec =>
                           let heading :=
                               match type of filter_dec with
                               | @RawTuple ?heading -> bool => constr:(heading)
                               end in
                           let schemas := eval simpl in (qschemaSchemas qs_schema) in
                               find_equivalent_tuple schemas heading
                                                     ltac:(fun idx' =>
                                                             let idx := eval simpl in idx' in
                                                                 let idx_search_update_term := eval simpl in (ith3 indices idx) in
                                                                     let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                                                                         let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                                                                             let search_term_type := search_term_type' in
                                                                             makeEvar (search_term_type)
                                                                                      ltac:(fun search_term =>

                                                                                              let eqv := fresh in
                                                                                              assert (forall a, filter_dec a
                                                                                                                = search_term_matcher search_term a) as eqv;
                                                                                            [ build_search_term qs_schema idx
                                                                                                                filter_dec search_term
                                                                                            | match goal with
                                                                                                |- ExtensionalEq ?f ?search_term' =>
                                                                                                match type of f with
                                                                                                | ?A -> _ =>
                                                                                                  unify search_term' (fun a : A => search_term_matcher search_term (ilist2_hd a))
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

    |- context[l <- CallBagEnumerate ?idx ?r_n;
                List_Query_In (filter (fun a => @?f a && @?filter_rest a)
                                      (Build_single_Tuple_list (snd l))) ?resultComp] =>
    match f with
    | fun a => ?MatchIndexSearchTerm ?st (ilist2_hd a) =>
      let b := fresh in
      pose proof (@refine_Query_For_In_Find_single _ _ _ r_o r_n H idx st resultComp filter_rest) as b;
        simpl in b; setoid_rewrite b; clear b
    end

  | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
    |- context[l <- CallBagEnumerate ?idx ?r_n;
                l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) ?cl;
                List_Query_In (filter (fun a => @?f a && @?filter_rest a)
                                      l') ?resultComp] =>
    match f with
    | fun a => ?MatchIndexSearchTerm ?st (ilist2_hd (ilist2_tl a)) =>
      let b := fresh in
      pose proof (fun foo => @refine_Join_Comp_Lists_filter_search_term_fst _ _ _ r_o r_n H idx _ cl st resultComp foo filter_rest) as b;
        simpl in b; setoid_rewrite b;
        [ clear b
        | match goal with
          | |- context [CallBagEnumerate ?idx' _] =>
            intros; eapply (realizeable_Enumerate (r_o := r_o) (r_n := r_n) idx' H)
          | |- context [CallBagFind ?idx' _ _] =>
            intros; eapply (realizeable_Find (r_o := r_o) (r_n := r_n) idx' H)
          end]
    end

  | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
    |- context[l <- CallBagFind ?idx ?r_n ?st;
                l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l))
                   (fun _ : ilist (@RawTuple) [?heading] =>
                      l <- CallBagEnumerate ?idx' ?r_n;
                    ret (snd l));
                List_Query_In (filter (fun a => @?f a && @?filter_rest a) l') ?resultComp] =>
    match f with
    | fun a => ?MatchIndexSearchTerm (Dep_SearchTerm_Wrapper ?st' (ilist2_hd (ilist2_tl a)))
                (ilist2_hd a) =>
      let b := fresh in
      pose proof (@refine_Join_Comp_Lists_filter_filter_search_term_snd_dep' _ _ _ r_o r_n H idx idx'
                                                                             (fun a => Dep_SearchTerm_Wrapper st' (ilist2_hd a))
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
      try simplify with monad laws;
      repeat setoid_rewrite refine_bind_unit
  end.

Ltac ilist_of_dep_evar n C D B As k :=
  match n with
  | 0 => k (fun (c : C) (d : D c) => inil (B := B c d))
  | S ?n' =>
    makeEvar (forall (c : C) (d : D c), B c d (Vector.hd As))
             ltac:(fun b =>
                     ilist_of_dep_evar n' C D B (Vector.tl As)
                                       ltac:(fun Bs' =>
                                               k (fun (c : C) (d : D c) => icons (b c d) (Bs' c d))))
  end.

Definition Join_Comp_Lists'
           {n} {A : Type} {f : A -> Type} {As : Vector.t A n} {a : A}
           (l : list (ilist2 (B := f) As)) (c : ilist2 (B := f) As -> list (f a))
  := flatten (map
                (fun l' => map (fun fa : f a => icons2 fa l') (c l')) l).

Lemma Join_Comp_Lists_Impl {n} {A : Type} {f : A -> Type} {As : Vector.t A n} {a : A}
  : forall (l : list (ilist2 (B := f) As))
           (c : ilist2 As -> Comp (list (f a)))
           (c' : ilist2 As -> list (f a)),
    (forall a', refine (c a') (ret (c' a')))
    -> refine (Join_Comp_Lists l c) (ret (Join_Comp_Lists' l c')).
Proof.
  induction l; unfold Join_Comp_Lists, Join_Comp_Lists'; simpl; intros.
  - reflexivity.
  - rewrite H; simplify with monad laws.
    setoid_rewrite IHl; eauto; simplify with monad laws.
    reflexivity.
Qed.

Ltac implement_bag_constructors :=
  repeat match goal with
         | |- context[ Pick (fun r_n : @Build_IndexedQueryStructure_Impl_cRep ?qs_schema ?Index ?DelegateReps =>
                               @Build_IndexedQueryStructure_Impl_AbsR
                                 _ _ ?DelegateReps ?DelegateImpls
                                 ?ValidImpls ?r_o r_n)] =>
           refine pick val (@Initialize_IndexedQueryStructureImpls' qs_schema Index DelegateReps DelegateImpls);
             [ higher_order_reflexivity |
               unfold Build_IndexedQueryStructure_Impl_AbsR;
                 eapply Lookup_Iterate_Dep_Type; simpl; intuition ]
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
                         {|bindex := ridx |} cidx d) as [r_o' [refines_r_o' AbsR_r_o'] ];
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
    makeEvar (ilist2 (B := f) As -> list (f a))
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
                   ] ]; cbv beta; simpl in * )
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
  | [
    |-  refine (Bind {r_n' | @Build_IndexedQueryStructure_Impl_AbsR
                               ?qs_schema
                               ?Index ?DelegateReps ?DelegateImpls
                               ?ValidImpls ?r_o r_n'} _) _]
    =>  etransitivity;
      [ apply refine_bind;
        [apply refine_pick_val; eauto;
         repeat match goal with
                  |- @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index _ _ _ _ _ =>
                  eapply (@Update_Build_IndexedQueryStructure_Impl_AbsR qs_schema Index);
                    eauto
                end
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
                                                       (GetUnConstrRelation ?r_o ?TableID))) r_n'}] ]
           => setoid_rewrite (@refine_BagADT_QSInsert _ _ r_o r_n H TableID tup);
             simplify with monad laws; reflexivity

         | [ H : DelegateToBag_AbsR ?r_o ?r_n

             |- context[idx <- {idx | UnConstrFreshIdx (GetUnConstrRelation ?r_o ?TableID) idx};
                         {r_n' |
                          DelegateToBag_AbsR
                            (UpdateUnConstrRelation ?r_o ?TableID
                                                    (EnsembleInsert
                                                       {| elementIndex := idx; indexedElement := ?tup |}
                                                       (GetUnConstrRelation ?r_o ?TableID))) r_n'} ] ]
           => apply refine_bind;
             [apply (@refine_BagADT_QSInsert _ _ r_o r_n H TableID tup)
             | intro; higher_order_reflexivity ]
         | |- _ => setoid_rewrite <- refineEquiv_bind_bind
         end

  | (* Refine the else branch *)
  repeat match goal with
         | [ H : DelegateToBag_AbsR ?r_o ?r_n
             |- context[{idx | UnConstrFreshIdx (GetUnConstrRelation ?r_o ?TableID) idx} >>
                                                                                         {r_n' | DelegateToBag_AbsR ?r_o r_n'}] ]
           => let H' := fresh in
              pose proof H as H';
                destruct H' as [_ H'];
                let l := fresh in
                let bnd := fresh in
                let fresh_bnd := fresh in
                destruct (H' TableID) as [l [ [bnd fresh_bnd] _] ];
                  refine pick val bnd; eauto;
                  setoid_rewrite refineEquiv_bind_unit;
                  refine pick val r_n; eauto;
                  setoid_rewrite refineEquiv_bind_unit;
                  reflexivity
         | |- _ => setoid_rewrite <- refineEquiv_bind_bind
         end
  ].

Ltac remove_spurious_Dep_Type_BoundedIndex_nth_eq := fail.
(*  match goal with
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
  end. *)

Lemma Implement_Bound_Bag_Call' A
  : forall qs_schema Index DelegateReps DelegateImpls ValidImpls
           r_o r_n ridx midx,
    @Build_IndexedQueryStructure_Impl_AbsR
      qs_schema Index DelegateReps DelegateImpls ValidImpls r_o r_n
    -> Lift_Method2P
         (fst (MethodDomCod
                 (BagSig RawTuple (BagSearchTermType (ith3 Index ridx))
                         (BagUpdateTermType (ith3 Index ridx))) midx))
         (snd (MethodDomCod
                 (BagSig RawTuple (BagSearchTermType (ith3 Index ridx))
                         (BagUpdateTermType (ith3 Index ridx))) midx))
         (fun cod m m' =>
            forall (k : _ -> Comp A) k',
              (forall r_n' r_o' c,
                  (AbsR (ValidImpls ridx)) r_o' r_n'
                  -> refine (k (r_o', c)) (k' r_n' c))
              -> refine (l <- m;
                         k l)
                        (k' (fst m') (snd m')))
         (fun m m' =>
            forall (k : _ -> Comp A) k',
              (forall r_n' r_o',
                  (AbsR (ValidImpls ridx)) r_o' r_n'
                  -> refine (k r_o') (k' r_n'))
              -> refine (l <- m;
                         k l)
                        (k' m'))
         (CallBagMethod (BagIndexKeys := Index) ridx midx r_o)
         (CallBagImplMethod DelegateReps DelegateImpls midx r_n).
Proof.
  simpl; intros.
  generalize (@refine_BagImplMethods qs_schema Index DelegateReps DelegateImpls ValidImpls r_o r_n ridx H midx).
  simpl.
  eapply (fun P H => Lookup_Iterate_Dep_Type P H midx).
  simpl in *; intuition.
  - destruct (H0 t) as [r_o' [refines_r_o' AbsR_r_o'] ].
    rewrite refines_r_o'; simplify with monad laws.
    eapply H1; eauto.
  - destruct (H0) as [r_o' [refines_r_o' AbsR_r_o'] ].
    rewrite refines_r_o'; simplify with monad laws.
    eapply H1; eauto.
  - destruct (H0 t) as [r_o' [refines_r_o' AbsR_r_o'] ].
    rewrite refines_r_o'; simplify with monad laws.
    eapply H1; eauto.
  - destruct (H0 t) as [r_o' [refines_r_o' AbsR_r_o'] ].
    rewrite refines_r_o'; simplify with monad laws.
    eapply H1; eauto.
  - destruct (H0 t) as [r_o' [refines_r_o' AbsR_r_o'] ].
    rewrite refines_r_o'; simplify with monad laws.
    eapply H1; eauto.
  - destruct (H0 t t0) as [r_o' [refines_r_o' AbsR_r_o'] ].
    rewrite refines_r_o'; simplify with monad laws.
    eapply H1; eauto.
Qed.

Ltac  Implement_Bound_Bag_Call :=
  let r_o' := fresh "r_o'" in
  let AbsR_r_o' := fresh "AbsR_r_o'" in
  let refines_r_o' := fresh "refines_r_o'" in
  match goal with
  | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                               ?ValidImpls _ _
    |- refine (Bind (CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?arg1 ?arg2) ?k) _ =>
    pose proof (fun r_n H => @Implement_Bound_Bag_Call' _ qs_schema Index DelegateReps DelegateImpls ValidImpls r_o r_n ridx midx H arg1 arg2 k) as refines_r_o'
  | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                               ?ValidImpls _ _
    |- refine (Bind (CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o ?arg) ?k) _ =>
    pose proof (fun r_n H => @Implement_Bound_Bag_Call' _ qs_schema Index DelegateReps DelegateImpls ValidImpls r_o r_n ridx midx H arg k) as refines_r_o'
  | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                               ?ValidImpls _ _
    |- refine (Bind (CallBagMethod (BagIndexKeys := ?Index') ?ridx ?midx ?r_o) ?k) _ =>
    pose proof (fun r_n H => @Implement_Bound_Bag_Call' _ qs_schema Index DelegateReps DelegateImpls ValidImpls r_o r_n ridx midx H k) as refines_r_o'
  end;
    simpl in refines_r_o';
    fold_string_hyps_in refines_r_o'; fold_heading_hyps_in refines_r_o';
    etransitivity;
    [ eapply refines_r_o'; cbv beta; simpl in *; intros; eauto;
      repeat match goal with
               |- @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index _ _ _ _ _ =>
               eapply (@Update_Build_IndexedQueryStructure_Impl_AbsR qs_schema Index);
                 eauto
             end
    | ].

Definition flatten_CompList'
           (A B : Type)
           (c : list (B -> Comp (B * list A)))
           (b : B)
  : Comp (B * list A) :=
  fold_right (fun a b =>
                l <- b;
              l' <- a (fst l);
              ret (fst l', app (snd l') (snd l)))
             (ret (b, [ ]))  c.

Definition Join_Comp_Lists_prod
           {n}
           {A B : Type}
           {f : A -> Type}
           {As : Vector.t A n}
           {a : A}
           (b : B)
           (l' : list (ilist2 (B := f) As))
           (c : B -> ilist2 (B := f) As -> Comp (B * list (f a)))
  : Comp (B * list (ilist2 (B := f) (Vector.cons _ a _ As))) :=
  flatten_CompList' (map (fun a' b' => l <- c b' a'; (ret (fst l, map (fun fa : f a => icons2 fa a') (snd l)))) l') b.

Lemma Join_Comp_Lists_eq qs_schema Index
  : forall idx n h f r_n l,
    refine (Join_Comp_Lists (n := n) l
                            (fun a0 : ilist2 h =>
                               u <- @CallBagMethod qs_schema Index idx BagFind
                                 r_n
                                 (f a0);
                             ret (snd u)))
           (u <- Join_Comp_Lists_prod r_n l
              (fun r_n (a0 : ilist2 h) =>
                 @CallBagFind qs_schema Index idx
                              r_n
                              (f a0));
            ret (snd u)) .
Proof.
  intros; induction l; unfold Join_Comp_Lists, Join_Comp_Lists_prod; simpl.
  - intros v CompV.
    computes_to_inv; subst.
    computes_to_econstructor.
  -
    setoid_rewrite IHl.
    repeat setoid_rewrite refineEquiv_bind_bind.
    Local Opaque CallBagMethod.
    simplify with monad laws.
    intros v Comp_v; computes_to_inv; subst.
    unfold CallBagFind in Comp_v'; computes_to_inv; subst; simpl.
    repeat computes_to_econstructor; eauto.
    assert (r_n = fst v0); subst; eauto.
    generalize v0 Comp_v; clear.
    induction l.
    + simpl; intros; computes_to_inv; subst.
      reflexivity.
    + simpl; intros; computes_to_inv; subst.
      apply IHl in Comp_v; simpl.
      unfold CallBagFind in Comp_v'; computes_to_inv; subst.
      simpl.
      apply CallBagFind_fst in Comp_v'; eauto.
Qed.

Lemma Join_Comp_Lists_eq' qs_schema Index
  : forall idx n h f r_n l a,
    computes_to (Join_Comp_Lists_prod (n := n) r_n l
                                      (fun r_n (a0 : ilist2 h) =>
                                         @CallBagFind qs_schema Index idx
                                                      r_n
                                                      (f a0))) a
    -> r_n = (fst a).
Proof.
  induction l; unfold Join_Comp_Lists, Join_Comp_Lists_prod; simpl; intros.
  - computes_to_inv; simpl; subst; reflexivity.
  - simpl; intros; computes_to_inv; subst.
    apply IHl in H; simpl.
    unfold CallBagFind in H'; computes_to_inv; subst.
    simpl; eapply CallBagFind_fst; eauto.
Qed.


Definition Join_Comp_Lists_prod'
           {n} {A B : Type} {f : A -> Type} {As : Vector.t A n} {a : A}
           (b : B) (l : list (ilist2 (B := f) As)) (c : B -> ilist2 (B := f) As -> B * list (f a)) : B * list (ilist2 (B := f) (Vector.cons _ a _ As)) :=
  fold_right (fun a' b' => let l'' := c (fst b') a' in
                           (fst l'',
                            app
                              (flatten (map
                                          (fun l' => map (fun fa : f a => icons2 fa l') (snd l'')) l)) (snd b')

             )) (b, [ ]) l.

Lemma ReturnComputes_eq {A}
  : forall (a a' : A),
    a = a' -> computes_to (ret a) a'.
Proof.
  intros; subst; computes_to_econstructor.
Qed.

Lemma Join_Comp_Lists_Impl''
      qs_schema
      (n' := numRawQSschemaSchemas qs_schema ) (schemas := qschemaSchemas qs_schema)
      n
      (Index : ilist3 schemas)
      (DelegateReps : Fin.t n' -> Type)
      (DelegateImpls : forall idx : Fin.t n',
          ComputationalADT.pcADT
            (Build_IndexedQueryStructure_Impl_Sigs Index idx)
            (DelegateReps idx))
      ValidImpls
      heading
      (idx : Fin.t n')
  : forall (r_n : IndexedQueryStructure qs_schema Index) l f' r_n',
    Build_IndexedQueryStructure_Impl_AbsR DelegateReps DelegateImpls
                                          ValidImpls r_n r_n'
    -> exists r_n'', computes_to (@Join_Comp_Lists_prod n _ _ (@RawTuple) heading _ r_n l
                                                        (fun r_n b' =>
                                                           br <- CallBagMethod idx BagFind r_n
                                                              (f' b');
                                                         ret
                                                           (UpdateIndexedRelation qs_schema
                                                                                  Index r_n
                                                                                  idx (fst br), snd br)))
                                 (r_n'', snd (Join_Comp_Lists_prod' (As := heading) r_n' l (fun r_n b' =>
                                                                                              let br := @CallBagImplMethod _ _ Index DelegateReps DelegateImpls _ BagFind r_n
                                                                                                                           (f' b') in

                                                                                              (Update_Build_IndexedQueryStructure_Impl_cRep qs_schema Index DelegateReps r_n
                                                                                                                                            idx (fst br), snd br))))
                     /\        Build_IndexedQueryStructure_Impl_AbsR DelegateReps DelegateImpls
                                                                     ValidImpls r_n''
                                                                     (fst (Join_Comp_Lists_prod' (As := heading) r_n' l (fun r_n b' =>
                                                                                                                           let br := @CallBagImplMethod _ _ Index DelegateReps DelegateImpls _ BagFind r_n
                                                                                                                                                        (f' b') in

                                                                                                                           (Update_Build_IndexedQueryStructure_Impl_cRep qs_schema Index DelegateReps r_n
                                                                                                                                                                         idx (fst br), snd br)))).
Proof.
  induction l; unfold Join_Comp_Lists_prod, Join_Comp_Lists_prod'; simpl; intros.
  - eexists; simpl; intuition eauto.
  - destruct (IHl f' r_n' H) as [r_n'' [? ?] ].
    destruct (@refine_BagImplMethods _ _ DelegateReps DelegateImpls ValidImpls _ _ idx H1 BagFind
                                     (f' a)) as [v' [ref AbsR] ].
    pose proof (ref _ (ReturnComputes _)).
    eexists; intuition eauto.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    simpl.
    eapply ReturnComputes_eq; f_equal.
    progress f_equal.
    unfold Join_Comp_Lists_prod'.
Admitted.

Lemma Join_Comp_Lists_Impl'
      {B}
      qs_schema
      (n' := numRawQSschemaSchemas qs_schema ) (schemas := qschemaSchemas qs_schema)
      n
      (Index : ilist3 schemas)
      (DelegateReps : Fin.t n' -> Type)
      (DelegateImpls : forall idx : Fin.t n',
          ComputationalADT.pcADT
            (Build_IndexedQueryStructure_Impl_Sigs Index idx)
            (DelegateReps idx))
      ValidImpls
      heading
      (idx : Fin.t n')
  : forall (r_n : IndexedQueryStructure qs_schema Index) l f' (f'' : _ -> B) r_n',
    Build_IndexedQueryStructure_Impl_AbsR DelegateReps DelegateImpls
                                          ValidImpls r_n r_n'
    -> refine (x <- @Join_Comp_Lists_prod n _ _ (@RawTuple) heading _ r_n l
                 (fun r_n b' =>
                    br <- CallBagMethod idx BagFind r_n
                       (f' b');
                  ret
                    (UpdateIndexedRelation qs_schema
                                           Index r_n
                                           idx (fst br), snd br));
               r_n'0 <- {r_n0 | Build_IndexedQueryStructure_Impl_AbsR DelegateReps
                                                                      DelegateImpls ValidImpls (fst x) r_n0};
               ret (r_n'0, f'' (snd x)))

              (let res := (Join_Comp_Lists_prod' (As := heading) r_n' l (fun r_n b' =>
                                                                           let br := @CallBagImplMethod _ _ Index DelegateReps DelegateImpls _ BagFind r_n
                                                                                                        (f' b') in

                                                                           (Update_Build_IndexedQueryStructure_Impl_cRep qs_schema Index DelegateReps r_n
                                                                                                                         idx (fst br), snd br))) in ret (fst res, f'' (snd res) )).
Proof.
  intros * AbsR v Comp_v.
  computes_to_inv; subst.
  destruct (@Join_Comp_Lists_Impl'' qs_schema n Index DelegateReps DelegateImpls ValidImpls heading idx r_n l f' r_n' AbsR) as [r_n'' [? AbsR_r_n''] ].
  computes_to_econstructor; eauto.
Qed.

Ltac Implement_Bound_Join_Comp_Lists' :=
  match goal with
  | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                               ?ValidImpls ?r_o ?r_n
    |- refine (Bind (@Join_Comp_Lists_prod _ _ ?B ?f ?As ?a ?b ?l
                                           (fun r_n b' =>
                                              br <- CallBagMethod ?idx BagFind r_n
                                                 (@?f' b');
                                            ret
                                              (UpdateIndexedRelation ?qs_schema
                                                                     ?Index r_n
                                                                     ?idx (fst br), snd br))
                    ) (fun x1 => r_n' <- _; ret (r_n', @?f'' x1 ))) _ =>
    match type of f'' with
      _ * ?B -> ?C =>
      makeEvar (B -> C)
               ltac:(fun g =>
                       assert (forall x', g (snd x') = f'' x') by
                         (let x' := fresh in intros x'; destruct x'; simpl; reflexivity);
                     setoid_rewrite (@Join_Comp_Lists_Impl' _ qs_schema _ Index DelegateReps DelegateImpls ValidImpls _ idx b l f' g);
                     eauto using (@Update_Build_IndexedQueryStructure_Impl_AbsR qs_schema Index DelegateReps DelegateImpls ValidImpls))

    end
  end.

(* PRE-ROS Ltac implement_bag_methods :=
  etransitivity;
  [ repeat (first [
                simpl; simplify with monad laws
              | remove_spurious_Dep_Type_BoundedIndex_nth_eq
              | Implement_If_Then_Else
              | Implement_If_Opt_Then_Else
              | Implement_Bound_Bag_Call
              | Implement_Bound_Join_Comp_Lists
              | Implement_Bound_Join_Comp_Lists'
              | Implement_AbsR_Relation
              | match goal with
                  |- context[CallBagImplMethod _ _ _ _ _] =>
                  unfold CallBagImplMethod; cbv beta; simpl
                end
              | higher_order_reflexivity ]; simpl) |];
  (* Clean up any leftover CallBagImplMethods *)
  repeat (cbv beta; simpl;
          match goal with
            |- appcontext[CallBagImplMethod] =>
            unfold CallBagImplMethod; cbv beta; simpl;
            try remove_spurious_Dep_Type_BoundedIndex_nth_eq
          end);
  higher_order_reflexivity. *)

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

Ltac implement_In_opt' :=
  match goal with
  (* Implement a List_Query_In of a list [l] applied to a UnConstrQuery_In [idx]
        by enumerating [idx] with a method call and joining the result with [l] *)
  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (List_Query_In ?l (fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b) )) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (refine_Filtered_Join_Query_In_Enumerate' H (idx := idx) f (l := l)) in
            apply H'
      |  apply refine_under_bind; intros; implement_In_opt' ]

  (* Implement a 'naked' UnConstrQuery_In as a call to enumerate *)
  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (refine_Filtered_Query_In_Enumerate H (idx := idx) f) in
            apply H'
      | apply refine_under_bind; intros; implement_In_opt' ]

  (* Convert all Where clauses to filters.*)
  | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
     |- refine (List_Query_In ?b (fun b : ?QueryT => Where (@?P b) (@?resultComp b))) _ ] =>
    etransitivity;
      [ let H' := eval simpl in (@refine_List_Query_In_Where QueryT _ b P resultComp _) in
            apply H'
      | implement_In_opt'; implement_In_opt' ]

  (* Finish if no progress can be made. This may miss some
       filters if In and Where Clauses are mixed. *)
  | _ =>
    repeat rewrite <- filter_and;
      repeat setoid_rewrite andb_true_r;
      higher_order_reflexivity
  end.

Ltac implement_In_opt :=
  etransitivity;
  [ implement_In_opt' | ]; cbv beta; simpl.

Ltac implement_Pick_DelegateToBag_AbsR :=
  match goal with
    [ H : DelegateToBag_AbsR ?r_o ?r_n
      |- context [ {r_n' |  DelegateToBag_AbsR ?r_o r_n'} ] ] =>
    setoid_rewrite (@refine_Pick_DelegateToBag_AbsR _ _ _ _ H)
  end.

Ltac Focused_refine_TopMost_Query :=
  match goal with
  | |- refine (Bind (Count (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_Count ResultT body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (MaxN (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_MaxN body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (SumN (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_SumN body') at 1;
                       clear refine_body' ] )
  | |- refine (Bind (MaxZ (@Query_For ?ResultT ?body)) ?k) _ =>

    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_MaxZ body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (SumZ (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_SumZ body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (Max (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_Max body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (Sum (@Query_For ?ResultT ?body)) ?k) _ =>
    makeEvar (Comp (list ResultT))
             ltac:(fun body' =>
                     let refine_body' := fresh in
                     assert (refine body body') as refine_body';
                   [ |
                     setoid_rewrite refine_body';
                       setoid_rewrite (@refine_For_List ResultT body') at 1;
                       setoid_rewrite (@refine_Sum body') at 1;
                       clear refine_body' ] )

  | |- refine (Bind (@Query_For ?ResultT ?body) ?k) _ =>
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
  assert (forall a : ilist2 (Vector.cons _ a _ As), f a = g (ilist2_tl a)) as H;
    [let a := fresh in
     intro a;
       match goal with
         |- ?f = ?g (ilist2_tl a)=>
         let f' :=  match eval pattern (ilist2_tl a) in f
                    with ?f' (ilist2_tl a) => eval simpl in f' end in
                 unify f' g
             end; reflexivity
           | clear H].

Ltac Realize_CallBagMethods :=
  match goal with
  | H : @DelegateToBag_AbsR ?qs_schema ?BagIndexKeys ?r_o ?r_n
    |- context [CallBagEnumerate ?idx' _] =>
    generalize H; clear;
    intros; eapply (@realizeable_Enumerate qs_schema BagIndexKeys r_n r_o idx' H)

  | H : @DelegateToBag_AbsR ?qs_schema ?BagIndexKeys ?r_o ?r_n
    |- context [CallBagFind ?idx' _ ?st] =>
    generalize H; clear;
    intros; eapply (@realizeable_Find qs_schema BagIndexKeys r_n r_o idx' st H)
  end.

Lemma refine_merge_bind (A B C : Type) :
  forall (a a' : Comp A) (b b' : A -> Comp B) (k : B -> Comp C),
    refine (x <- a; b x) (x <- a'; b' x)
    -> refine (x <- a; y <- b x; k y)
              (x <- a'; y <- b' x; k y).
Proof.
  intros.
  rewrite <- refineEquiv_bind_bind, H, refineEquiv_bind_bind.
  reflexivity.
Qed.

Ltac distribute_filters_to_joins' :=
  match goal with
    |- refine
         (l <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond; _)
         _ =>
    etransitivity; (* Recursively drill under the binds *)
      [ apply refine_under_bind; intros; cbv beta; simpl; distribute_filters_to_joins'
      |   cbv beta; simpl;
          match goal with
            |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                       l'' <- Join_Filtered_Comp_Lists
                           (filter ?f l') ?l2' ?cond2;
                       @?k l' l'')
                      _  =>  eapply (refine_merge_bind (fun l' =>
                                                          Join_Filtered_Comp_Lists
                                                            (filter f l') l2' cond2)
                                                       (a' := Join_Filtered_Comp_Lists _ _ _)
                                                       (fun l' =>
                                                          Join_Filtered_Comp_Lists
                                                            l' l2' cond2));
              repeat match goal with
                       |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                  Join_Filtered_Comp_Lists
                                    (filter (fun a : ilist2 (Vector.cons _ ?heading1 _ (Vector.cons _ ?heading2 _ ?headings)) =>
                                               @?f a && @?g a) l') ?l2' ?cond2)
                                 _ => first (* No test case for this branch *)
                                        [ makeEvar (ilist2 (B := @RawTuple) headings -> bool)
                                                   ltac:(fun f' =>
                                                           find_equiv_tl heading1 headings f f';
                                                         let Comp_l2 := fresh in
                                                         assert
                                                           (forall a : ilist2 (B := @RawTuple) headings,
                                                               exists v : list (@RawTuple heading1),
                                                                 refine (l2 a) (ret v)) as Comp_l2
                                                             by Realize_CallBagMethods;
                                                         etransitivity;
                                                         [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_hd_andb _ heading1 heading2 headings f' g l2 l2' cond1 cond2 Comp_l2 l1) | ])
                                        | etransitivity;
                                          [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_tail_andb _ heading1 heading2 headings f g l2 l2' cond1 cond2 l1)
                                          | ]
                                        ]
                     | |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                  Join_Filtered_Comp_Lists (a := ?heading2)
                                                           (@filter (ilist2 (Vector.cons _ ?heading1 _ ?headings)) ?f l') ?l2' ?cond2) _
                       =>   first
                              [ makeEvar (ilist2 (B := @RawTuple) headings -> bool) (* No test case for this branch either *)
                                         ltac:(fun f' =>
                                                 find_equiv_tl heading1 headings f f';
                                               let Comp_l2 := fresh in
                                               assert
                                                 (forall a : ilist2 (B := @RawTuple) headings,
                                                     exists v : list (@RawTuple heading1),
                                                       refine (l2 a) (ret v)) as Comp_l2
                                                   by Realize_CallBagMethods;
                                               etransitivity;
                                               [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_hd _ heading1 heading2 headings f' l2 l2' cond1 cond2 Comp_l2 l1)
                                               | ])
                              | etransitivity;
                                [ apply (@refine_Join_Join_Filtered_Comp_Lists_filter_tail _ heading1 heading2 headings f l2 l2' cond1 cond2 l1) | ] ]
                     (* If there's no filter on the first list, we're done. *)
                     | |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond1;
                                  Join_Filtered_Comp_Lists l' ?l2' ?cond2)
                                 _ => reflexivity
                     end

          (* The bottom case where we've recursed under all the bound Joins. *)
          | |- refine (l' <- Join_Filtered_Comp_Lists _ _ _;
                       List_Query_In _ _)
                      _ =>
            match goal with
              |- refine (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                         List_Query_In (ResultT := ?ResultT)
                                       (filter (fun a : ilist2 (Vector.cons _ ?heading _ ?headings) =>
                                                  @?f a && @?g a) l') ?resultComp)
                        _ =>
              first [makeEvar (ilist2 (B := @RawTuple) headings -> bool)
                              ltac:(fun f' => find_equiv_tl heading headings f f';
                                    let Comp_l2 := fresh in
                                    assert
                                      (forall a : ilist2 (B := @RawTuple) headings,
                                          exists v : list (@RawTuple heading),
                                            refine (l2 a) (ret v)) as Comp_l2
                                        by Realize_CallBagMethods;
                                    etransitivity;
                                    [apply (@refine_Join_Filtered_Comp_Lists_filter_hd_andb _ heading headings f' g ResultT resultComp l2 cond' Comp_l2 l1)
                                    | ])
                    | etransitivity;
                      [apply (@refine_Join_Filtered_Comp_Lists_filter_tail_andb _ heading headings f g ResultT resultComp l2 ) | ] ]

            | |- refine
                   (l' <- Join_Filtered_Comp_Lists ?l1 ?l2 ?cond';
                    List_Query_In (ResultT := ?ResultT)
                                  (@filter (ilist2 (Vector.cons _ ?heading _ ?headings)) ?f l') ?resultComp)
                   _ =>
              first [ makeEvar (ilist2 (B := @RawTuple) headings -> bool)
                               ltac:(fun f' => find_equiv_tl heading headings f f';
                                     let Comp_l2 := fresh in
                                     assert
                                       (forall a : ilist2 (B := @RawTuple) headings,
                                           exists v : list (@RawTuple heading),
                                             refine (l2 a) (ret v)) as Comp_l2 by
                                           Realize_CallBagMethods;
                                     apply (@refine_Join_Filtered_Comp_Lists_filter_hd _ heading headings f' ResultT resultComp l2 Comp_l2 l1))
                    | apply (@refine_Join_Filtered_Comp_Lists_filter_tail _ heading headings f ResultT resultComp l2 cond' l1) ]

            end
          | |- _ => higher_order_reflexivity
          end
      ]
  | |- _ => higher_order_reflexivity

  end.

Ltac distribute_filters_to_joins :=
  etransitivity;
  [ repeat (progress distribute_filters_to_joins') | cbv beta; simpl ].

Ltac convert_filter_search_term_to_find :=
  match goal with
  | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
    |- refine (l <- Join_Filtered_Comp_Lists (a := ?heading) (As := ?headings) ?l1
                 (fun _ => l' <- CallBagEnumerate ?idx ?r_n;
                  ret (snd l')) ?f;
               _) _ =>
    match f with
    (* Resolve the unfiltered case *)
    | fun a => true =>
      unfold Join_Filtered_Comp_Lists at 1; setoid_rewrite filter_true
    (* Try non-dependent search term first *)
    | fun a => (?MatchIndexSearchTerm ?st (ilist2_hd a)) && true =>
      let r := fresh in
      pose proof (@refine_Join_Comp_Lists_To_Find _ _ _ r_o r_n H _ l1 idx st) as r;
        simpl in r; rewrite r; clear r
    (* Then do dependent search term  *)
    | fun a => (?MatchIndexSearchTerm (@?st a) (ilist2_hd a)) && true =>
      let stT := type of st in
      match stT with _ -> ?stT =>
                     makeEvar (ilist2 (B := @RawTuple) headings -> stT)
                              ltac:(fun st_dep =>
                                      let eqv := fresh in
                                      let a := fresh in
                                      assert (forall (a : ilist2 (Vector.cons _ _ _ _)),
                                                 st a = st_dep (ilist2_tl a) ) as eqv;
                                    [intro a; simpl;
                                     match goal with
                                       |- ?st' = _ =>

                                       let st'' := eval pattern (ilist2_tl a) in st' in                                                     match st'' with | ?f (ilist2_tl a) =>
                                                                                                                                                              let f' := eval simpl in f in unify f' st_dep end
                                     end; simpl; reflexivity |
                                     let r := fresh in
                                     pose proof (refine_Join_Comp_Lists_To_Find_dep
                                                   H l1 idx
                                                   st_dep) as r;
                                       simpl in r;
                                       fold_string_hyps_in r; fold_heading_hyps_in r;
                                       rewrite r; clear r eqv
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
          pose_string_hyps; pose_heading_hyps;
          apply refine_under_bind; intros);
  apply List_Query_In_Return.

Ltac implement_Query' k k_dep:=
  Focused_refine_Query;
  [ (* Step 1: Implement [In / Where Combinations] by enumerating and joining. *)
    implement_In_opt;
    (* Step 2: Move filters to the outermost [Join_Comp_Lists] to which *)
    (* they can be applied. *)
    repeat progress distribute_filters_to_joins;
    (* Step 3: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep
  |
  ]; pose_string_hyps; pose_heading_hyps.

Ltac implement_Query CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  implement_Query'
    ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex)
           ltac:(find_simple_search_term_dep makeClause_dep EarlyIndex_dep LastIndex_dep).


Ltac implement_nested_Query
         CreateTerm EarlyIndex LastIndex
         makeClause_dep EarlyIndex_dep LastIndex_dep :=
    Focused_refine_Query;
      [ match goal with
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- refine (UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f) _ ] =>
      etransitivity;
        [ let H' := (eval simpl in (@refine_UnConstrQuery_In resultT _ r_o idx)) in
          eapply H'; intro;
          implement_Query CreateTerm EarlyIndex LastIndex
                          makeClause_dep EarlyIndex_dep LastIndex_dep;
          simpl; repeat first [setoid_rewrite refine_bind_unit
                              | setoid_rewrite refine_bind_bind ];
          simplify with monad laws; finish honing
        | let H' := eval simpl in (refine_Filtered_Query_In_Enumerate (ResultT := resultT) H (idx := idx)) in
              apply H']

    end | ].

Ltac Implement_Nested_Query_In :=
  let r_o' := fresh "r_o'" in
  let AbsR_r_o' := fresh "AbsR_r_o'" in
  let refines_r_o' := fresh "refines_r_o'" in
  match goal with
  | H : @Build_IndexedQueryStructure_Impl_AbsR ?qs_schema ?Index ?DelegateReps ?DelegateImpls
                                               ?ValidImpls _ _
    |- refine (Bind (List_Query_In ?l ?f) ?k) _ =>
    setoid_rewrite (@List_Query_In_Return' _ _ _ f _ l);
          [ | intros; repeat Implement_Bound_Bag_Call; finish honing];
          setoid_rewrite List_Query_In_Return
  end.

Ltac implement_bag_methods :=
  etransitivity;
  [ repeat (first [
                simpl; simplify with monad laws
              | remove_spurious_Dep_Type_BoundedIndex_nth_eq
              | Implement_If_Then_Else
              | Implement_If_Opt_Then_Else
              | Implement_Bound_Bag_Call
              | Implement_Bound_Join_Comp_Lists
              | Implement_Bound_Join_Comp_Lists'
              | Implement_AbsR_Relation
              | match goal with
                  |- context[CallBagImplMethod _ _ _ _ _] =>
                  unfold CallBagImplMethod; cbv beta; simpl
                end
              | Implement_Nested_Query_In
              | higher_order_reflexivity ]; simpl) |];
  (* Clean up any leftover CallBagImplMethods *)
  repeat (cbv beta; simpl;
          match goal with
                |- appcontext[CallBagImplMethod] =>
                unfold CallBagImplMethod; cbv beta; simpl;
                try remove_spurious_Dep_Type_BoundedIndex_nth_eq
          end);
  higher_order_reflexivity.

Ltac implement_TopMost_Query' k k_dep:=
  Focused_refine_TopMost_Query;
  [ (* Step 1: Implement [In / Where Combinations] by enumerating and joining. *)
    implement_In_opt;
    (* Step 2: Move filters to the outermost [Join_Comp_Lists] to which *)
    (* they can be applied. *)
    repeat progress distribute_filters_to_joins;
    (* Step 3: Convert filter function on topmost [Join_Filtered_Comp_Lists] to an
               equivalent search term matching function.  *)
    implement_filters_with_find k k_dep
  |
  ]; pose_string_hyps; pose_heading_hyps.

Ltac implement_TopMost_Query CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  implement_TopMost_Query'
    ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex)
           ltac:(find_simple_search_term_dep makeClause_dep EarlyIndex_dep LastIndex_dep).

Ltac FullySharpenQueryStructure qs_schema Index :=
  let DelegateSigs := constr:(@Build_IndexedQueryStructure_Impl_Sigs _ (qschemaSchemas qs_schema) Index) in
  let DelegateSpecs := constr:(@Build_IndexedQueryStructure_Impl_Specs _ (qschemaSchemas qs_schema) Index) in
  let cRep' := constr:(@Build_IndexedQueryStructure_Impl_cRep _ (qschemaSchemas qs_schema) Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let ValidRefinements := fresh in
  let FullySharpenedImpl := fresh "FullySharpenedImpl" in
  match goal with
    |- @FullySharpenedUnderDelegates _ (@BuildADT ?Rep ?n ?n' ?consSigs ?methSigs ?consDefs ?methDefs) _ =>
    ilist_of_dep_evar n
                      (Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                      (fun D =>
                         forall idx,
                           ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                      (fun
                          (DelegateReps : Fin.t _ -> Type)
                          (DelegateImpls : forall idx,
                              ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                          (Sig : consSig) =>
                          ComputationalADT.cConstructorType (cRep' DelegateReps)
                                                            (consDom Sig))
                      consSigs
                      ltac:(fun cCons =>
                              ilist_of_dep_evar n'
                                                (Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                (fun D =>
                                                   forall idx,
                                                     ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                                                (fun (DelegateReps : Fin.t _ -> Type)
                                                     (DelegateImpls : forall idx,
                                                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                     (Sig : methSig) =>
                                                   ComputationalADT.cMethodType (cRep' DelegateReps)
                                                                                (methDom Sig) (methCod Sig))
                                                methSigs
                                                ltac:(fun cMeths =>
                                                        assert
                                                          ((forall
                                                               (DelegateReps : Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                               (DelegateImpls : forall idx,
                                                                   ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                               (ValidImpls
                                                                : forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
                                                                   refineADT (DelegateSpecs idx)
                                                                             (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                                               Iterate_Dep_Type_BoundedIndex
                                                                 (fun idx =>
                                                                    @refineConstructor _
                                                                                       (cRep' DelegateReps) (cAbsR' _ _ ValidImpls)
                                                                                       (consDom (Vector.nth consSigs idx))
                                                                                       (getConsDef consDefs idx)
                                                                                       (ComputationalADT.LiftcConstructor _ _ (ith  (cCons DelegateReps DelegateImpls) idx))))
                                                           * (forall
                                                                 (DelegateReps : Fin.t (numRawQSschemaSchemas qs_schema) -> Type)
                                                                 (DelegateImpls : forall idx,
                                                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                                                 (ValidImpls
                                                                  : forall idx : Fin.t (numRawQSschemaSchemas qs_schema),
                                                                     refineADT (DelegateSpecs idx)
                                                                               (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                                                 Iterate_Dep_Type_BoundedIndex
                                                                   (fun idx =>
                                                                      @refineMethod
                                                                        _ (cRep' DelegateReps)
                                                                        (cAbsR' _ _ ValidImpls)
                                                                        (methDom (Vector.nth methSigs idx))
                                                                        (methCod (Vector.nth methSigs idx))
                                                                        (getMethDef methDefs idx)
                                                                        (ComputationalADT.LiftcMethod (ith (cMeths DelegateReps DelegateImpls) idx))))) as ValidRefinements;
                                                      [ |
                                                        pose proof (@Notation_Friendly_SharpenFully'
                                                                      _
                                                                      _
                                                                      _
                                                                      consSigs
                                                                      methSigs
                                                                      consDefs
                                                                      methDefs
                                                                      _
                                                                      DelegateSigs
                                                                      cRep'
                                                                      cCons
                                                                      cMeths
                                                                      DelegateSpecs
                                                                      cAbsR'
                                                                      (fst ValidRefinements)
                                                                      (snd ValidRefinements))
                                                          as FullySharpenedImpl
                                                        ; clear ValidRefinements ] ))
  end;
    [ simpl; intros; split;
      [ repeat split; intros; try exact tt;
        try (etransitivity;
             [eapply (@Initialize_IndexedQueryStructureImpls_AbsR qs_schema Index)
             | ];
             cbv beta;
             unfold Initialize_IndexedQueryStructureImpls',
             CallBagImplConstructor; simpl;
             higher_order_reflexivity
            )
      | repeat split; intros; try exact tt;
        try implement_bag_methods
      ] | ];
    simpl in FullySharpenedImpl;
    fold_string_hyps_in FullySharpenedImpl;
    fold_heading_hyps_in FullySharpenedImpl;
    pose_SearchUpdateTerms_in FullySharpenedImpl;
    pose_search_term_in FullySharpenedImpl;
    let impl := fresh "impl" in
    match type of FullySharpenedImpl with
      @FullySharpenedUnderDelegates _ _ ?Impl =>
      set (impl := Impl) in *
    end;
      cbv beta in *; simpl in impl;
      let impl' :=
          match goal with
            |- @FullySharpenedUnderDelegates _ _ ?Impl => Impl
          end in
      (* Not having to worry about re-typing the body during zeta-expansion
     yields a 30x speedup.
       *)
      assert (True) by
          (clear FullySharpenedImpl; zeta_expand_all impl; unify impl impl'; econstructor);
        exact FullySharpenedImpl.

Ltac FullySharpenQueryStructure' qs_schema Index :=
  let DelegateSigs := constr:(Build_IndexedQueryStructure_Impl_Sigs Index) in
  let DelegateSpecs := constr:(Build_IndexedQueryStructure_Impl_Specs Index) in
  let cRep' := constr:(Build_IndexedQueryStructure_Impl_cRep Index) in
  let cAbsR' := constr:(@Build_IndexedQueryStructure_Impl_AbsR qs_schema Index) in
  let DelegateIDs := constr:(map relName (qschemaSchemas qs_schema)) in
  let ValidRefinements := fresh in
  let FullySharpenedImpl := fresh in
  match goal with
    |- Sharpened (@BuildADT ?Rep ?consSigs ?methSigs ?consDefs ?methDefs) =>
    ilist_of_dep_evar
      (@BoundedString DelegateIDs -> Type)
      (fun D =>
         forall idx,
           ComputationalADT.pcADT (DelegateSigs idx) (D idx))
      (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
           (DelegateImpls : forall idx,
               ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
           (Sig : methSig) => ComputationalADT.cMethodType (cRep' DelegateReps)
                                                           (methDom Sig) (methCod Sig))
      methSigs
      ltac:(fun cMeths =>
              ilist_of_dep_evar
                (@BoundedString DelegateIDs -> Type)
                (fun D =>
                   forall idx,
                     ComputationalADT.pcADT (DelegateSigs idx) (D idx))
                (fun (DelegateReps : @BoundedString DelegateIDs -> Type)
                     (DelegateImpls : forall idx,
                         ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                     (Sig : consSig) =>
                   ComputationalADT.cConstructorType (cRep' DelegateReps) (consDom Sig))
                consSigs
                ltac:(fun cCons =>
                        assert
                          ((forall
                               (DelegateReps : @BoundedString DelegateIDs -> Type)
                               (DelegateImpls : forall idx,
                                   ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                               (ValidImpls
                                : forall idx : @BoundedString DelegateIDs,
                                   refineADT (DelegateSpecs idx)
                                             (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                               Iterate_Dep_Type_BoundedIndex
                                 (fun idx : BoundedIndex (map consID consSigs) =>
                                    @refineConstructor
                                      _ (cRep' DelegateReps) (cAbsR' _ _ ValidImpls)
                                      (consDom (nth_Bounded consID consSigs idx))
                                      (getConsDef consDefs idx)
                                      (fun d => ret (ith_Bounded consID (cCons DelegateReps DelegateImpls) idx d))))
                           * (forall
                                 (DelegateReps : @BoundedString DelegateIDs -> Type)
                                 (DelegateImpls : forall idx,
                                     ComputationalADT.pcADT (DelegateSigs idx) (DelegateReps idx))
                                 (ValidImpls
                                  : forall idx : @BoundedString DelegateIDs,
                                     refineADT (DelegateSpecs idx)
                                               (ComputationalADT.LiftcADT (existT _ _ (DelegateImpls idx)))),
                                 Iterate_Dep_Type_BoundedIndex
                                   (fun idx : BoundedIndex (map methID methSigs) =>
                                      @refineMethod
                                        _ (cRep' DelegateReps)
                                        (cAbsR' _ _ ValidImpls)
                                        (methDom (nth_Bounded methID methSigs idx))
                                        (methCod (nth_Bounded methID methSigs idx))
                                        (getMethDef methDefs idx)
                                        (fun r_n d => ret (ith_Bounded methID (cMeths DelegateReps DelegateImpls) idx r_n d))))) as ValidRefinements;
                      [ |
                        pose proof (@Notation_Friendly_SharpenFully'
                                      _
                                      consSigs
                                      methSigs
                                      consDefs
                                      methDefs
                                      DelegateIDs
                                      DelegateSigs
                                      cRep'
                                      cCons
                                      cMeths
                                      DelegateSpecs
                                      cAbsR'
                                      (fst ValidRefinements)
                                      (snd ValidRefinements))
                          as FullySharpenedImpl
                        ; clear ValidRefinements ]

           ))
  end;
    [ simpl; intros; split;
      [ repeat split; intros; try exact tt;
        try (etransitivity;
             [eapply (@Initialize_IndexedQueryStructureImpls_AbsR qs_schema Index)
             | ];
             cbv beta;
             unfold Initialize_IndexedQueryStructureImpls',
             CallBagImplConstructor; simpl;
             higher_order_reflexivity
            )
      | repeat split; intros; try exact tt;
        try implement_bag_methods
      ] | ].

Ltac cleanup_Count :=
  repeat first [ setoid_rewrite app_nil_r
               | setoid_rewrite filter_true
               | setoid_rewrite map_map
               | setoid_rewrite map_app
               | setoid_rewrite map_length
               ].

Ltac observer CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  try simplify with monad laws;
  repeat setoid_rewrite refine_If_Then_Else_Bind at 1;
  repeat setoid_rewrite Bind_refine_If_Then_Else;
  repeat eapply refine_If_Then_Else;
  implement_Query CreateTerm EarlyIndex LastIndex
                  makeClause_dep EarlyIndex_dep LastIndex_dep;
  simpl; repeat first [setoid_rewrite refine_bind_unit
                      | setoid_rewrite refine_bind_bind ];
  cbv beta; simpl; commit;
  (*cleanup_Count; *) (* This is taking waaaaay too much time. *)
  fold_string_hyps; fold_heading_hyps;
  finish honing.

Ltac initializer :=
  try simplify with monad laws;
  rewrite refine_QSEmptySpec_Initialize_IndexedQueryStructure;
  cbv beta; simpl;
  try simplify with monad laws;
  fold_string_hyps; fold_heading_hyps;
  finish honing.

Ltac implement_delete CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  repeat (cbv beta; simpl;
          first
            [simplify with monad laws; simpl
            | setoid_rewrite refine_If_Then_Else_Bind
            | implement_Query CreateTerm EarlyIndex LastIndex
                              makeClause_dep EarlyIndex_dep LastIndex_dep
            | implement_QSDeletedTuples ltac:(find_simple_search_term
                                                CreateTerm EarlyIndex LastIndex)
            | implement_EnsembleDelete_AbsR ltac:(find_simple_search_term
                                                    CreateTerm EarlyIndex LastIndex)
            |  setoid_rewrite refine_Pick_DelegateToBag_AbsR; [ | solve [ eauto ] .. ] ]).

Ltac implement_UpdateUnConstrRelationDeleteC find_search_term :=
  match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- refine (Bind (UpdateUnConstrRelationDeleteC ?r_o ?idx ?DeletedTuples) ?k) _ ] =>
    let filter_dec := eval simpl in (@DecideableEnsembles.dec _ DeletedTuples _) in
        let idx_search_update_term := eval simpl in (ith3 indices idx) in
            let search_term_type' := eval simpl in (BagSearchTermType idx_search_update_term) in
                let search_term_matcher := eval simpl in (BagMatchSearchTerm idx_search_update_term) in
                    makeEvar search_term_type'
                             ltac: (fun search_term =>
                                      let eqv := fresh in
                                      assert (ExtensionalEq filter_dec (search_term_matcher search_term)) as eqv;
                                    [ find_search_term qs_schema idx filter_dec search_term
                                    | let H' := fresh in
                                      pose proof (fun k' => @refine_BagADT_QSDelete' _ _ _ r_o r_n idx DeletedTuples k k' _ search_term eqv H) as H';
                                        fold_string_hyps_in H'; fold_heading_hyps_in H';
                                        eapply H'; clear H' eqv; set_evars])
  end.

Ltac deletion CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  doAny ltac:(implement_delete
                CreateTerm EarlyIndex LastIndex
                makeClause_dep EarlyIndex_dep LastIndex_dep)
               rewrite_drill ltac:(finish honing).

Ltac implement_insert CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  repeat first
         [simplify with monad laws; simpl
         | setoid_rewrite refine_If_Then_Else_Bind
         | match goal with
             H : DelegateToBag_AbsR ?r_o ?r_n
             |- context[Pick (fun idx => UnConstrFreshIdx (GetUnConstrRelation ?r_o ?Ridx) idx)] =>
             let freshIdx := fresh in
             destruct (exists_UnConstrFreshIdx H Ridx) as [? freshIdx];
               setoid_rewrite (refine_Pick_UnConstrFreshIdx H Ridx freshIdx)
           end
         | implement_Query CreateTerm EarlyIndex LastIndex
                           makeClause_dep EarlyIndex_dep LastIndex_dep
         | progress (rewrite ?refine_BagADT_QSInsert; try setoid_rewrite refine_BagADT_QSInsert); [ | solve [ eauto ] .. ]
         | progress (rewrite ?refine_Pick_DelegateToBag_AbsR; try setoid_rewrite refine_Pick_DelegateToBag_AbsR); [ | solve [ eauto ] .. ] ].

Ltac insertion CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  doAny ltac:(implement_insert
                CreateTerm EarlyIndex LastIndex
                makeClause_dep EarlyIndex_dep LastIndex_dep)
               rewrite_drill ltac:(finish honing).

Ltac method CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  match goal with
  | [ |- context[EnsembleInsert _ _] ] =>
    insertion CreateTerm EarlyIndex LastIndex
              makeClause_dep EarlyIndex_dep LastIndex_dep
  | [ |- context[Query_For _] ] =>
    observer CreateTerm EarlyIndex LastIndex
             makeClause_dep EarlyIndex_dep LastIndex_dep
  | [ |- context[EnsembleDelete _ _] ] =>
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
  match goal with
  | |- context[QSEmptySpec _] => initializer
  | |- appcontext[EnsembleInsert] =>
    insertion CreateTerm EarlyIndex LastIndex
              makeClause_dep EarlyIndex_dep LastIndex_dep
  | |- appcontext[EnsembleDelete] =>
    deletion CreateTerm EarlyIndex LastIndex
             makeClause_dep EarlyIndex_dep LastIndex_dep
  | |- _ =>
    observer CreateTerm EarlyIndex LastIndex
             makeClause_dep EarlyIndex_dep LastIndex_dep
  end.

Lemma hd_error_map:
  forall (A B: Type) (l : list A) (f : A -> B) ,
    hd_error (map f l) =
    match hd_error l with
    | Some a => Some (f a)
    | None => None
    end.
Proof.
  induction l; simpl; reflexivity.
Qed.

Ltac planner' CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  first
    [simplify with monad laws; simpl
    | simpl; rewrite !map_app
    | simpl; rewrite !map_length
    | simpl; rewrite !app_nil_r
    | simpl; rewrite !map_map
    | simpl; rewrite !filter_map
    | simpl; rewrite !hd_error_map
    | simpl; setoid_rewrite refine_if_Then_Else_Duplicate
    | simpl; setoid_rewrite refine_If_Then_Else_Bind
    | simpl; setoid_rewrite refine_If_Opt_Then_Else_Bind
    | match goal with
        H : DelegateToBag_AbsR ?r_o ?r_n
        |- context[Pick (fun idx => UnConstrFreshIdx (GetUnConstrRelation ?r_o ?Ridx) idx)] =>
        let freshIdx := fresh in
        destruct (exists_UnConstrFreshIdx H Ridx) as [? freshIdx];
          setoid_rewrite (refine_Pick_UnConstrFreshIdx H Ridx freshIdx)
      end
    | implement_QSDeletedTuples ltac:(find_simple_search_term
                                        CreateTerm EarlyIndex LastIndex)
    | implement_TopMost_Query CreateTerm EarlyIndex LastIndex
                              makeClause_dep EarlyIndex_dep LastIndex_dep
    | implement_Pick_DelegateToBag_AbsR ].

Ltac implement_drill CreateTerm EarlyIndex LastIndex :=
  subst_refine_evar;
  first
    [ eapply refine_BagADT_QSInsert'; try eassumption; intros
    | implement_UpdateUnConstrRelationDeleteC ltac:(find_simple_search_term
                                                      CreateTerm EarlyIndex LastIndex);
      intros
    | eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else;
      [intro; set_refine_evar | set_refine_evar ] ].

(*Ltac master_plan' matchIndex
       BuildEarlyIndex BuildLastIndex
       CreateTerm EarlyIndex LastIndex
       CreateTerm_dep EarlyIndex_dep LastIndex_dep
       BuildEarlyBag BuildLastBag :=
  (* Implement constraints as queries. *)
  start honing QueryStructure;
  (* Automatically select indexes + data structure. *)
  [GenerateIndexesForAll
    matchIndex
    ltac:(fun attrlist => make_simple_indexes attrlist BuildEarlyIndex BuildLastIndex;
          match goal with
            | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
            | |- _ => (* Otherwise implement each method using the indexed data structure *)
              plan CreateTerm EarlyIndex LastIndex
                   CreateTerm_dep EarlyIndex_dep LastIndex_dep
          end;
          pose_headings_all;
          match goal with
            | |- appcontext[@BuildADT (IndexedQueryStructure ?Schema ?Indexes)] =>
              FullySharpenQueryStructure Schema Indexes
          end
         )
  | simpl; pose_string_ids; pose_headings_all;
    pose_search_term;  pose_SearchUpdateTerms;

    BuildQSIndexedBags' BuildEarlyBag BuildLastBag
  | higher_order_reflexivityT ].

Ltac partial_master_plan' matchIndex
     CreateTerm EarlyIndex LastIndex
     makeClause_dep EarlyIndex_dep LastIndex_dep :=
  (* Implement constraints as queries. *)
  start honing QueryStructure;
  (* Automatically select indexes + data structure. *)
  GenerateIndexesForAll
    matchIndex
    ltac:(fun attrlist => make simple indexes using attrlist;
          match goal with
            | |- Sharpened _ => idtac (* Do nothing to the next Sharpened ADT goal. *)
            | |- _ => (* Otherwise implement each method using the indexed data structure *)
              plan CreateTerm EarlyIndex LastIndex
                   makeClause_dep EarlyIndex_dep LastIndex_dep
          end
         ). *)

Ltac Finite_AbsR_rewrite_drill :=
  subst_refine_evar;
  first
    [ try set_refine_evar;
      match goal with
        |- context [ QueryResultComp ?P ?k ] =>
        match k with
        | context [Query_Where _ _] =>
          match k with
          | context [QueryResultComp _ _] =>
            match type of k with
            | ?A -> ?B => makeEvar (A -> B)
                                   ltac:(fun k' => let H := fresh in
                                                   assert (@pointwise_relation A B refine k k') as H;
                                         [ intros ?; try set_refine_evar | setoid_rewrite H; clear H])
            end
          end
        end
      end
    | eapply refine_under_bind_both;
      [set_refine_evar | intros; set_refine_evar ]
    | eapply refine_If_Then_Else;
      [set_refine_evar | set_refine_evar ]
    | eapply refine_If_Opt_Then_Else;
      [intro; set_refine_evar | set_refine_evar ] ].

Global Opaque CallBagMethod.
Global Opaque CallBagConstructor.
Global Opaque Initialize_IndexedQueryStructure.

(* Debugging tactics *)

Ltac packaged_plan IndexTactics :=
  IndexTactics ltac:(fun _ a b c d e f => plan a b c d e f).

Ltac find_simple_search_term_through_find_Good_Term
     makeClause  qs_schema idx filter_dec search_term :=
  match type of search_term with
  | BuildIndexSearchTerm ?indexed_attrs =>
    let indexed_attrs' :=
        eval simpl in (map (fun kidx =>
                              {| KindNameKind := KindIndexKind kidx;
                                 KindNameName := @bindex string _ (KindIndexIndex kidx) |}) indexed_attrs) in
        let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
        findGoodTerm SC filter_dec indexed_attrs' makeClause
                     ltac:(fun fds tail =>
                             let tail := eval simpl in tail in
                                 pose search_term;
                           pose fds; pose tail; pose SC; pose indexed_attrs') end.

Ltac find_simple_search_term_dep_through_find_Good_Term
     makeClause  qs_schema idx dom filter_dec search_term :=
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
                                         pose search_term; pose dom;
                                   pose fds; pose tail; pose SC; pose indexed_attrs') end.
Arguments ilist2 : simpl never.
Arguments ilist2_tl : simpl never.
Arguments ilist2_hd : simpl never.

Arguments ilist3 : simpl never.
Arguments ilist3_tl : simpl never.
Arguments ilist3_hd : simpl never.

Global Opaque callMethod.
Global Opaque callConstructor.

Global Opaque QSInsert.
Global Opaque QSDelete.
Global Opaque UpdateUnConstrRelationInsertC.
Global Opaque UpdateUnConstrRelationDeleteC.
Global Opaque QueryResultComp.
