Require Export Coq.Bool.Bool Coq.Strings.String
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.ListMorphisms
        ADTSynthesis.Common.ListFacts
        ADTSynthesis.Common.BoolFacts
        ADTSynthesis.Common.LogicFacts
        ADTSynthesis.Common.FlattenList
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.IterateBoundedIndex
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Implementation.Constraints.ConstraintChecksRefinements
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagImplementation
        ADTSynthesis.QueryStructure.Implementation.ListImplementation
        ADTSynthesis.QueryStructure.Specification.Constraints.tupleAgree
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Implementation.Operations.BagADT.Refinements
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Require Export ADTSynthesis.QueryStructure.Implementation.Operations.

Global Opaque binsert benumerate bfind bcount.

Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- eq_N_dec_bool_true_iff;
  try setoid_rewrite <- eq_Z_dec_bool_true_iff;
  try setoid_rewrite <- string_dec_bool_true_iff;
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

  Require Import ADTNotation.BuildComputationalADT.
  Require Import ADT.ComputationalADT.

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
                               cAbsR')));
        unfold Dep_Type_BoundedIndex_app_comm_cons
    end; simpl; split.

  Fixpoint Build_IndexedQueryStructure_Impl_Sigs
    {indices : list NamedSchema}
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
    : list NamedADTSig :=
    match indices as indices return ilist _ indices -> list NamedADTSig with
      | nil => fun _ => nil
      | cons ns indices' =>
        fun Index =>
          {| ADTSigname := relName ns;
             namedADTSig :=
               BagSig (@Tuple (schemaHeading (relSchema ns))) (BagSearchTermType (ilist_hd Index)) (BagUpdateTermType (ilist_hd Index)) |}
                       :: @Build_IndexedQueryStructure_Impl_Sigs indices' (ilist_tl Index)
    end Index.

  Fixpoint Build_IndexedQueryStructure_Impl_Specs
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
  : ilist (fun ns => ADT (namedADTSig ns)) (@Build_IndexedQueryStructure_Impl_Sigs indices Index) :=
    match indices as indices return
          forall (Index : ilist _ indices),
            ilist (fun ns : NamedADTSig => ADT (namedADTSig ns))
                  (@Build_IndexedQueryStructure_Impl_Sigs indices Index)
    with
      | nil => fun _ => inil _
      | cons ns indices' =>
        fun Index => icons {| ADTSigname := relName ns;
                              namedADTSig := _ |}
                           (@BagSpec (@Tuple (schemaHeading (relSchema ns)))
                                     (BagSearchTermType (ilist_hd Index))
                                     (BagUpdateTermType (ilist_hd Index))
                                     (BagMatchSearchTerm (ilist_hd Index))
                                     (BagApplyUpdateTerm (ilist_hd Index)))
                           (@Build_IndexedQueryStructure_Impl_Specs indices' (ilist_tl Index))
    end Index.

  Definition Build_IndexedQueryStructure_Impl_cRep
           {indices : list NamedSchema}
           (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns)) (@Build_IndexedQueryStructure_Impl_Sigs indices Index))
  : Type
    :=
    i2list
      (fun (ns : NamedADTSig)
           (index : cADT (namedADTSig ns)) => cRep index) DelegateImpls.

  Fixpoint map_IndexedQS_idx_boundi
        {indices}
  : forall
      n
      (Index : ilist
                 (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))
                 indices)
      idx,
      nth_error
        (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index))
        n = Some idx
      ->  nth_error (map relName indices) n = Some idx.
  Proof.
    refine (match indices with
              | nil => _
              | ns :: indices' =>
                fun n =>
                  match n return
                        forall
                          (Index : ilist
                                     (fun ns : NamedSchema =>
                                        SearchUpdateTerms (schemaHeading (relSchema ns)))
                                     (ns :: indices'))
                          idx,
                          nth_error (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)) n =
                          Some idx ->
                          nth_error (map relName (ns :: indices')) n = Some idx
                  with
                    | 0 => fun Index idx nth_n => nth_n
                    | S n' => fun Index => (map_IndexedQS_idx_boundi indices' n' (ilist_tl Index))
                  end
            end);
    simpl; intros; try discriminate; eauto.
  Defined.

  Definition map_IndexedQS_idx
             indices
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             (idx : BoundedIndex
                      (map ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index)))
  : BoundedIndex (map relName indices) :=
    {| bindex := bindex idx;
       indexb := {| ibound := ibound (indexb idx);
                    boundi := map_IndexedQS_idx_boundi _ Index (boundi (indexb idx))|} |}.

  Fixpoint map_IndexedQS_idx_boundi'
        {indices}
  : forall
      n
      (Index : ilist
                 (fun ns : NamedSchema =>
                    SearchUpdateTerms (schemaHeading (relSchema ns)))
                 indices)
      idx,
      nth_error (map relName indices) n = Some idx
      -> nth_error
        (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index))
        n = Some idx.
  Proof.
    refine (match indices with
              | nil => _
              | ns :: indices' =>
                fun n =>
                  match n return
                        forall
                          (Index : ilist
                                     (fun ns : NamedSchema =>
                                        SearchUpdateTerms (schemaHeading (relSchema ns)))
                                     (ns :: indices'))
                          idx,
                          nth_error (map relName (ns :: indices')) n = Some idx
                          -> nth_error (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)) n = Some idx
                  with
                    | 0 => fun Index idx nth_n => nth_n
                    | S n' => fun Index => (map_IndexedQS_idx_boundi' indices' n' (ilist_tl Index))
                  end
            end);
    simpl; intros; try discriminate; eauto.
  Defined.

  Definition map_IndexedQS_idx'
             indices
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             (idx : BoundedIndex (map relName indices))
  : BoundedIndex
                      (map ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index)) :=
    {| bindex := bindex idx;
       indexb := {| ibound := ibound (indexb idx);
                    boundi := map_IndexedQS_idx_boundi' _ Index (boundi (indexb idx))|} |}.

  Lemma ith_Build_IndexedQueryStructure_Impl_Sigs_eq
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      (BagSig (@Tuple (schemaHeading (relSchema ((nth_Bounded relName indices (map_IndexedQS_idx Index idx))))))
              (BagSearchTermType
                 (ith_Bounded relName Index (map_IndexedQS_idx Index idx)))
              (BagUpdateTermType
                 (ith_Bounded relName Index (map_IndexedQS_idx Index idx))))
      = namedADTSig
          (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index) idx).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.

  Lemma ith_Build_IndexedQueryStructure_Impl_Specs_eq
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) idx =
  eq_rect _ ADT
          (@BagSpec (@Tuple (schemaHeading (relSchema (@nth_Bounded NamedSchema string relName
                                                                    indices (map_IndexedQS_idx Index idx)))))
                    (BagSearchTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                    (BagUpdateTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                    (BagMatchSearchTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                    (BagApplyUpdateTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx))))
                    _ (ith_Build_IndexedQueryStructure_Impl_Sigs_eq Index idx).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.

  Definition map_IndexedQS_Rep
             {indices}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             idx
             (rep : @IndexedEnsemble
                      (@Tuple
                         (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index idx) )))))
  : Rep
      (ith_Bounded ADTSigname
                   (Build_IndexedQueryStructure_Impl_Specs Index) idx).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n rep.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply IHindices; eauto.
  Defined.

  Definition map_IndexedQS_Rep'
             {indices}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             idx
             (rep : Rep
                      (ith_Bounded ADTSigname
                                   (Build_IndexedQueryStructure_Impl_Specs Index)
                                   (map_IndexedQS_idx' Index idx)))
  : @IndexedEnsemble
      (@Tuple
         (schemaHeading
            (relSchema
               (@nth_Bounded NamedSchema string relName
                             indices idx )))).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n rep.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index)); eauto.
  Defined.

  Definition Build_IndexedQueryStructure_Impl_AbsR
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
    forall idx,
      AbsR (ValidImpl idx)
           (map_IndexedQS_Rep Index idx (GetIndexedRelation r_o (map_IndexedQS_idx Index idx)))
           (i2th_Bounded ADTSigname r_n idx).

  Definition map_IndexedQS_Rep''
             {indices}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
             idx
             (rep : @IndexedEnsemble
                      (@Tuple
                         (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices idx)))))
  : Rep
      (ith_Bounded ADTSigname
                   (Build_IndexedQueryStructure_Impl_Specs Index) (map_IndexedQS_idx' Index idx)).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n rep.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply IHindices; eauto.
  Defined.

  Definition Build_IndexedQueryStructure_Impl_AbsR''
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                     (Build_IndexedQueryStructure_Impl_Sigs Index))
             (ValidImpl :
                forall idx : BoundedIndex (map relName (qschemaSchemas qs_schema)),
                  refineADT (ith_Bounded ADTSigname
                                         (Build_IndexedQueryStructure_Impl_Specs Index) (map_IndexedQS_idx' Index idx))
                            (LiftcADT (ith_Bounded ADTSigname DelegateImpls (map_IndexedQS_idx' Index idx))))
             (r_o : IndexedQueryStructure qs_schema Index)
             (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
  : Prop :=
    forall idx,
      AbsR (ValidImpl idx)
           (map_IndexedQS_Rep'' Index idx (GetIndexedRelation r_o idx))
           (i2th_Bounded ADTSigname r_n (map_IndexedQS_idx' Index idx)).

  Definition CallBagImplMethod
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                    (Build_IndexedQueryStructure_Impl_Sigs Index))
             idx midx
             (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls) :=
    cMethods (ith_Bounded ADTSigname DelegateImpls idx) midx (i2th_Bounded _ r_n idx).

  Definition CallBagImplConstructor
             {qs_schema : QueryStructureSchema}
             (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
             (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                                    (Build_IndexedQueryStructure_Impl_Sigs Index))
             idx midx :=
    cConstructors (ith_Bounded ADTSigname DelegateImpls idx) midx .

  Fixpoint Build_IndexedQueryStructure_Impl_midx
           {indices}
           (P : ADTSig -> Type)
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
             ridx
             (midx : P
                       (BagSig (@Tuple (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index ridx ) ))))
                               (BagSearchTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                               (BagUpdateTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))),
      P
        (namedADTSig
           (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)
                        ridx)) :=
    match indices return
          forall (Index : ilist
                            (fun ns : NamedSchema =>
                               SearchUpdateTerms (schemaHeading (relSchema ns)))
                            indices)
                 (ridx : BoundedIndex
                           (map ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)))
                 (midx : P
                       (BagSig (@Tuple (schemaHeading
                            (relSchema
                               (@nth_Bounded NamedSchema string relName
                                             indices (map_IndexedQS_idx Index ridx ) ))))
                               (BagSearchTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx)))
                               (BagUpdateTermType
                                  (ith_Bounded relName Index (map_IndexedQS_idx Index ridx))))),
      P
        (namedADTSig
           (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index)
                        ridx))
    with
      | nil => fun _ ridx => BoundedIndex_nil _ ridx
      | ns :: indices' =>
        fun Index ridx =>
          match ridx with
            | {| bindex := ridx;
                 indexb := {|ibound := n;
                             boundi := nth_n |}|} =>
              match n return
                    forall
                      (Index' : ilist
                                  (fun ns : NamedSchema =>
                                     SearchUpdateTerms (schemaHeading (relSchema ns))) (ns :: indices'))
                      ridx nth_n,
                      let idx := {| bindex := ridx;
                                    indexb := {|ibound := n;
                                                boundi := nth_n |}|} in
                      P
                                (BagSig (@Tuple (schemaHeading
                                                   (relSchema
                                                      (@nth_Bounded NamedSchema string relName
                                                                    (ns :: indices') (map_IndexedQS_idx Index' idx ) ))))
                                        (BagSearchTermType
                                           (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx)))
                                        (BagUpdateTermType
                                           (ith_Bounded relName Index' (map_IndexedQS_idx Index' idx)))) ->
                      P
                        (namedADTSig
                           (nth_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Sigs Index')
                                        {| bindex := ridx;
                                           indexb := {|ibound := n;
                                                       boundi := nth_n |}|}))
              with
                | 0 => fun Index idx nth_n midx => midx
                | S n' => fun Index idx nth_n midx =>
                            (@Build_IndexedQueryStructure_Impl_midx
                               indices' P (ilist_tl Index)
                               {| bindex := idx;
                                  indexb := {|ibound := n';
                                              boundi := nth_n |}|}
                               midx)
              end Index ridx nth_n
                            end
         end.

  Definition Build_IndexedQueryStructure_Impl_MethodDom
           {indices}
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           ridx
           midx,
      fst (MethodDomCod
             (BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices  ridx))))
                     (BagSearchTermType
                        (ith_Bounded relName Index ridx))
                     (BagUpdateTermType
                        (ith_Bounded relName Index ridx)))
             midx)
    -> fst
        (MethodDomCod
           (namedADTSig
              (nth_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index) (map_IndexedQS_idx' Index ridx)))
           (Build_IndexedQueryStructure_Impl_midx MethodIndex Index (map_IndexedQS_idx' Index ridx) midx)).
  Proof.
    destruct ridx as [idx [n nth_n]]; revert Index idx n nth_n.
    induction indices.
  - destruct n; simpl; discriminate.
  - destruct n; simpl; eauto.
    intros; eapply (IHindices (ilist_tl Index) idx n nth_n); eauto.
  Defined.

  Definition Build_IndexedQueryStructure_Impl_MethodCod
           {indices}
  : forall (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices)
           ridx
           midx,
      snd
        (MethodDomCod
           (namedADTSig
              (nth_Bounded ADTSigname
                           (Build_IndexedQueryStructure_Impl_Sigs Index) (map_IndexedQS_idx' Index ridx)))
           (Build_IndexedQueryStructure_Impl_midx MethodIndex Index (map_IndexedQS_idx' Index ridx) midx))
  ->       snd (MethodDomCod
             (BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices  ridx))))
                     (BagSearchTermType
                        (ith_Bounded relName Index ridx))
                     (BagUpdateTermType
                        (ith_Bounded relName Index ridx)))
             midx)
.
  Proof.
    destruct ridx as [idx [n nth_n]]; revert Index idx n nth_n.
    induction indices.
  - destruct n; simpl; discriminate.
  - destruct n; simpl; eauto.
    intros; eapply (IHindices (ilist_tl Index) idx n nth_n); eauto.
  Defined.

Lemma ith_Build_IndexedQueryStructure_Impl_Methods
        {indices}
  : forall
      (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) indices )
      (idx : BoundedIndex
               (map ADTSigname
                    (Build_IndexedQueryStructure_Impl_Sigs Index))),
      Methods (ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) idx) =
      eq_rect _ (fun r => forall idx, methodType (Rep r) _ _ )
              (Methods (eq_rect _ ADT
                                (@BagSpec (@Tuple (schemaHeading (relSchema (@nth_Bounded NamedSchema string relName
                                                                                          indices (map_IndexedQS_idx Index idx)))))
                                          (BagSearchTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagUpdateTermType (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagMatchSearchTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx)))
                                          (BagApplyUpdateTerm (ith_Bounded _ Index (map_IndexedQS_idx Index idx))))
                                _ (ith_Build_IndexedQueryStructure_Impl_Sigs_eq Index idx)))
              _ (eq_sym (ith_Build_IndexedQueryStructure_Impl_Specs_eq Index idx)).
  Proof.
    destruct idx as [idx [n nth_n]].
    revert Index idx n nth_n.
    induction indices; destruct n; simpl; intros; try discriminate; eauto.
    eapply (IHindices (ilist_tl Index) idx n nth_n).
  Defined.

  Lemma refine_Mapped_Methods
        {indices}
        (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (indices) )
  :  forall
      ridx,
      forall
        (r_o : @IndexedEnsemble (@Tuple (schemaHeading (relSchema (nth_Bounded relName indices ridx)))))
      midx
      d r s,
        let ridx' := map_IndexedQS_idx' Index ridx in
        let midx' := Build_IndexedQueryStructure_Impl_midx MethodIndex Index ridx' midx in
        let d' := Build_IndexedQueryStructure_Impl_MethodDom Index ridx _ d in
Methods
     (ith_Bounded ADTSigname (Build_IndexedQueryStructure_Impl_Specs Index) ridx') midx'
     (map_IndexedQS_Rep'' Index ridx r_o) d'
     ↝ (r, s) ->
Methods
  (BagSpec (BagMatchSearchTerm (ith_Bounded relName Index ridx))
           (BagApplyUpdateTerm (ith_Bounded relName Index ridx))) midx r_o d
   ↝ (map_IndexedQS_Rep' Index ridx r,
     Build_IndexedQueryStructure_Impl_MethodCod Index ridx midx s).
  Proof.
    intros; pose proof (ith_Build_IndexedQueryStructure_Impl_Methods Index ridx') as H';
    rewrite H' in H; revert H; clear H'.
    unfold d', midx', ridx' in *; clear ridx' midx' d'.
    revert r_o d r s.
    intro; eapply (Iterate_Dep_Type_BoundedIndex_equiv_1) with (idx := midx);
    simpl.
    intuition;
      simpl in *;
      first [revert midx r_o d r s H
            | revert midx r_o b a r s H ];
    try (destruct ridx as [idx [n nth_n]];
      revert idx n nth_n;
      unfold IndexedQueryStructure, GetIndexedRelation in *;
      unfold list_ind, list_rect in *;
      induction indices; destruct n; simpl; try (intros; discriminate); eauto;
      eapply IHindices).
  Qed.


  Lemma map_indexedqs_Rep'_id
        {indices}
  : forall Index idx r_o,
      map_IndexedQS_Rep'' (indices := indices) Index idx (map_IndexedQS_Rep' Index idx r_o) = r_o.
  Proof.
    destruct idx as [idx [n nth_n]]; revert Index idx n nth_n.
    induction indices; simpl; intros.
    - destruct n; discriminate.
    - destruct n; simpl in *; eauto.
      eapply (IHindices (ilist_tl Index)).
  Qed.

  Lemma Update_Build_IndexedQueryStructure_Impl_AbsR''
        {qs_schema}
        Index
  : forall
      DelegateImpl
      ValidImpl
      (r_o : IndexedQueryStructure qs_schema Index)
      (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpl)
      idx r_o' r_n',
      Build_IndexedQueryStructure_Impl_AbsR'' ValidImpl r_o r_n
      -> AbsR (ValidImpl idx) r_o' r_n'
      -> Build_IndexedQueryStructure_Impl_AbsR''
           ValidImpl
           (UpdateIndexedRelation r_o idx (map_IndexedQS_Rep' _ _ r_o'))
           (replace_BoundedIndex2 _ r_n (map_IndexedQS_idx' _ idx) r_n').
  Proof.
    intros; intro idx'.
    destruct (BoundedString_eq_dec idx idx'); subst.
    - rewrite i2th_replace_BoundIndex_eq, get_update_indexed_eq, map_indexedqs_Rep'_id; eauto.
    - rewrite i2th_replace_BoundIndex_neq, get_update_indexed_neq; eauto using string_dec.
      intuition; apply n.
      destruct idx as [idx [m nth_m]]; destruct idx' as [idx' [n' nth_n']]; simpl in *.
      injection H1; intros; subst; repeat f_equal.
      unfold map_IndexedQS_idx' in H1; simpl in H1.
      apply eq_proofs_unicity_Opt_A; eauto using string_dec.
  Qed.

  Lemma refine_BagImplMethods'
        {qs_schema : QueryStructureSchema}
        (Index : ilist (fun ns : NamedSchema => SearchUpdateTerms (schemaHeading (relSchema ns))) (qschemaSchemas qs_schema) )
        (DelegateImpls : ilist (fun ns => cADT (namedADTSig ns))
                               (Build_IndexedQueryStructure_Impl_Sigs Index))
        ValidImpl
  :  forall (r_o : IndexedQueryStructure qs_schema Index)
            (r_n : Build_IndexedQueryStructure_Impl_cRep Index DelegateImpls)
            ridx,
       let ridx' := map_IndexedQS_idx' Index ridx in
       Build_IndexedQueryStructure_Impl_AbsR'' ValidImpl r_o r_n ->
            forall (midx : MethodIndex
                     (BagSig Tuple
                             (BagSearchTermType
                                (ith_Bounded relName Index (map_IndexedQS_idx Index ridx')))
                             (BagUpdateTermType
                                (ith_Bounded relName Index (map_IndexedQS_idx Index ridx')))))
                   (d : fst
                          (MethodDomCod
                             (BagSig (@Tuple (schemaHeading (relSchema (nth_Bounded relName (qschemaSchemas qs_schema) ridx))))
                                     (BagSearchTermType (ith_Bounded relName Index ridx))
                                     (BagUpdateTermType (ith_Bounded relName Index ridx))) midx)),
       let midx' := Build_IndexedQueryStructure_Impl_midx MethodIndex Index ridx' midx in
       let d' := Build_IndexedQueryStructure_Impl_MethodDom Index ridx _ d in
       exists r_o',
                  refine (CallBagMethod ridx midx r_o d)
                  (ret (map_IndexedQS_Rep' _ _ r_o',
                        Build_IndexedQueryStructure_Impl_MethodCod Index ridx _
                                                                   (snd (CallBagImplMethod (map_IndexedQS_idx' Index ridx) midx' r_n d'))))
                /\ AbsR (ValidImpl ridx) r_o' (fst (CallBagImplMethod ridx' midx' r_n d')).
    intros.
    pose proof (ADTRefinementPreservesMethods (ValidImpl ridx) midx'
                                              (map_IndexedQS_Rep'' Index ridx
                                                                 (GetIndexedRelation r_o ridx))
                                              (i2th_Bounded _ r_n ridx') d' (H ridx) (ReturnComputes _)).
    Local Arguments map_IndexedQS_Rep : simpl never.
    inversion_by computes_to_inv; subst.
    exists (fst x);
      unfold CallBagImplMethod; simpl in *.
      split; simpl.
      - pose proof (f_equal snd H3) as eq_x; simpl in eq_x.
        assert (refine (CallBagMethod ridx midx r_o d)
                       (ret
                          (map_IndexedQS_Rep' Index ridx (fst x),
                           Build_IndexedQueryStructure_Impl_MethodCod Index ridx midx (snd x))));
          [ | rewrite eq_x in H0;  eapply H0 ].
        intros v Comp_v; simpl in *; inversion_by computes_to_inv; subst.
        destruct x; simpl @fst in *; simpl @snd in *.
        unfold ridx' in *.
        revert H1.
        Local Transparent CallBagMethod.
        eapply refine_Mapped_Methods.
      - pose proof (f_equal fst H3) as eq_x0; simpl in eq_x0.
        rewrite eq_x0 in H2; simpl in H2; apply H2.
  Qed.

  Opaque CallBagMethod.


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


Ltac findMatchingTerm fds s k :=
  match fds with
    | (?fd, ?X) =>
      let H := fresh in assert (H : bindex s = fd) by reflexivity; clear H;
        k X
    | (?fds1, ?fds2) => findMatchingTerm fds1 s k || findMatchingTerm fds2 s k
  end.

Ltac createTerm f fds tail fs k :=
  match fs with
  | nil =>
    k tail
  | ?s :: ?fs' =>
    createTerm f fds tail fs' ltac:(fun rest =>
      findMatchingTerm fds s ltac:(fun X =>
        k (Some X, rest))
      || k (@None (f s), rest))
  end.

(* Get the heading of SC, then *)
Ltac makeTerm fs SC fds tail k :=
  match eval hnf in SC with
  | Build_Heading ?f =>
    createTerm f fds tail fs k
  end.

(* Given a storage schema [SC], a filter [F], and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]). *)
Ltac findGoodTerm SC F k :=
  match F with
    | fun a => ?[@?f a] =>
      match type of f with
        | forall a, {?X = _!?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {_!?fd = ?X} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {?X = _``?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
        | forall a, {_``?fd = ?X} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
      end
    | fun a => (@?f a) && (@?g a) =>
      findGoodTerm SC f ltac:(fun fds1 tail1 =>
                                findGoodTerm SC g ltac:(fun fds2 tail2 =>
                                                          k (fds1, fds2) (fun tup : @Tuple SC => (tail1 tup) && (tail2 tup))))
    | _ => k tt F
  end.

Ltac find_simple_search_term qs_schema idx filter_dec search_term :=
  match type of search_term with
    | BuildIndexSearchTerm ?attr =>
     let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
              findGoodTerm SC filter_dec
                           ltac:(fun fds tail =>
                                   let tail := eval simpl in tail in
                                       makeTerm attr SC fds tail
                                                ltac:(fun tm => pose tm; try unify tm search_term;
                                                      unfold ExtensionalEq, MatchIndexSearchTerm;
                                                      simpl; intro; try prove_extensional_eq))
  end.

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
        |- context[For (l <- CallBagMethod ?idx {| bindex := "Enumerate"|} ?r_n0 ();
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

  Add Parametric Morphism
      (A : Type)
      (f : A -> Type)
      (As : list A)
      (a : A)
      (l' : list (ilist f As))
      : (@Join_Lists A f As a l')
      with signature
      (pointwise_relation _ refine) ==> refine
        as refine_Join_Lists.
  Proof.
    unfold pointwise_relation; simpl; intros.
    induction l'; unfold Join_Lists; simpl.
    - reflexivity.
    - rewrite H; setoid_rewrite IHl'; reflexivity.
  Qed.

Lemma refine_Join_Enumerate_Swap
      qs_schema BagIndexKeys
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : _ -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                l' <- (Join_Lists (Build_single_Tuple_list (snd l))
                                  (fun _ => l <- (CallBagMethod idx' {|bindex := "Enumerate" |} r_n ());
                                   ret (snd l)));
                List_Query_In l' resultComp)
               (l <- CallBagMethod idx' {|bindex := "Enumerate" |} r_n ();
                l' <- (Join_Lists (Build_single_Tuple_list (snd l))
                                  (fun _ => l <- (CallBagMethod idx {|bindex := "Enumerate" |} r_n ());
                                   ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (icons _ (ilist_hd (ilist_tl tup_pair)) (icons _ (ilist_hd tup_pair) (inil _)))))).
  Proof.
  Admitted.

(* implement_In' implements [UnConstrQuery_In] in a variety of contexts. *)
Ltac implement_In' :=
  match goal with
    (* Implement a List_Query_In of a list [l] applied to a UnConstrQuery_In [idx]
        by enumerating [idx] with a method call and joining the result with [l] *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[fun b' : ?ElementT => List_Query_In (@?l b') (fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b' b) )] ] =>
      let H' := eval simpl in
      (fun (b' : ElementT) => refine_Join_Query_In_Enumerate' H idx (f b') (l b')) in
          setoid_rewrite H'

    (* Implement a 'naked' UnConstrQuery_In as a call to enumerate *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx ?f] ] =>
      let H' := eval simpl in (refine_Query_In_Enumerate H (idx := idx) f) in
          setoid_rewrite H'

    (* Implement a UnConstrQuery_In under a single binder as a call to enumerate *)
    | [H : @DelegateToBag_AbsR ?qs_schema ?indexes ?r_o ?r_n
       |- context[fun b => UnConstrQuery_In (ResultT := ?resultT) ?r_o ?idx (@?f b) ] ] =>
      let H' := eval simpl in
      (fun b => @refine_Query_In_Enumerate qs_schema indexes _ r_o r_n H idx (f b)) in
          setoid_rewrite H'
  end.

Ltac implement_In :=
  (* First simplify any large terms [i.e. Rep, BagSpec, snd, and MethodDomCod
     that might slow down setoid rewriting *)
  simpl in *;
  (* The repeatedly implement [In]s *)
  repeat implement_In'.


  Fixpoint Join_ListsT (Ts : list Type) : Type
    :=
      match Ts with
        | [] => unit
        | [A] => A
        | A :: Cs => prod A (Join_ListsT Cs)
      end.

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
      | |- ExtensionalEq (fun a => (@?f a)) ?b =>
        let fT := type of f in
        makeEvar
          fT
          ltac:(fun f' => k)
    end.

  (* Convert List_Query_In Where Clauses into a filter using search terms. *)
  Ltac convert_Where_to_search_term :=
    (* First replace Where clauses with test functions. *)
    simpl; repeat (setoid_rewrite refine_List_Query_In_Where;
                   instantiate (1 := _)); simpl;
    (* Combine different filters into a single function. *)
    repeat setoid_rewrite <- filter_and;
    (* Now break the functions up again and find search term replacements for each. *)
    match goal with
        |- context [List_Query_In (filter ?f _) _] =>
        let T := type of f in
        makeEvar T
                 ltac:(fun g =>
                         let eqv := fresh in
                         assert (ExtensionalEq f g) as eqv;
                       [ apply ExtensionalEq_andb_true; split_filters idtac
                       | setoid_rewrite (filter_by_equiv f g eqv)])
    end.

  Ltac equate X Y := let H := fresh in assert (H : X = Y) by reflexivity; clear H.

    Definition unit_Heading :=
      {| Attributes := unit;
         Domain := fun _ => unit |}.

    Definition unit_Tuple : @Tuple unit_Heading := id.

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

 (* Build pairs of fields + their values. *)
    Ltac findGoodTerm_dep SC F k :=
  match F with
  | fun (a : ?T) b => ?[@?f a b] =>
    match type of f with
    | forall a b, {@?X a = _!?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
    | forall a b, {_!?fd = @?X a} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
    | forall a b, {@?X a = _``?fd} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
    | forall a b, {_``?fd = @?X a} + {_} => k (fd, X) (fun _ : @Tuple SC => true)
    end
  | fun (a : ?T) b => (@?f a b) && (@?g a b) =>
    findGoodTerm_dep SC f ltac:(fun fds1 tail1 =>
      findGoodTerm_dep SC g ltac:(fun fds2 tail2 =>
        k (fds1, fds2) (fun tup : @Tuple SC => (tail1 tup) && (tail2 tup))))
  | _ => k tt F
  end.

    (* Build search a search term from the list of attribute + value pairs in fs. *)
Ltac createTerm_dep dom fs f fds tail k :=
  match fs with
  | nil =>
    k (fun x : dom => tail)
  | ?s :: ?fs' =>
    createTerm_dep dom fs' f fds tail
      ltac:(fun rest =>
               findMatchingTerm fds s
                   ltac:(fun X =>
                           k (fun x : dom => (Some (X x), rest x)))
                          || k (fun x : dom => (@None (f s), rest x)))
  end.

(* Get the heading of [SC] before building the search term. *)
Ltac makeTerm_dep dom fs SC fds tail k :=
  match eval hnf in SC with
  | Build_Heading ?f =>
    createTerm_dep dom fs f fds tail k
  end.

Definition Dep_SearchTerm_Wrapper {A} {heading}
           (search_term_dep : @Tuple heading -> A)
           (tup : @Tuple heading) : A := search_term_dep tup.

Ltac find_simple_search_term_dep qs_schema idx dom filter_dec search_term :=
  match type of search_term with
    | ?dom -> BuildIndexSearchTerm ?attr =>
      let SC := constr:(QSGetNRelSchemaHeading qs_schema idx) in
      findGoodTerm_dep SC filter_dec
                       ltac:(fun fds tail =>
                               let tail := eval simpl in tail in
                                   makeTerm_dep dom attr SC fds tail
                                                ltac:(fun tm => pose tm;
                                                      (* unification fails if I don't pose tm first... *)
                                                      unify (Dep_SearchTerm_Wrapper tm) search_term;
                                                      unfold ExtensionalEq, MatchIndexSearchTerm;
                                                      simpl; intros;
                                                      try prove_extensional_eq))
  end.

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

Ltac find_equivalent_search_term_pair m n build_search_term_dep :=
match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- ExtensionalEq ?f _ ] =>
    get_ithDefault_pair f m n
      ltac:(fun filter_dec =>
        let dom := match type of filter_dec with
                     | ?A -> ?B -> bool => constr:(A)
                   end in
        let heading := match type of filter_dec with
                         | ?A -> @Tuple ?heading -> bool => constr:(heading)
                       end in
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
                          assert (forall a b, filter_dec a b
                                                = search_term_matcher (search_term a) b) as eqv;
                        [ build_search_term_dep qs_schema idx
                          dom filter_dec search_term
                        | match goal with
                            |- ExtensionalEq ?f ?search_term' =>
                            match type of f with
                                | ?A -> _ =>
                                  unify search_term' (fun a : A => search_term_matcher (search_term (ith_default unit_Heading unit_Tuple a m))
            ((ith_default unit_Heading unit_Tuple a n)))
                            end
                                                  end;
                          unfold ExtensionalEq in *; intros;
                          simpl in *; rewrite eqv; reflexivity
]))) end.

Ltac find_equivalent_search_term m build_search_term :=
match goal with
    [ H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
      |- ExtensionalEq ?f _ ] =>
    get_ithDefault f m
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
                                  unify search_term' (fun a : A => search_term_matcher search_term (ith_default unit_Heading unit_Tuple a m))
                              end
                          end;
                          unfold ExtensionalEq in *; intros;
                          simpl in *; rewrite eqv; reflexivity
]))) end.


Corollary refine_Join_Lists_filter_filter_search_term_snd_dep'
          qs_schema BagIndexKeys
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx idx'
           (search_pattern : _ -> _)
           (resultComp : ilist (@Tuple) [_; _] -> Comp (list ResultT))
           filter_rest st,
      refine (cl <- CallBagMethod idx {| bindex := "Find" |} r_n st;
              l' <- (Join_Lists (Build_single_Tuple_list (snd cl))
                                (fun _ => l <- CallBagMethod idx' {| bindex := "Enumerate" |} r_n ();
                                 ret (snd l)));
              List_Query_In (filter (fun a : ilist (@Tuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist_tl a)) (ilist_hd a) && filter_rest a) l')
                            resultComp)
             (cl <- CallBagMethod idx {| bindex := "Find" |} r_n st;
              l' <- (Join_Lists (Build_single_Tuple_list (snd cl))
                                (fun tup => l <- CallBagMethod idx' {| bindex := "Find" |} r_n (search_pattern tup);
                                             ret (snd l)));
                      List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; f_equiv; intro;
    apply refine_Join_Lists_filter_search_term_snd_dep.
  Qed.

  Ltac convert_filter_to_find':=
    try match goal with
            |- context[filter (fun a => (_ && _) && true) _] =>
            setoid_rewrite <- andb_assoc; simpl
        end;
    match goal with
      | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[l <- CallBagMethod ?idx ``("Enumerate") ?r_n ();
                    List_Query_In (filter (fun a => MatchIndexSearchTerm ?st (ilist_hd a) && @?filter_rest a)
                                          (Build_single_Tuple_list (snd l))) ?resultComp] =>
        let b := fresh in
        pose proof (@refine_Query_For_In_Find_single _ _ _ r_o r_n H idx st resultComp filter_rest) as b;
          simpl in b; setoid_rewrite b; clear b

      | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[l <- CallBagMethod ?idx ``("Enumerate") ?r_n ();
                    l' <- Join_Lists (Build_single_Tuple_list (snd l)) ?cl;
                    List_Query_In (filter (fun a => MatchIndexSearchTerm ?st (ilist_hd (ilist_tl a)) && @?filter_rest a)
                                          l') ?resultComp] =>
        let b := fresh in
        pose proof (fun foo => @refine_Join_Lists_filter_search_term_fst _ _ _ r_n idx _ cl st resultComp foo filter_rest) as b;
          simpl in b; setoid_rewrite b;
          [ clear b
          | match goal with
              | |- context [CallBagMethod ?idx' ``("Enumerate") _ _] =>
                intros; eapply (realizeable_Enumerate (r_o := r_o) (r_n := r_n) idx' H)
              | |- context [CallBagMethod ?idx' ``("Find") _ _] =>
                intros; eapply (realizeable_Find (r_o := r_o) (r_n := r_n) idx' H)
            end]
      | H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
        |- context[l <- CallBagMethod ?idx ``("Find") ?r_n ?st;
                    l' <- Join_Lists (Build_single_Tuple_list (snd l))
                       (fun _ : ilist (@Tuple) [?heading] =>
                          l <- CallBagMethod ?idx' ``("Enumerate") ?r_n ();
                        ret (snd l));
                    List_Query_In (filter (fun a => MatchIndexSearchTerm (Dep_SearchTerm_Wrapper ?st' (ilist_hd (ilist_tl a)))
                                                                         (ilist_hd a) && @?filter_rest a) l') ?resultComp] =>
        let b := fresh in
        pose proof (@refine_Join_Lists_filter_filter_search_term_snd_dep' _ _ _ r_n idx idx'
                                                                          (fun a => Dep_SearchTerm_Wrapper st' (ilist_hd a))
                                                                          resultComp filter_rest st) as b;
          unfold Dep_SearchTerm_Wrapper in b; simpl in b; setoid_rewrite b; clear b
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
      end.

  (* Commits the database at the end of a method call. *)
  Ltac commit :=
    match goal with
      | [H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n
         |- context[{r_n' : IndexedQueryStructure ?qs_schema ?indices | DelegateToBag_AbsR ?r_o r_n'}] ]
        => setoid_rewrite (refine_pick_val (@DelegateToBag_AbsR qs_schema indices r_o) H);
          simplify with monad laws
    end.
