Require Export Coq.Lists.List Coq.Program.Program
        ADTSynthesis.QueryStructure.Specification.Representation.Tuple
        ADTSynthesis.QueryStructure.Specification.Representation.Heading
        ADTSynthesis.Common.ilist
        ADTSynthesis.Common.i2list.
Require Import Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.Arith.Arith
        ADTSynthesis.Common.String_as_OT
        ADTSynthesis.Common.Ensembles.IndexedEnsembles
        ADTSynthesis.Common.DecideableEnsembles
        ADTSynthesis.Common.ListFacts
        ADTSynthesis.QueryStructure.Specification.Operations.FlattenCompList
        ADTSynthesis.QueryStructure.Implementation.Operations.General.QueryRefinements
        ADTSynthesis.QueryStructure.Implementation.Operations.General.EmptyRefinements
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Implementation.ListImplementation
        ADTSynthesis.Common.PermutationFacts
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms.

Section BagsQueryStructureRefinements.

  Variable qs_schema : QueryStructureSchema.
  Variable BagIndexKeys :
    ilist (fun ns => SearchUpdateTerms (schemaHeading (relSchema ns)))
      (qschemaSchemas qs_schema).

  Lemma i2th_Bounded_Initialize_IndexedQueryStructure
  : forall ns indices v idx,
      computes_to (@Initialize_IndexedQueryStructure ns indices) v
      -> i2th_Bounded relName v idx = fun _ => False.
  Proof.
    clear.
    simpl; destruct idx as [idx [n In_n]]; revert v idx n In_n.
    induction indices; simpl; intros; destruct n; simpl in *; try discriminate;
    try injection In_n; intros; inversion_by computes_to_inv; subst.
    - unfold i2th_Bounded, ith_Bounded_rect; simpl; eauto.
      apply Extensionality_Ensembles; unfold Same_set, Included; simpl; intuition.
      inversion H.
    - unfold i2th_Bounded, ith_Bounded_rect; simpl; eapply IHindices; eauto.
  Qed.

  Corollary refine_QSEmptySpec_Initialize_IndexedQueryStructure
  : refine {nr' | DelegateToBag_AbsR (DropQSConstraints (QSEmptySpec qs_schema)) nr'}
           (Initialize_IndexedQueryStructure BagIndexKeys).
  Proof.
    intros v Comp_v.
    econstructor.
    unfold IndexedQueryStructure, DelegateToBag_AbsR, GetIndexedRelation.
    unfold GetUnConstrRelation.
    unfold DropQSConstraints, QSEmptySpec.
    intros; rewrite <- ith_Bounded_imap, ith_Bounded_BuildEmptyRelations,
    i2th_Bounded_Initialize_IndexedQueryStructure; eauto.
  Qed.

  Definition UpdateIndexedRelation
             (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx newRel
  : IndexedQueryStructure qs_schema BagIndexKeys  :=
    replace_BoundedIndex2 relName r_n idx newRel.

  Lemma get_update_indexed_eq :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx newRel,
      GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx = newRel.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i2th_replace_BoundIndex_eq; eauto using string_dec.
  Qed.

  Lemma get_update_indexed_neq :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx idx' newRel,
      idx <> idx'
      -> GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx' =
      GetIndexedRelation r_n idx'.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i2th_replace_BoundIndex_neq; eauto using string_dec.
  Qed.

  (* Cross product of lists using heterogenous lists. *)
    Definition Join_Lists
             {A : Type}
             {f : A -> Type}
             {As : list A}
             {a : A}
             (l : list (f a))
             (l' : list (ilist f As))
  : list (ilist f (a :: As)) :=
    (flat_map (fun l' => map (fun fa => icons _ fa l') l) l').

  Definition Build_single_Tuple_list
             {heading}
             (l : list (@Tuple heading))
  : list (ilist (@Tuple) [heading])
    := map (fun a => icons _ a (inil _)) l.

  Lemma refine_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : BoundedString)
                (resultComp : Tuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                   List_Query_In (Build_single_Tuple_list (snd l))
                                 (fun tup => resultComp (ilist_hd tup))) .
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod;
    intros; simpl.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold List_Query_In.
    intros v Comp_v; inversion_by computes_to_inv;
    unfold EnsembleIndexedListEquivalence,
    UnIndexedEnsembleListEquivalence in *.
    intuition; destruct_ex; intuition; subst.
    econstructor; eauto.
    econstructor; rewrite (H idx); eauto.
    unfold Build_single_Tuple_list in *; rewrite map_map.
    repeat rewrite map_map in H2; simpl in *; eauto.
  Qed.

  Local Transparent Query_For.

  Lemma refine_For_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : BoundedString)
                (f : _ -> Comp (list ResultT)),
           refine (For (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                        f l))
                  (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                   For (f l)).
  Proof.
    simpl; intros; unfold Query_For.
    simplify with monad laws.
    unfold CallBagMethod; simpl.
    unfold refine; intros; inversion_by computes_to_inv.
    subst; econstructor; econstructor; eauto.
  Qed.

  Lemma flatten_CompList_app_inv
        {A : Type}
  : forall (l l' : list (Comp (list A))) v,
      flatten_CompList (l ++ l') ↝ v
      -> exists e e',
           v = app e e'
           /\ flatten_CompList l ↝ e
           /\ flatten_CompList l' ↝ e'.
  Proof.
    induction l; simpl; intros.
    - eexists []; exists v; simpl; intuition.
    - inversion_by computes_to_inv; subst.
      destruct (IHl _ _ H1) as [e [e' [v_eq [Comp_l Comp_l']]]].
      rewrite v_eq.
      exists (app x e); exists e'; intuition.
      repeat econstructor; eauto.
  Qed.


  Lemma refine_Join_Query_In_Enumerate'
        headings
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : BoundedString)
             (resultComp : ilist (@Tuple) headings
                           -> Tuple
                           -> Comp (list ResultT))
             l,
        refine (List_Query_In l (fun tup : ilist (@Tuple) headings =>
                                   UnConstrQuery_In r_o idx (resultComp tup)))
               (l' <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                List_Query_In (Join_Lists (snd l') l)
                              (fun tup_pair => (resultComp (ilist_tl tup_pair) (ilist_hd tup_pair)))).
  Proof.
    intros.
    unfold List_Query_In; induction l; simpl.
    - intros v Comp_v; inversion_by computes_to_inv; subst; eauto.
    - setoid_rewrite IHl; rewrite refine_Query_In_Enumerate; eauto.
      unfold List_Query_In.
      setoid_rewrite refineEquiv_bind_bind at 1.
      setoid_rewrite refineEquiv_bind_bind at 2.
      intros v Comp_v; inversion_by computes_to_inv.
      rewrite map_app, map_map in H2; simpl in *.
      econstructor; eauto.
      apply flatten_CompList_app_inv in H2; destruct_ex; intuition.
      subst; repeat (econstructor; eauto).
      unfold Build_single_Tuple_list in *; rewrite map_map; simpl;
      eauto.
  Qed.

  Corollary refine_Join_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : Tuple -> Tuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist_hd tup))))
               (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                l' <- CallBagMethod idx' {|bindex := "Enumerate" |} r_n ();
                List_Query_In (Join_Lists (snd l') (Build_single_Tuple_list (snd l)))
                              (fun tup_pair => (resultComp (ilist_hd (ilist_tl tup_pair)) (ilist_hd tup_pair)))).
  Proof.
    intros.
    f_equiv; simpl; intro.
    eapply refine_Join_Query_In_Enumerate'; eauto.
  Qed.

  Lemma refine_Join_Enumerate_Swap
        (A B ResultT : Type) :
    forall (c : Comp A) (c' : Comp B)
           (resultComp : _ -> _ -> Comp (list ResultT)),
      refineEquiv (For (l <- c;
                   l' <- c';
                   resultComp l l'))
                (For (l' <- c';
                      l <- c;
                      resultComp l l')).
  Proof.
    split; simpl; intros; f_equiv; intros v Comp_v;
    inversion_by computes_to_inv; subst;
    repeat (econstructor; eauto).
  Qed.

  Lemma refine_Query_For_In_Find
        (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      ->
      forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
             filter_dec
             search_pattern
             (resultComp : Tuple -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx) search_pattern)
        -> refine (For (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                        List_Query_In (filter filter_dec (snd l)) resultComp))
                  (l <- CallBagMethod idx {|bindex := "Find" |} r_n search_pattern;
                   List_Query_In (snd l) resultComp).
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod, Query_For;
    intros; simpl.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl; f_equiv; intro.
    unfold List_Query_In.
    rewrite (filter_by_equiv _ _ H0).
    intros v Comp_v; econstructor; eauto.
  Qed.

  Instance DecideableEnsemblePair_tail
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (ilist f As))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist f (a :: As) => P (ilist_tl ab)) :=
    {| dec ab := dec (ilist_tl ab) |}.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist_tl a0)).
  Defined.

  Instance DecideableEnsemblePair_head
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (f a))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist f (a :: As) => P (ilist_hd ab)) :=
    {| dec ab := dec (ilist_hd ab) |}.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist_hd a0)).
  Defined.

  Lemma filter_join_ilist_hd
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s2 : list (ilist f' As))
      (s1 : list (f' a)),
      filter (fun x : ilist f' (a :: As) => f (ilist_hd x))
             (Join_Lists s1 s2) =
      Join_Lists (filter f s1) s2.
  Proof.
    induction s2; simpl; intros; eauto.
    rewrite filter_app, IHs2; f_equal.
    induction s1; simpl; eauto.
    rewrite IHs1; destruct (f a1); simpl; eauto.
  Qed.

  Lemma Join_Lists_nil
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall (s2 : list (ilist f' As)),
      Join_Lists (a := a) [] s2 = [].
  Proof.
    induction s2; simpl; eauto.
  Qed.

  Lemma filter_join_ilist_tail
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall
      (f : (ilist f' As) -> bool)
      (s2 : list (ilist f' As))
      (s1 : list (f' a)),
      filter (fun x : ilist f' (a :: As) => f (ilist_tl x))
                (Join_Lists s1 s2) =
      Join_Lists s1 (filter f s2).
  Proof.
    induction s2; simpl; intros; eauto.
    rewrite filter_app, IHs2.
    rewrite filter_map; simpl.
    induction s1; simpl.
    - repeat rewrite Join_Lists_nil; eauto.
    - destruct (f a0); simpl; eauto.
      + f_equal; simpl in *.
        rewrite filter_true; reflexivity.
      + rewrite filter_false in *; reflexivity.
  Qed.

  Lemma filter_Build_single_Tuple_list
        {heading}
        (l : list (@Tuple heading))
        (filter_dec : @Tuple heading -> bool)
  : filter (fun tup : ilist (@Tuple) [_] => filter_dec (ilist_hd tup)) (Build_single_Tuple_list l) = Build_single_Tuple_list (filter filter_dec l).
  Proof.
    induction l; simpl; eauto.
    destruct (filter_dec a); simpl; congruence.
  Qed.

  Corollary refine_Query_For_In_Find'
        (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      ->
      forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
             (filter_dec : Tuple -> bool)
             search_pattern
             (resultComp : _ -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx) search_pattern)
        -> refine (For (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                        List_Query_In (filter (fun tup : ilist (@Tuple) [_] => filter_dec (ilist_hd tup)) (Build_single_Tuple_list (snd l)))
                                      resultComp))
                  (l <- CallBagMethod idx {|bindex := "Find" |} r_n search_pattern;
                   List_Query_In (Build_single_Tuple_list (snd l)) resultComp).
  Proof.
    simpl; intros.
    setoid_rewrite filter_Build_single_Tuple_list.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod, Query_For;
    intros; simpl.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl; f_equiv; intro.
    unfold List_Query_In.
    rewrite (filter_by_equiv _ _ H0).
    intros v Comp_v; econstructor; eauto.
  Qed.

  Lemma refine_Join_Lists_Where_snd
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx idx'
           (DT : Ensemble Tuple)
           (DT_Dec : DecideableEnsemble DT)
           search_pattern
           (resultComp : Tuple -> Tuple -> Comp (list ResultT)),
      ExtensionalEq (@dec _ _ DT_Dec)
                    (BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx') search_pattern)
      -> refine (For (l <- CallBagMethod idx {| bindex := "Enumerate" |} r_n ();
                      l' <- CallBagMethod idx' {| bindex := "Enumerate" |} r_n ();
                      List_Query_In (Join_Lists (snd l') (Build_single_Tuple_list (snd l)))
                                    (fun tup_pair =>
                                       Where (DT (ilist_hd tup_pair))
                                             (resultComp (ilist_hd tup_pair) (ilist_hd (ilist_tl tup_pair))))))

                (For (l <- CallBagMethod idx {| bindex := "Enumerate" |} r_n ();
                      l' <- CallBagMethod idx' {| bindex := "Find" |} r_n search_pattern;
                      List_Query_In
                        (Join_Lists (snd l') (Build_single_Tuple_list (snd l)))
                                    (fun tup_pair =>
                                       (resultComp (ilist_hd tup_pair) (ilist_hd (ilist_tl tup_pair)))))).
  Proof.
    intros; repeat f_equiv; simpl; intro.
    unfold CallBagMethod; simpl.
    repeat setoid_rewrite refineEquiv_bind_bind;
      repeat setoid_rewrite refineEquiv_bind_unit;
      f_equiv; unfold pointwise_relation; intro; simpl.
    setoid_rewrite <- (filter_by_equiv _ _ H).
    setoid_rewrite refine_List_Query_In_Where; simpl.
    instantiate (1 := _); simpl.
    rewrite filter_join_ilist_hd; f_equiv.
  Qed.

  Lemma refine_List_Query_In_Return
        (ElementT ResultT : Type):
    forall (l : list ElementT)
           (f : ElementT -> ResultT),
      refine (List_Query_In l (fun el => Query_Return (f el)) ) (ret (map f l)).
  Proof.
    unfold List_Query_In; induction l; intros; simpl.
    - reflexivity.
    - unfold Query_Return; simplify with monad laws;
      setoid_rewrite IHl; simplify with monad laws;
      reflexivity.
  Qed.

  Require Import ADTSynthesis.QueryStructure.Implementation.Operations.General.DeleteRefinements.

  Lemma refine_BagADT_QSDelete_fst :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                (DT : Ensemble Tuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx) search_pattern)
           -> refine {x : list Tuple |
                      QSDeletedTuples r_o idx DT x}
                     (l <- (CallBagMethod idx {|bindex := "Delete" |} r_n search_pattern);
                      ret (snd l)).
  Proof.
    intros; setoid_rewrite DeletedTuplesFor; auto.
    rewrite refine_Query_In_Enumerate by eauto.
    setoid_rewrite refine_List_Query_In_Where.
    instantiate (1 := _).
    simpl in *.
    setoid_rewrite (refine_Query_For_In_Find' H _ H0).
    setoid_rewrite refine_List_Query_In_Return.
    unfold Build_single_Tuple_list; setoid_rewrite map_map; simpl.
    setoid_rewrite map_id.
    unfold CallBagMethod; simpl; simplify with monad laws;
    setoid_rewrite refineEquiv_bind_bind;
    setoid_rewrite refineEquiv_bind_unit; simpl;
    f_equiv; intro.
  Qed.

  Lemma refine_BagADT_QSDelete_snd :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                (DT : Ensemble Tuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx) search_pattern)
           -> refine
                {r_n' |
                 DelegateToBag_AbsR
                   (UpdateUnConstrRelation r_o idx (EnsembleDelete
                                                      (GetUnConstrRelation r_o idx)
                                                      DT)) r_n'}
                (l <- (CallBagMethod idx {|bindex := "Delete" |} r_n search_pattern);
                 ret (UpdateIndexedRelation r_n idx (fst l))).
  Proof.
    intros.
    constructor; inversion_by computes_to_inv.
    unfold CallBagMethod in *; simpl in *; inversion_by computes_to_inv; subst.
    simpl.
    unfold DelegateToBag_AbsR; intros.
    destruct (BoundedString_eq_dec idx idx0); subst.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation;
      rewrite ith_replace_BoundIndex_eq.
      unfold GetIndexedRelation, UpdateIndexedRelation;
      rewrite i2th_replace_BoundIndex_eq.
      f_equal; eauto.
      apply Extensionality_Ensembles; unfold Same_set, Included, In;
      intuition; rewrite <- H0 in *;
      eapply dec_decides_P; eauto.
    - unfold GetUnConstrRelation, UpdateUnConstrRelation;
      rewrite ith_replace_BoundIndex_neq by eauto using string_dec.
      unfold GetIndexedRelation, UpdateIndexedRelation;
      rewrite i2th_replace_BoundIndex_neq by eauto using string_dec.
      apply H.
  Qed.

End BagsQueryStructureRefinements.
