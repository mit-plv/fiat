Require Export Coq.Lists.List Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.Common.ilist
        Fiat.Common.i2list.
Require Import Coq.Bool.Bool Coq.Strings.String
        Coq.Structures.OrderedTypeEx Coq.Arith.Arith
        Fiat.Common.String_as_OT
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.ListFacts
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.EmptyRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.ListImplementation
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

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
    try injection In_n; intros;  computes_to_inv; subst.
    - unfold i2th_Bounded, ith_Bounded_rect; simpl; eauto.
      apply Extensionality_Ensembles; unfold Same_set, Included; simpl; intuition.
      unfold CallBagConstructor in H; simpl in H;  computes_to_inv.
      subst; simpl in *; destruct H0.
    - unfold i2th_Bounded, ith_Bounded_rect; simpl; eapply IHindices; eauto.
  Qed.

  Corollary refine_QSEmptySpec_Initialize_IndexedQueryStructure
  : refine {nr' | DelegateToBag_AbsR (DropQSConstraints (QSEmptySpec qs_schema)) nr'}
           (@Initialize_IndexedQueryStructure _ BagIndexKeys).
  Proof.
    intros v Comp_v.
    computes_to_econstructor.
    unfold IndexedQueryStructure, DelegateToBag_AbsR, GetIndexedRelation.
    unfold GetUnConstrRelation.
    unfold DropQSConstraints, QSEmptySpec; split.
    intros; rewrite <- ith_Bounded_imap, ith_Bounded_BuildEmptyRelations,
            i2th_Bounded_Initialize_IndexedQueryStructure; eauto.
    intros; eexists [];
    apply EnsembleIndexedListEquivalence_Empty.
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

  Lemma refine_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : BoundedString)
                (resultComp : Tuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- Join_Comp_Lists [ inil _ ]
                     (fun _ =>
                        l <- CallBagMethod idx BagEnumerate r_n ();
                      (ret (snd l)));
                   (List_Query_In l (fun tup : ilist (@Tuple) [ _ ]=> resultComp (ilist_hd tup)))) .
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod;
    intros; simpl.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold List_Query_In.
    intros v Comp_v;  computes_to_inv;
    unfold EnsembleIndexedListEquivalence,
    UnIndexedEnsembleListEquivalence in *.
    intuition; destruct_ex; intuition; subst.
    computes_to_econstructor; eauto.
    computes_to_econstructor; rewrite ((proj1 H) idx); eauto.
    rewrite map_map.
    repeat setoid_rewrite map_app in Comp_v'';
      repeat setoid_rewrite map_map in Comp_v''; simpl in *;
      rewrite app_nil_r in Comp_v''; eauto.
  Qed.

  Lemma refine_Filtered_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : BoundedString)
                (resultComp : Tuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- Join_Filtered_Comp_Lists [ inil _ ]
                     (fun _ =>
                        l <- CallBagMethod idx BagEnumerate r_n ();
                      (ret (snd l)))
                     (fun _ => true);
                   (List_Query_In l (fun tup : ilist (@Tuple) [ _ ]=> resultComp (ilist_hd tup)))) .
  Proof.
    intros; rewrite refine_Query_In_Enumerate by eauto.
    rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Local Transparent Query_For.

  Lemma refine_For_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : BoundedString)
                (f : _ -> Comp (list ResultT)),
           refine (For (l <- CallBagMethod idx BagEnumerate r_n ();
                        f l))
                  (l <- CallBagMethod idx BagEnumerate r_n ();
                   For (f l)).
  Proof.
    simpl; intros; unfold Query_For.
    simplify with monad laws.
    unfold CallBagMethod; simpl.
    unfold refine; intros;  computes_to_inv.
    subst; repeat computes_to_econstructor; eauto.
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
               (l' <- (Join_Comp_Lists l (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                          ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (ilist_tl tup_pair) (ilist_hd tup_pair)))).
  Proof.
    intros.
    unfold List_Query_In; induction l; unfold Join_Comp_Lists; simpl.
    - intros v Comp_v;  computes_to_inv; subst; eauto.
    - setoid_rewrite IHl; rewrite refine_Query_In_Enumerate; eauto.
      unfold List_Query_In.
      setoid_rewrite refineEquiv_bind_bind at 1.
      setoid_rewrite refineEquiv_bind_bind at 2.
      intros v Comp_v;  computes_to_inv.
      subst.
      rewrite map_app, map_map in Comp_v'; simpl in *.
      computes_to_econstructor; eauto.
      apply flatten_CompList_app_inv' in Comp_v'; destruct_ex; intuition.
      subst; repeat (computes_to_econstructor; eauto).
      unfold Build_single_Tuple_list in *.
      rewrite !map_app, !map_map, app_nil_r; simpl; eauto.
  Qed.

  Corollary refine_Join_Query_In_Enumerate
            (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : Tuple -> Tuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist_hd tup))))
               (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (ilist_hd (ilist_tl tup_pair)) (ilist_hd tup_pair)))).
  Proof.
    intros.
    f_equiv; simpl; intro.
    eapply refine_Join_Query_In_Enumerate'; eauto.
  Qed.

  Corollary refine_Filtered_Join_Query_In_Enumerate'
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
               (l' <- (Join_Filtered_Comp_Lists l (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                                   ret (snd l))
                                                (fun _ => true));
                List_Query_In l' (fun tup_pair => (resultComp (ilist_tl tup_pair) (ilist_hd tup_pair)))).
  Proof.
    intros; rewrite refine_Join_Query_In_Enumerate' by eauto.
    rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Corollary refine_Filtered_Join_Query_In_Enumerate
            (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : Tuple -> Tuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist_hd tup))))
               (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Filtered_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l))
                                       (fun _ => true));
                List_Query_In l' (fun tup_pair => (resultComp (ilist_hd (ilist_tl tup_pair)) (ilist_hd tup_pair)))).
  Proof.
    intros; rewrite refine_Join_Query_In_Enumerate by eauto.
    f_equiv; intro; rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Lemma refine_Join_Enumerate_Swap
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : _ -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' resultComp)
               (l <- CallBagMethod idx' BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (icons _ (ilist_hd (ilist_tl tup_pair)) (icons _ (ilist_hd tup_pair) (inil _)))))).
  Proof.
  Admitted.

  (* Lemma refine_Join_Enumerate_Swap
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
     computes_to_inv; subst;
    repeat (econstructor; eauto).
  Qed.*)

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
        -> refine (l <- CallBagMethod idx BagEnumerate r_n ();
                   List_Query_In (filter filter_dec (snd l)) resultComp)
                  (l <- CallBagMethod idx BagFind r_n search_pattern;
                   List_Query_In (snd l) resultComp).
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod, Query_For;
    intros; simpl.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl; f_equiv; intro.
    unfold List_Query_In.
    rewrite (filter_by_equiv _ _ H0).
    reflexivity.
  Qed.

  Lemma refine_Join_Comp_Lists_To_Find
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall {headings}
                (l1 : list (ilist (@Tuple) headings))
                (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                search_pattern,
           refine (Join_Filtered_Comp_Lists l1
                                            (fun _ =>
                                               l <- CallBagMethod idx BagEnumerate r_n ();
                                             ret (snd l))
                                            (fun a => BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx) search_pattern (ilist_hd a) && true))
                  (Join_Comp_Lists l1
                                   (fun _ =>
                                      l <- CallBagMethod idx BagFind r_n search_pattern;
                                    ret (snd l))) .
  Proof.
    unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; intros; simpl.
    induction l1.
    - simplify with monad laws; reflexivity.
    - Local Transparent CallBagMethod.
      unfold CallBagMethod.
      simpl.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      intros v Comp_v.
       computes_to_inv; subst.
       generalize (IHl1 _ Comp_v); intros;  computes_to_inv.
       computes_to_econstructor; subst; eauto.
      rewrite filter_app, filter_map.
      simpl.
      erewrite filter_by_equiv; eauto.
      unfold ExtensionalEq; intros; rewrite andb_true_r; auto.
  Qed.

  Lemma refine_Join_Comp_Lists_To_Find_dep
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall {headings}
                (l1 : list (ilist (@Tuple) headings))
                (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                (search_pattern : ilist (@Tuple) headings -> _),
           refine (Join_Filtered_Comp_Lists l1
                                            (fun _ =>
                                               l <- CallBagMethod idx BagEnumerate r_n ();
                                             ret (snd l))
                                            (fun a => BagMatchSearchTerm (ith_Bounded relName BagIndexKeys idx)
                                                                         (search_pattern (ilist_tl a)) (ilist_hd a) && true))
                  (Join_Comp_Lists l1
                                   (fun a =>
                                      l <- CallBagMethod idx BagFind r_n (search_pattern a);
                                    ret (snd l))) .
  Proof.
    unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; intros; simpl.
    induction l1.
    - simplify with monad laws; reflexivity.
    - Local Transparent CallBagMethod.
      unfold CallBagMethod.
      simpl.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      intros v Comp_v.
       computes_to_inv; subst.
      generalize (IHl1 _ Comp_v); intros;  computes_to_inv.
      computes_to_econstructor; subst; eauto.
      rewrite filter_app, filter_map.
      simpl.
      erewrite filter_by_equiv; eauto.
      unfold ExtensionalEq; intros; rewrite andb_true_r; auto.
  Qed.


  Instance DecideableEnsemblePair_tail
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (ilist f As))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist f (a :: As) => P (ilist_tl ab)) :=
    { dec ab := dec (ilist_tl ab) }.
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
    { dec ab := dec (ilist_hd ab) }.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist_hd a0)).
  Defined.

  Lemma Join_Comp_Lists_nil
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall (s2 : _ -> Comp (list (f' a))),
      refineEquiv (Join_Comp_Lists (As := As) (a := a) [] s2) (ret []).
  Proof.
    unfold Join_Comp_Lists; simpl; try reflexivity.
  Qed.

  Lemma filter_and_join_ilist_hd
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s1 : list (ilist f' As))
      (s2 : _ -> Comp (list (f' a)))
      filter_rest ,
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist f' (a :: As) => f (ilist_hd x) && filter_rest x) l))
                  (l <- Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter f l));
                   ret (filter filter_rest l)).
  Proof.
    split; induction s1; unfold Join_Comp_Lists in *; simpl in *; intros; eauto.
    - simplify with monad laws; rewrite refineEquiv_bind_unit;
      reflexivity.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHs1 _ (BindComputes _ (fun x => ret (filter filter_rest x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, c'; eauto.
    - intros v Comp_v;  computes_to_inv; subst; eauto.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose proof (IHs1 _ (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      rewrite filter_app, filter_map; simpl; eauto.
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, H'; eauto.
  Qed.

  Corollary filter_join_ilist_hd
            {A}
            {a}
            {As}
            (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s1 : list (ilist f' As))
      (s2 : _ -> Comp (list (f' a))),
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist f' (a :: As) => f (ilist_hd x)) l))
                  (Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter f l))).
  Proof.
    intros; pose proof (filter_and_join_ilist_hd f s1 s2 (fun _ => true)).
    setoid_rewrite filter_and in H; setoid_rewrite filter_true in H.
    setoid_rewrite H; eauto; setoid_rewrite refineEquiv_unit_bind; reflexivity.
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

  Corollary refine_Query_For_In_Find_snd'
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
        -> refine (l <- CallBagMethod idx BagEnumerate r_n ();
                   List_Query_In (filter (fun tup : ilist (@Tuple) [_] => filter_dec (ilist_hd tup)) (Build_single_Tuple_list (snd l)))
                                 resultComp)
                  (l <- CallBagMethod idx BagFind r_n search_pattern;
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
    reflexivity.
  Qed.

  Corollary refine_Query_For_In_Find_single
            (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
             search_pattern
             (resultComp : _ -> Comp (list ResultT))
             filter_rest,
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (filter (fun a : ilist (@Tuple) [_] => BagMatchSearchTerm _ search_pattern (ilist_hd a) && filter_rest a) (Build_single_Tuple_list (snd l)))
                              resultComp)
               (l <- CallBagMethod idx BagFind r_n search_pattern;
                List_Query_In (filter filter_rest (Build_single_Tuple_list (snd l))) resultComp).
  Proof.
    unfold CallBagMethod; simpl; intros.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
    setoid_rewrite <- filter_Build_single_Tuple_list; rewrite filter_and;
    f_equiv.
  Qed.

  Add Parametric Morphism
      (A : Type)
      (f : A -> Type)
      (As : list A)
      (a : A)
      (l' : list (ilist f As))
  : (@Join_Comp_Lists A f As a l')
      with signature
      (pointwise_relation _ refineEquiv) ==> refineEquiv
        as refineEquiv_Join_Comp_Lists.
  Proof.
    unfold pointwise_relation; simpl; intros.
    induction l'; unfold Join_Comp_Lists; simpl.
    - reflexivity.
    - rewrite H; setoid_rewrite IHl'; reflexivity.
  Qed.

  Lemma Join_Comp_Lists_apply_f
        {A B C : Type}
        {f : A -> Type}
  : forall (As : list A)
           (a : A)
           (l : list (ilist f As))
           (c : ilist f As -> Comp (list (f a)))
           (c' : B -> Comp C) (f' : list (ilist f (a :: As)) -> B),
      refineEquiv (l' <- Join_Comp_Lists l c;
                   c' (f' l'))
                  (l' <- (l' <- Join_Comp_Lists l c; ret (f' l'));
                   c' l').
  Proof.
    split; rewrite refineEquiv_bind_bind;
    setoid_rewrite refineEquiv_bind_unit;
    intros v Comp_v;  computes_to_inv;
    try econstructor; eauto.
  Qed.

  Lemma refine_Join_Comp_Lists_filter_search_term_snd
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           headings
           idx'
           search_pattern
           (resultComp : ilist (@Tuple) (_ :: headings) -> Comp (list ResultT))
           filter_rest
           cl,
      refine (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist (@Tuple) (_ :: headings) => BagMatchSearchTerm _ search_pattern (ilist_hd a) && filter_rest a) l')
                            resultComp)
             (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagFind r_n search_pattern;
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    setoid_rewrite Join_Comp_Lists_apply_f
    with (c' := fun l =>  List_Query_In l _).
    setoid_rewrite (refineEquiv_bind_bind) at 2;
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    setoid_rewrite refineEquiv_unit_bind; simpl.
    rewrite (filter_and_join_ilist_hd
               (As := headings) (f' := @Tuple)
               (BagMatchSearchTerm _ search_pattern)
               cl
               (fun _ : ilist (@Tuple) headings =>
                  {l : list Tuple |
                   EnsembleIndexedListEquivalence (GetIndexedRelation r_n idx') l})) by eauto.
    simplify with monad laws; f_equiv.
  Qed.

  Corollary refine_Join_Comp_Lists_filter_search_term_snd'
            (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx idx'
           search_pattern
           (resultComp : ilist (@Tuple) [_; _] -> Comp (list ResultT))
           filter_rest,
      refine (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist (@Tuple) [_ ; _] => BagMatchSearchTerm _ search_pattern (ilist_hd a) && filter_rest a) l')
                            resultComp)
             (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagFind r_n search_pattern;
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; f_equiv; intro.
    apply refine_Join_Comp_Lists_filter_search_term_snd.
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

  Lemma filter_and_join_ilist_hd_dep
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall
      (f : ilist f' As -> f' a -> bool)
      (s1 : list (ilist f' As))
      (s2 : _ -> Comp (list (f' a)))
      filter_rest,
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist f' (a :: As) => f (ilist_tl x) (ilist_hd x) && filter_rest x) l))
                  (l <- Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter (f a) l));
                   ret (filter filter_rest l)).
  Proof.
    split; induction s1; unfold Join_Comp_Lists in *; simpl in *; intros; eauto.
    - simplify with monad laws; rewrite refineEquiv_bind_unit; reflexivity.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHs1 _ (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, c'; eauto.
    - intros v Comp_v;  computes_to_inv; subst; eauto.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose proof (IHs1 _ (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      rewrite filter_app, filter_map; simpl; eauto.
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, H'; eauto.
  Qed.

  Lemma refine_Join_Comp_Lists_filter_search_term_snd_dep
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           headings
           idx'
           (search_pattern : _ -> _)
           (resultComp : ilist (@Tuple) (_ :: headings) -> Comp (list ResultT))
           filter_rest
           (cl : list (ilist (@Tuple) headings)),
      refine (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist (@Tuple) (_ :: headings) => BagMatchSearchTerm _ (search_pattern (ilist_tl a)) (ilist_hd a) && filter_rest a) l')
                            resultComp)
             (l' <- (Join_Comp_Lists cl
                                     (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    setoid_rewrite Join_Comp_Lists_apply_f
    with (c' := fun l =>  List_Query_In l _).
    setoid_rewrite (refineEquiv_bind_bind) at 2;
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    setoid_rewrite refineEquiv_unit_bind; simpl.
    rewrite filter_and_join_ilist_hd_dep with
    (f := fun tup =>  (BagMatchSearchTerm
                         (ith_Bounded' relName (qschemaSchemas qs_schema)
                                       (nth_error_map relName (ibound idx')
                                                      (qschemaSchemas qs_schema) (boundi idx'))
                                       (ith_error BagIndexKeys (ibound idx')))
                         (search_pattern tup))).
    simplify with monad laws; f_equiv.
  Qed.

  Lemma realizeable_Enumerate
  : forall
      (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
      (r_o : UnConstrQueryStructure qs_schema)
      idx,
      DelegateToBag_AbsR r_o r_n ->
      exists v : list Tuple,
        refine
          (l <- CallBagMethod idx BagEnumerate r_n ();
           ret (snd l))
          (ret v).
  Proof.
    intros; destruct H as [r_o_eq H]; destruct (H idx) as [l l_eqv].
    rewrite (r_o_eq idx) in l_eqv.
    Local Transparent CallBagMethod.
    eexists l; unfold CallBagMethod; simpl; simplify with monad laws.
    computes_to_econstructor;  computes_to_inv; subst; eauto.
  Qed.

  Lemma realizeable_Find
  : forall
      (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
      (r_o : UnConstrQueryStructure qs_schema)
      idx st,
      DelegateToBag_AbsR r_o r_n ->
      exists v : list Tuple,
        refine (l <- CallBagMethod idx BagFind r_n st;
                ret (snd l))
               (ret v).
  Proof.
    intros; destruct H as [r_o_eq H]; destruct (H idx) as [l l_eqv].
    rewrite (r_o_eq idx) in l_eqv.
    eexists (filter _ l); unfold CallBagMethod; simpl; eauto.
    computes_to_econstructor; eauto.
  Qed.

  Corollary refine_Join_Comp_Lists_filter_search_term_snd_dep'
            (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx idx'
           (search_pattern : _ -> _)
           (resultComp : ilist (@Tuple) [_; _] -> Comp (list ResultT))
           filter_rest,
      refine (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist (@Tuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist_tl a)) (ilist_hd a) && filter_rest a) l')
                            resultComp)
             (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; f_equiv; intro;
    apply refine_Join_Comp_Lists_filter_search_term_snd_dep.
  Qed.

  Lemma refine_Join_Comp_Lists_filter_search_term_fst
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx
           heading
           cl
           (search_pattern : _)
           (resultComp : ilist (@Tuple) [heading ; _] -> Comp (list ResultT))
           (cl_realizable : forall a, exists v, computes_to (cl a) v)
           filter_rest,
      refine (l <- CallBagMethod idx BagEnumerate r_n ();
              l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) cl;
              List_Query_In (filter (fun a : ilist (@Tuple) [_ ; _] => (BagMatchSearchTerm _ search_pattern (ilist_hd (ilist_tl a)) && filter_rest a)) l')
                            resultComp)
             (l <- CallBagMethod idx BagFind r_n search_pattern;
              l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) cl;
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    f_equiv; unfold pointwise_relation; intros.
    setoid_rewrite Join_Comp_Lists_apply_f
    with (c' := fun l =>  List_Query_In l resultComp).
    setoid_rewrite (refineEquiv_bind_bind) at 2;
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    rewrite (filter_and_join_ilist_tail
               (fun a0 : ilist (@Tuple) [_] =>_ (ilist_hd a0))
               (Build_single_Tuple_list a)) by eauto.
    simplify with monad laws; f_equiv.
    unfold Build_single_Tuple_list; simpl;
    repeat rewrite filter_map; f_equiv.
  Qed.


  Require Import Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements.

  Lemma refineEquiv_Join_Comp_Lists_Build_single_Tuple_list
  : forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx,
      refineEquiv (Join_Comp_Lists [inil (@Tuple)]
                                   (fun _ : ilist (@Tuple) [] =>
                                      l <- CallBagMethod idx BagEnumerate r_n ();
                                    ret (snd l)))
                  (l <- CallBagMethod idx BagEnumerate r_n ();
                   ret (Build_single_Tuple_list (snd l))) .
  Proof.
    unfold Join_Comp_Lists, Build_single_Tuple_list; simpl; intros;
    repeat setoid_rewrite refineEquiv_bind_bind;
    repeat setoid_rewrite refineEquiv_bind_unit; f_equiv.
    intros u.
    rewrite app_nil_r; reflexivity.
  Qed.

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
                     (l <- (CallBagMethod idx BagDelete r_n search_pattern);
                      ret (snd l)).
  Proof.
    intros; setoid_rewrite DeletedTuplesFor; auto.
    rewrite refine_Query_In_Enumerate by eauto.
    setoid_rewrite refine_List_Query_In_Where.
    instantiate (1 := _).
    simpl in *.
    rewrite (refineEquiv_Join_Comp_Lists_Build_single_Tuple_list r_n idx).
    setoid_rewrite refineEquiv_bind_bind at 1.
    setoid_rewrite refineEquiv_bind_bind at 1.
    setoid_rewrite refineEquiv_bind_unit at 1.
    setoid_rewrite <- refineEquiv_bind_bind at 1.
    rewrite (refine_Query_For_In_Find_snd' H _ H0).
    setoid_rewrite refine_List_Query_In_Return.
    unfold Build_single_Tuple_list; setoid_rewrite map_map; simpl.
    setoid_rewrite map_id.
    unfold CallBagMethod; simpl; simplify with monad laws;
    setoid_rewrite refineEquiv_bind_bind;
    setoid_rewrite refineEquiv_bind_unit; simpl;
    f_equiv; intro.
    refine pick val _; eauto.
    reflexivity.
  Qed.

  Lemma NoDup_filter {A} :
    forall (f : A -> bool)
           (l : list A),
      NoDup l
      -> NoDup (filter f l).
  Proof.
    induction l; simpl.
    - constructor.
    - case_eq (f a); simpl; intros.
      + inversion H0; constructor; eauto.
        subst; unfold not; intros H1;
        apply filter_In in H1; intuition.
      + inversion H0; eauto.
  Qed.

  Lemma NoDup_filter_map {A} :
    forall (f : A -> bool)
           (l : list _),
      NoDup (map elementIndex l)
      -> NoDup
           (map elementIndex
                (filter (fun a => f (indexedElement a)) l)) .
  Proof.
    induction l; simpl.
    - constructor.
    - case_eq (f (indexedElement a)); simpl; intros; inversion H0; subst; eauto.
      constructor; eauto.
      unfold not; intros; apply H3.
      revert H1; clear; induction l; simpl.
      + eauto.
      + case_eq (f (indexedElement a0)); simpl; intros; intuition.
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
                (l <- (CallBagMethod idx BagDelete r_n search_pattern);
                 ret (UpdateIndexedRelation r_n idx (fst l))).
  Proof.
    intros.
    computes_to_constructor;  computes_to_inv.
    unfold CallBagMethod in *; simpl in *;  computes_to_inv; subst.
    simpl.
    unfold DelegateToBag_AbsR; split; intros.
    - destruct (BoundedString_eq_dec idx idx0); subst.
      + unfold GetUnConstrRelation, UpdateUnConstrRelation;
        rewrite ith_replace_BoundIndex_eq.
        unfold GetIndexedRelation, UpdateIndexedRelation;
          rewrite i2th_replace_BoundIndex_eq.
        f_equal; eauto.
        * eapply H.
        * apply Extensionality_Ensembles. unfold Same_set, Included, In;
            intuition; rewrite <- H0 in *;
            eapply dec_decides_P; eauto.
      + unfold GetUnConstrRelation, UpdateUnConstrRelation;
        rewrite ith_replace_BoundIndex_neq by eauto using string_dec.
        unfold GetIndexedRelation, UpdateIndexedRelation;
          rewrite i2th_replace_BoundIndex_neq by eauto using string_dec.
        apply H.
    - destruct H.
      destruct (BoundedString_eq_dec idx idx0); subst.
      + rewrite get_update_unconstr_eq.
        destruct (H2 idx0) as [l [[bnd fresh_bnd] [l' [l'_eq [l_eqv NoDup_l']]]]].
        exists (filter (fun a => negb (dec a)) l); split.
        * exists bnd; unfold EnsembleDelete, UnConstrFreshIdx; intros.
          inversion H3; subst; eauto.
        * unfold UnIndexedEnsembleListEquivalence;
          exists (filter (fun a => negb (dec (indexedElement a))) l'); split; eauto.
          rewrite <- l'_eq; rewrite filter_map; reflexivity.
          intuition.
          apply filter_In; split.
          eapply l_eqv; inversion H3; eauto.
          inversion H3; subst; rewrite (proj2 (Decides_false _ _)); eauto.
          rewrite filter_In in H3; intuition; constructor;
          [ apply l_eqv; eauto
          | case_eq (dec (indexedElement x)); intros H'; rewrite H' in H5;
            try discriminate;
            eapply Decides_false in H'; eauto ].
          eapply NoDup_filter_map with (f := fun a => negb (dec a)); eauto.
      + rewrite get_update_unconstr_neq; eauto.
  Qed.

  Lemma refine_BagADT_QSInsert :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                t,
           refine
             (u <- { freshIdx | UnConstrFreshIdx (GetUnConstrRelation r_o idx) freshIdx };
              {r_n' |
               DelegateToBag_AbsR
                 (UpdateUnConstrRelation r_o idx (
                                           EnsembleInsert
                                             {| indexedElement := t; elementIndex := u |}
                                             (GetUnConstrRelation r_o idx))) r_n'})
             (l <- (CallBagMethod idx BagInsert r_n t);
              ret (UpdateIndexedRelation r_n idx (fst l))).
  Proof.
    intros; unfold CallBagMethod, DelegateToBag_AbsR; simpl; destruct H as [H H'].
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    rewrite H.
    apply refine_bind_pick; intros.
    unfold GetUnConstrRelation, UpdateUnConstrRelation in *;
      unfold GetIndexedRelation, UpdateIndexedRelation in *;
      refine pick val _; try reflexivity; try split;
      intros; destruct (BoundedString_eq_dec idx idx0); subst.
    - rewrite ith_replace_BoundIndex_eq; rewrite i2th_replace_BoundIndex_eq.
      unfold Add, EnsembleInsert; apply Extensionality_Ensembles; split;
      unfold Included; intros; unfold In in *; destruct H1.
      + rewrite H1; apply Union_intror; intuition.
      + apply Union_introl; unfold In; exact H1.
      + right; unfold In in H1; exact H1.
      + left; unfold In in H1; eapply Singleton_ind; eauto; symmetry; exact H1.
    - rewrite ith_replace_BoundIndex_neq by eauto using string_dec;
      rewrite i2th_replace_BoundIndex_neq by eauto using string_dec; apply H.
    - rewrite ith_replace_BoundIndex_eq.
      destruct (H' idx0) as [l [[bnd fresh_bnd] [l' [l'_eq [l_eqv NoDup_l']]]]].
      exists (t :: l); split.
      + exists (S a); unfold UnConstrFreshIdx in *; intros.
               unfold EnsembleInsert in H1; destruct H1.
               * rewrite H1; simpl; omega.
               * apply H0 in H1; omega.
               + unfold UnIndexedEnsembleListEquivalence;
                 exists ({| indexedElement := t; elementIndex := a |} :: l'); intuition.
                 * simpl; rewrite l'_eq; trivial.
                 * simpl; destruct H1;
                   [ left; symmetry; exact H1 | right; apply l_eqv; rewrite H; apply H1 ].
                 * unfold EnsembleInsert; destruct H1;
                   [ rewrite <- H1; left; trivial |
                     right; rewrite <- H; apply l_eqv in H1; unfold In in H1; exact H1 ].
                 * simpl; apply NoDup_cons;
                   [ unfold not; intros;
                     apply in_map_iff in H1; destruct H1; destruct H1;
                     apply l_eqv in H2; rewrite <- H in H0; unfold UnConstrFreshIdx in H0;
                     unfold In in H2; apply H0 in H2; omega | exact NoDup_l' ].
               - rewrite ith_replace_BoundIndex_neq.
                 apply H'. apply string_dec. unfold not in *; intros; rewrite H1 in n; intuition.
  Qed.

Corollary refine_Join_Comp_Lists_filter_filter_search_term_snd_dep'
          (ResultT : Type) :
  forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
         idx idx'
         (search_pattern : _ -> _)
         (resultComp : ilist (@Tuple) [_; _] -> Comp (list ResultT))
         filter_rest st,
    refine (cl <- CallBagMethod idx BagFind r_n st;
            l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                   (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                    ret (snd l)));
            List_Query_In (filter (fun a : ilist (@Tuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist_tl a)) (ilist_hd a) && filter_rest a) l')
                          resultComp)
           (cl <- CallBagMethod idx BagFind r_n st;
            l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                   (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                    ret (snd l)));
            List_Query_In (filter filter_rest l') resultComp).
Proof.
  intros; f_equiv; intro;
  apply refine_Join_Comp_Lists_filter_search_term_snd_dep.
Qed.

End BagsQueryStructureRefinements.
