Require Export Coq.Lists.List Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.Common.ilist2
        Fiat.Common.i2list.
Require Import Coq.Bool.Bool
        Coq.Strings.String
        Coq.Structures.OrderedTypeEx
        Coq.Arith.Arith
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

  Import Coq.Vectors.VectorDef.VectorNotations.
  
  Variable qs_schema : RawQueryStructureSchema.
  Variable BagIndexKeys :
    ilist2 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns))
          (qschemaSchemas qs_schema).

  Lemma i2th_Bounded_Initialize_IndexedQueryStructure {n}
  : forall ns indices v idx,
      computes_to (@Initialize_IndexedQueryStructure n ns indices) v
      -> i2th v idx = Empty_set _.
  Proof.
    induction ns.
    - intros; inversion idx.
    - intros; revert ns IHns indices v H; pattern n, idx.
      match goal with
        |- ?P n idx => simpl; apply (@Fin.caseS P); intros; simpl in *
      end.
      + unfold CallBagConstructor in H; simpl in H; computes_to_inv.
        subst; simpl in *; eauto.
      + computes_to_inv; subst.
        eapply IHns; eauto.
  Qed.

  Corollary refine_QSEmptySpec_Initialize_IndexedQueryStructure
    : refine {nr' | DelegateToBag_AbsR (imap2 rawRel (Build_EmptyRelations (qschemaSchemas qs_schema))) nr'}
             (@Initialize_IndexedQueryStructure _ (qschemaSchemas qs_schema) BagIndexKeys).
  Proof.
    intros v Comp_v.
    computes_to_econstructor.
    unfold IndexedQueryStructure, DelegateToBag_AbsR, GetIndexedRelation.
    unfold GetUnConstrRelation.
    unfold DropQSConstraints, QSEmptySpec; split.
    intros; simpl; rewrite <- ith_imap2, ith_Bounded_BuildEmptyRelations,
                   i2th_Bounded_Initialize_IndexedQueryStructure; eauto.
    intros; eexists List.nil;
    intros; simpl; rewrite <- ith_imap2, ith_Bounded_BuildEmptyRelations.
    split; simpl; intros.
    - exists 0; unfold UnConstrFreshIdx; intros; intuition.
    - eexists List.nil; intuition eauto.
      + inversion H.
      + inversion H.
      + econstructor.
  Qed.

  Definition UpdateIndexedRelation
             (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx newRel
  : IndexedQueryStructure qs_schema BagIndexKeys  :=
    replace2_Index2 _ _ r_n idx newRel.

  Lemma get_update_indexed_eq :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx newRel,
      GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx = newRel.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i2th_replace_Index_eq; eauto using string_dec.
  Qed.

  Lemma get_update_indexed_neq :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx idx' newRel,
      idx <> idx'
      -> GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx' =
         GetIndexedRelation r_n idx'.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i2th_replace_Index_neq; eauto using string_dec.
  Qed.

  Lemma refine_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : Fin.t _)
                (resultComp : RawTuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- Join_Comp_Lists [ inil2 ]
                     (fun _ =>
                        l <- CallBagMethod idx BagEnumerate r_n ();
                      (ret (snd l)));
                   (List_Query_In l (fun tup : ilist2 (B := @RawTuple) [ _ ]=> resultComp (ilist2_hd tup)))) .
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
      -> forall (idx : Fin.t _)
                (resultComp : RawTuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- Join_Filtered_Comp_Lists [ inil2 ]
                     (fun _ =>
                        l <- CallBagMethod idx BagEnumerate r_n ();
                      (ret (snd l)))
                     (fun _ => true);
                   (List_Query_In l (fun tup : ilist (B := @RawTuple) [ _ ]=> resultComp (ilist_hd tup)))) .
  Proof.
    intros; rewrite refine_Query_In_Enumerate by eauto.
    rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Local Transparent Query_For.

  Lemma refine_For_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : Fin.t _)
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
        {n}
        headings
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : Fin.t _)
             (resultComp : ilist2 (n := n) (B:= @RawTuple) headings
                           -> RawTuple
                           -> Comp (list ResultT))
             l,
        refine (List_Query_In l (fun tup : ilist2 (B := @RawTuple) headings =>
                                   UnConstrQuery_In r_o idx (resultComp tup)))
               (l' <- (Join_Comp_Lists l (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                          ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_tl tup_pair) (ilist2_hd tup_pair)))).
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
      forall (idx idx' : Fin.t _)
             (resultComp : RawTuple -> RawTuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist2_hd tup))))
               (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_hd (ilist2_tl tup_pair)) (ilist2_hd tup_pair)))).
  Proof.
    intros.
    f_equiv; simpl; intro.
    eapply refine_Join_Query_In_Enumerate' with
    (l := Build_single_Tuple_list (snd a)); eauto.
  Qed.

  Corollary refine_Filtered_Join_Query_In_Enumerate'
            {n}
        headings
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : Fin.t _)
             (resultComp : ilist2 (n := n) ( B:= @RawTuple) headings
                           -> RawTuple
                           -> Comp (list ResultT))
             l,
        refine (List_Query_In l (fun tup : ilist2 (B:= @RawTuple) headings =>
                                   UnConstrQuery_In r_o idx (resultComp tup)))
               (l' <- (Join_Filtered_Comp_Lists l (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                                   ret (snd l))
                                                (fun _ => true));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_tl tup_pair) (ilist2_hd tup_pair)))).
  Proof.
    intros; rewrite refine_Join_Query_In_Enumerate' by eauto.
    rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Corollary refine_Filtered_Join_Query_In_Enumerate
            (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : Fin.t _)
             (resultComp : RawTuple -> RawTuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist2_hd tup))))
               (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Filtered_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l))
                                       (fun _ => true));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_hd (ilist2_tl tup_pair)) (ilist2_hd tup_pair)))).
  Proof.
    intros; rewrite refine_Join_Query_In_Enumerate by eauto.
    f_equiv; intro; rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  (*Lemma refine_Join_Enumerate_Swap
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
                List_Query_In l' (fun tup_pair => (resultComp (icons _ (ilist2_hd (ilist2_tl tup_pair)) (icons _ (ilist2_hd tup_pair) (inil _)))))).
  Proof.
  Admitted. *)

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
      forall (idx : Fin.t _)
             filter_dec
             search_pattern
             (resultComp : RawTuple -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (BagMatchSearchTerm (ith2 BagIndexKeys idx) search_pattern)
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

  Lemma refine_Join_Comp_Lists_To_Find {n}
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall {headings}
                (l1 : list (ilist2 (n := n) (B:= @RawTuple) headings))
                (idx : Fin.t _)
                search_pattern,
           refine (Join_Filtered_Comp_Lists l1
                                            (fun _ =>
                                               l <- CallBagMethod idx BagEnumerate r_n ();
                                             ret (snd l))
                                            (fun a => BagMatchSearchTerm (ith2  BagIndexKeys idx) search_pattern (ilist2_hd a) && true))
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

  Lemma refine_Join_Comp_Lists_To_Find_dep {n}
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall {headings}
                (l1 : list (ilist2 (n := n) (B:= @RawTuple) headings))
                (idx :Fin.t _)
                (search_pattern : ilist2 (B:= @RawTuple) headings -> _),
           refine (Join_Filtered_Comp_Lists l1
                                            (fun _ =>
                                               l <- CallBagMethod idx BagEnumerate r_n ();
                                             ret (snd l))
                                            (fun a => BagMatchSearchTerm (ith2  BagIndexKeys idx)
                                                                         (search_pattern (ilist2_tl a)) (ilist2_hd a) && true))
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
           {n}
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (ilist2 (n := n) (B := f) As))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist2 (B := f) (a :: As) => P (ilist2_tl ab)) :=
    { dec ab := dec (ilist2_tl ab) }.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist2_tl a0)).
  Defined.

  Instance DecideableEnsemblePair_head
           {n}
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (f a))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist2 (n := S n) (B := f) (a :: As) => P (ilist2_hd ab)) :=
    { dec ab := dec (ilist2_hd ab) }.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist2_hd a0)).
  Defined.

  Lemma Join_Comp_Lists_nil
        {n}
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall (s2 : _ -> Comp (list (f' a))),
      refineEquiv (Join_Comp_Lists (n := n) (As := As) (a := a) (List.nil) s2) (ret (List.nil)).
  Proof.
    unfold Join_Comp_Lists; simpl; try reflexivity.
  Qed.

  Lemma filter_and_join_ilist2_hd
        {n}
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s1 : list (ilist2 (n := n) (B := f') As))
      (s2 : _ -> Comp (list (f' a)))
      filter_rest ,
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist2 (B := f') (a :: As) => f (ilist2_hd x) && filter_rest x) l))
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

  Corollary filter_join_ilist2_hd
            {n}
            {A}
            {a}
            {As}
            (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s1 : list (ilist2 (B := f') As))
      (s2 : _ -> Comp (list (f' a))),
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist2 (n := S n) (B := f') (a :: As) => f (ilist2_hd x)) l))
                  (Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter f l))).
  Proof.
    intros; pose proof (filter_and_join_ilist2_hd f s1 s2 (fun _ => true)).
    setoid_rewrite filter_and in H; setoid_rewrite filter_true in H.
    setoid_rewrite H; eauto; setoid_rewrite refineEquiv_unit_bind; reflexivity.
  Qed.

  Lemma filter_Build_single_Tuple_list
        {heading}
        (l : list (@RawTuple heading))
        (filter_dec : @RawTuple heading -> bool)
  : filter (fun tup : ilist2 (B:= @RawTuple) [_] => filter_dec (ilist2_hd tup)) (Build_single_Tuple_list l) = Build_single_Tuple_list (filter filter_dec l).
  Proof.
    induction l; simpl; eauto.
    destruct (filter_dec a); simpl; eauto.
    f_equal; eauto.
  Qed.

  Corollary refine_Query_For_In_Find_snd'
            (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      ->
      forall (idx :Fin.t _)
             (filter_dec : RawTuple -> bool)
             search_pattern
             (resultComp : _ -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (BagMatchSearchTerm (ith2  BagIndexKeys idx) search_pattern)
        -> refine (l <- CallBagMethod idx BagEnumerate r_n ();
                   List_Query_In (filter (fun tup : ilist2 (B:= @RawTuple) [_] => filter_dec (ilist2_hd tup)) (Build_single_Tuple_list (snd l)))
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
      forall (idx :Fin.t _)
             search_pattern
             (resultComp : _ -> Comp (list ResultT))
             filter_rest,
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_] => BagMatchSearchTerm _ search_pattern (ilist2_hd a) && filter_rest a) (Build_single_Tuple_list (snd l)))
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
      (n : nat) 
      (A : Type)
      (f : A -> Type)
      (As : Vector.t A n)
      (a : A)
      (l' : list (ilist2 (B := f) As))
  : (@Join_Comp_Lists n A f As a l')
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
        {n}
        {A B C : Type}
        {f : A -> Type}
  : forall (As : Vector.t A n)
           (a : A)
           (l : list (ilist2 (B := f) As))
           (c : ilist2 (B := f) As -> Comp (list (f a)))
           (c' : B -> Comp C) (f' : list (ilist2 (B := f) (a :: As)) -> B),
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
        {n}
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           headings
           idx'
           search_pattern
           (resultComp : ilist2 (B:= @RawTuple) (_ :: headings) -> Comp (list ResultT))
           filter_rest
           cl,
      refine (l' <- (Join_Comp_Lists (n := n) cl
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) (_ :: headings) => BagMatchSearchTerm _ search_pattern (ilist2_hd a) && filter_rest a) l')
                            resultComp)
             (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagFind r_n search_pattern;
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    match goal with
      |- refine (l' <- Join_Comp_Lists ?l ?c; (@?f l')) _ =>
      setoid_rewrite (Join_Comp_Lists_apply_f l c) with (c' := fun l => List_Query_In l _)
    end.
    setoid_rewrite refineEquiv_unit_bind.
    rewrite (filter_and_join_ilist2_hd
               (As := headings) (f' := @RawTuple)
               (BagMatchSearchTerm _ search_pattern)
               cl
               (fun _ : ilist2 (B:= @RawTuple) headings =>
                  {l : list RawTuple |
                   EnsembleIndexedListEquivalence (GetIndexedRelation r_n idx') l})).
    simplify with monad laws; f_equiv.
  Qed.

  Corollary refine_Join_Comp_Lists_filter_search_term_snd'
            (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx idx'
           search_pattern
           (resultComp : ilist2 (B:= @RawTuple) [_; _] -> Comp (list ResultT))
           filter_rest,
      refine (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => BagMatchSearchTerm _ search_pattern (ilist2_hd a) && filter_rest a) l')
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

  Lemma filter_and_join_ilist2_hd_dep
        {n}
        {A}
        {a}
        {As : Vector.t A n}
        (f' : A -> Type)
  : forall
      (f : ilist2 (B := f') As -> f' a -> bool)
      (s1 : list (ilist2 (B := f') As))
      (s2 : _ -> Comp (list (f' a)))
      filter_rest,
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist2 (B := f') (a :: As) => f (ilist2_tl x) (ilist2_hd x) && filter_rest x) l))
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
        {n}
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           (headings : Vector.t _ n)
           idx'
           (search_pattern : _ -> _)
           (resultComp : ilist2 (B:= @RawTuple) (_ :: headings) -> Comp (list ResultT))
           filter_rest
           (cl : list (ilist2 (B:= @RawTuple) headings)),
      refine (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) (_ :: headings) => BagMatchSearchTerm _ (search_pattern (ilist2_tl a)) (ilist2_hd a) && filter_rest a) l')
                            resultComp)
             (l' <- (Join_Comp_Lists cl
                                     (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    match goal with
      |- refine (l' <- Join_Comp_Lists ?l ?c; (@?f l')) _ =>
      setoid_rewrite (Join_Comp_Lists_apply_f l c) with (c' := fun l => List_Query_In l _)
    end.
    setoid_rewrite refineEquiv_unit_bind.
    rewrite filter_and_join_ilist2_hd_dep with
    (f := fun tup =>  (BagMatchSearchTerm (ith2 BagIndexKeys idx')
                                          (search_pattern tup))).
    simplify with monad laws; f_equiv.
  Qed.

  Lemma realizeable_Enumerate
  : forall
      (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
      (r_o : UnConstrQueryStructure qs_schema)
      idx,
      DelegateToBag_AbsR r_o r_n ->
      exists v : list RawTuple,
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
      exists v : list RawTuple,
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
           (resultComp : ilist2 (B:= @RawTuple) [_; _] -> Comp (list ResultT))
           filter_rest,
      refine (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist2_tl a)) (ilist2_hd a) && filter_rest a) l')
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
           (resultComp : ilist2 (B:= @RawTuple) [heading ; _] -> Comp (list ResultT))
           (cl_realizable : forall a, exists v, computes_to (cl a) v)
           filter_rest,
      refine (l <- CallBagMethod idx BagEnumerate r_n ();
              l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) cl;
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => (BagMatchSearchTerm _ search_pattern (ilist2_hd (ilist2_tl a)) && filter_rest a)) l')
                            resultComp)
             (l <- CallBagMethod idx BagFind r_n search_pattern;
              l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) cl;
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    f_equiv; unfold pointwise_relation; intros.
    match goal with
      |- refine (l' <- Join_Comp_Lists ?l ?c; (@?f l')) _ =>
      setoid_rewrite (Join_Comp_Lists_apply_f l c) with (c' := fun l => List_Query_In l _)
    end.
    setoid_rewrite <- refineEquiv_unit_bind.
    setoid_rewrite (filter_and_join_ilist_tail
               (fun a0 : ilist2 (B:= @RawTuple) [_] =>_ (ilist2_hd a0))
               (Build_single_Tuple_list a)); eauto.
    simplify with monad laws; f_equiv.
    unfold Build_single_Tuple_list; simpl;
    repeat rewrite filter_map; f_equiv.
    setoid_rewrite refineEquiv_bind_bind; setoid_rewrite refineEquiv_unit_bind;
    reflexivity.
  Qed.

  Require Import Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements.

  Lemma refineEquiv_Join_Comp_Lists_Build_single_Tuple_list
  : forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx,
      refineEquiv (Join_Comp_Lists [inil2 (B := @RawTuple)]
                                   (fun _ : ilist2 (B:= @RawTuple) [] =>
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
      -> forall (idx :Fin.t _)
                (DT : Ensemble RawTuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (BagMatchSearchTerm (ith2  BagIndexKeys idx) search_pattern)
           -> refine {x : list RawTuple |
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
      -> forall (idx :Fin.t _)
                (DT : Ensemble RawTuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (BagMatchSearchTerm (ith2  BagIndexKeys idx) search_pattern)
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
    - destruct (fin_eq_dec idx idx0); subst.
      + unfold GetUnConstrRelation, UpdateUnConstrRelation;
        rewrite ith_replace2_Index_eq.
        unfold GetIndexedRelation, UpdateIndexedRelation;
          rewrite i2th_replace_Index_eq.
        f_equal; eauto.
        * eapply H.
        * apply Extensionality_Ensembles. unfold Same_set, Included, In;
            intuition; rewrite <- H0 in *;
            eapply dec_decides_P; eauto.
      + unfold GetUnConstrRelation, UpdateUnConstrRelation;
        rewrite ith_replace2_Index_neq by eauto using string_dec.
        unfold GetIndexedRelation, UpdateIndexedRelation;
          rewrite i2th_replace_Index_neq by eauto using string_dec.
        apply H.
    - destruct H.
      destruct (fin_eq_dec idx idx0); subst.
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
      -> forall (idx :Fin.t _)
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
      intros; destruct (fin_eq_dec idx idx0); subst.
    - rewrite ith_replace2_Index_eq; rewrite i2th_replace_Index_eq.
      unfold Add, EnsembleInsert; apply Extensionality_Ensembles; split;
      unfold Included; intros; unfold In in *; destruct H1.
      + rewrite H1; apply Union_intror; intuition.
      + apply Union_introl; unfold In; exact H1.
      + right; unfold In in H1; exact H1.
      + left; unfold In in H1; eapply Singleton_ind; eauto; symmetry; exact H1.
    - rewrite ith_replace2_Index_neq by eauto using string_dec;
      rewrite i2th_replace_Index_neq by eauto using string_dec; apply H.
    - rewrite ith_replace2_Index_eq.
      destruct (H' idx0) as [l [[bnd fresh_bnd] [l' [l'_eq [l_eqv NoDup_l']]]]].
      exists (List.cons t l); split.
      + exists (S a); unfold UnConstrFreshIdx in *; intros.
               unfold EnsembleInsert in H1; destruct H1.
               * rewrite H1; simpl; omega.
               * auto with arith.
      + unfold UnIndexedEnsembleListEquivalence;
                 exists ({| indexedElement := t; elementIndex := a |} :: l')%list; intuition.
                 * simpl in *; rewrite l'_eq; trivial.
                 * simpl; destruct H1;
                   [ left; symmetry; exact H1 | right; apply l_eqv; rewrite H; apply H1 ].
                 * unfold EnsembleInsert; destruct H1;
                   [ rewrite <- H1; left; trivial |
                     right; rewrite <- H; apply l_eqv in H1; unfold In in H1; exact H1 ].
                 * simpl; apply NoDup_cons;
                   [ unfold not; intros;
                     apply in_map_iff in H1; destruct H1; destruct H1;
                     apply l_eqv in H2; rewrite <- H in H0; unfold UnConstrFreshIdx in H0;
                     unfold In in H2; apply H0 in H2; unfold GetNRelSchema in *; omega | exact NoDup_l' ].
    - rewrite ith_replace2_Index_neq; eauto.
  Qed.

Corollary refine_Join_Comp_Lists_filter_filter_search_term_snd_dep'
          (ResultT : Type) :
  forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
         idx idx'
         (search_pattern : _ -> _)
         (resultComp : ilist2 (B:= @RawTuple) [_; _] -> Comp (list ResultT))
         filter_rest st,
    refine (cl <- CallBagMethod idx BagFind r_n st;
            l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                   (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                    ret (snd l)));
            List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist2_tl a)) (ilist2_hd a) && filter_rest a) l')
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
