Require Export BagsInterface CountingListBags TreeBags Tuple Heading List Program ilist i2list.
Require Import String_as_OT IndexedEnsembles DecideableEnsembles.
Require Import Bool String OrderedTypeEx BagsOfTuples.
Require Import GeneralQueryRefinements.
Require Import QueryStructureNotations ListImplementation.
Require Import AdditionalLemmas AdditionalPermutationLemmas Arith BagADT.

Section BagsOfTuplesRefinements.

  Variable qs_schema : QueryStructureSchema.
  Definition Bag_index (ns : NamedSchema) :=
    list (@ProperAttribute (schemaHeading (relSchema ns))).

  Variable indices : ilist Bag_index (qschemaSchemas qs_schema).

  Definition IndexedQueryStructure
    := i2list (fun ns index => Rep (BagSpec (SearchTermFromAttributesMatcher index))) indices.

  Definition GetIndexedRelation (r_n : IndexedQueryStructure) idx
    := i2th_Bounded relName r_n idx.

  Definition CallBagMethod idx midx r_n :=
    Methods (BagSpec (SearchTermFromAttributesMatcher (ith_Bounded relName indices idx))) midx
            (GetIndexedRelation r_n idx).

  Definition DelegateToBag_AbsR
             (r_o : UnConstrQueryStructure qs_schema)
             (r_n : IndexedQueryStructure)
    := forall idx, GetUnConstrRelation r_o idx = GetIndexedRelation r_n idx.

  Fixpoint Initialize_IndexedQueryStructure
          (ns : list NamedSchema)
          (indices' : ilist Bag_index ns)
          {struct indices'}
  : Comp (i2list (fun ns index => Rep (BagSpec (SearchTermFromAttributesMatcher index))) indices')
    := match indices' return Comp (i2list _ indices') with
      | inil => ret (i2nil _ _)
      | icons ns ns' index indices'' =>
        c <- (Constructors
                (BagSpec (SearchTermFromAttributesMatcher index)) {|bindex := "EmptyBag" |} tt);
          cs <- (@Initialize_IndexedQueryStructure ns' indices'');
          ret (i2cons ns index c cs)

    end.

  Lemma refine_QSEmptySpec_Initialize_IndexedQueryStructure
        : refine {nr' | DelegateToBag_AbsR (DropQSConstraints (QSEmptySpec qs_schema)) nr'}
                 (Initialize_IndexedQueryStructure indices).
  Proof.
    intros v Comp_v.
    econstructor.
    unfold IndexedQueryStructure, DelegateToBag_AbsR, GetIndexedRelation.
  Admitted.

  Definition UpdateIndexedRelation (r_n : IndexedQueryStructure) idx newRel
  : IndexedQueryStructure :=
    replace_BoundedIndex2 relName r_n idx newRel.

  Lemma get_update_indexed_eq :
    forall (r_n : IndexedQueryStructure) idx newRel,
      GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx = newRel.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i2th_replace_BoundIndex_eq; eauto using string_dec.
  Qed.

  Lemma get_update_indexed_neq :
    forall (r_n : IndexedQueryStructure) idx idx' newRel,
      idx <> idx'
      -> GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx' =
      GetIndexedRelation r_n idx'.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i2th_replace_BoundIndex_neq; eauto using string_dec.
  Qed.

  Lemma refine_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o r_n,
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : BoundedString)
                (resultComp : Tuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                   List_Query_In (snd l) resultComp).
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
        heading
        (ResultT : Type) :
    forall r_o r_n,
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : BoundedString)
             (resultComp : Tuple -> Tuple -> Comp (list ResultT))
             l,
        refine (List_Query_In l (fun tup : @Tuple heading =>
                                   UnConstrQuery_In r_o idx (resultComp tup)))
               (l' <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                List_Query_In (Join_Lists l (snd l'))
                              (fun tup_pair => (resultComp (fst tup_pair) (snd tup_pair)))).
  Proof.
    intros.
    unfold List_Query_In; induction l; simpl.
    - intros v Comp_v; inversion_by computes_to_inv; subst; constructor.
    - setoid_rewrite IHl; rewrite refine_Query_In_Enumerate; eauto.
      unfold List_Query_In.
      setoid_rewrite refineEquiv_bind_bind at 1.
      setoid_rewrite refineEquiv_bind_bind at 2.
      intros v Comp_v; inversion_by computes_to_inv.
      rewrite map_app, map_map in H2; simpl in *.
      econstructor; eauto.
      apply flatten_CompList_app_inv in H2; destruct_ex; intuition.
      subst; repeat (econstructor; eauto).
  Qed.

  Corollary refine_Join_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o r_n,
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : Tuple -> Tuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                List_Query_In (snd l) (fun tup : Tuple =>
                                          UnConstrQuery_In r_o idx' (resultComp tup)))
               (l <- CallBagMethod idx {|bindex := "Enumerate" |} r_n ();
                l' <- CallBagMethod idx' {|bindex := "Enumerate" |} r_n ();
                List_Query_In (Join_Lists (snd l) (snd l'))
                              (fun tup_pair => (resultComp (fst tup_pair) (snd tup_pair)))).
  Proof.
    intros.
    f_equiv; simpl; intro.
    apply refine_Join_Query_In_Enumerate'; eauto.
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

  Local Transparent Query_For.

  Lemma refine_Query_For_In_Find
        (ResultT : Type)
  : forall r_o r_n,
      DelegateToBag_AbsR r_o r_n
      ->
      forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
             filter_dec
             search_pattern
             (resultComp : Tuple -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (SearchTermFromAttributesMatcher
                         (ith_Bounded relName indices idx) search_pattern)
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

  Lemma refine_Join_Lists_Where_snd
        (ResultT : Type) :
    forall r_n idx idx'
           (DT : Ensemble Tuple)
           (DT_Dec : DecideableEnsemble DT)
           search_pattern
           (resultComp : Tuple -> Tuple -> Comp (list ResultT)),
      ExtensionalEq (@dec _ _ DT_Dec)
                    (SearchTermFromAttributesMatcher
                       (ith_Bounded relName indices idx') search_pattern)
      -> refine (For (l <- CallBagMethod idx {| bindex := "Enumerate" |} r_n ();
                      l' <- CallBagMethod idx' {| bindex := "Enumerate" |} r_n ();
                      List_Query_In (Join_Lists (snd l) (snd l'))
                                    (fun tup_pair : Tuple * Tuple =>
                                       Where (DT (snd tup_pair))
                                             (resultComp (fst tup_pair) (snd tup_pair)))))

                (For (l <- CallBagMethod idx {| bindex := "Enumerate" |} r_n ();
                      l' <- CallBagMethod idx' {| bindex := "Find" |} r_n search_pattern;
                      List_Query_In (Join_Lists (snd l) (snd l'))
                                    (fun tup_pair : Tuple * Tuple =>
                                       (resultComp (fst tup_pair) (snd tup_pair))))).
  Proof.
    intros; repeat f_equiv; simpl; intro.
    setoid_rewrite refine_List_Query_In_Where with
    (P := fun tup_pair => DT (snd tup_pair)).
  Admitted.

  Lemma refine_List_Query_In_Return
        (ResultT : Type) :
    forall l,
      refine (List_Query_In l (@Query_Return ResultT) ) (ret l).
  Proof.
    unfold List_Query_In; induction l; simpl.
    - reflexivity.
    - simplify with monad laws; rewrite IHl; simplify with monad laws;
      reflexivity.
  Qed.

  Require Import GeneralDeleteRefinements.

  Lemma refine_BagADT_QSDelete_fst :
    forall r_o r_n,
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                (DT : Ensemble Tuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (SearchTermFromAttributesMatcher
                            (ith_Bounded relName indices idx) search_pattern)
           -> refine {x : list Tuple |
                      QSDeletedTuples r_o idx DT x}
                     (l <- (CallBagMethod idx {|bindex := "Delete" |} r_n search_pattern);
                      ret (snd l)).
  Proof.
      intros; setoid_rewrite DeletedTuplesFor; auto.
      rewrite refine_Query_In_Enumerate by eauto.
      setoid_rewrite refine_List_Query_In_Where.
      rewrite (refine_Query_For_In_Find H Query_Return H0).
      setoid_rewrite refine_List_Query_In_Return.
      unfold CallBagMethod; simpl; simplify with monad laws;
      setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
    Qed.

  Lemma refine_BagADT_QSDelete_snd :
    forall r_o r_n,
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : @BoundedString (map relName (qschemaSchemas qs_schema)))
                (DT : Ensemble Tuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (SearchTermFromAttributesMatcher
                            (ith_Bounded relName indices idx) search_pattern)
           -> refine
                {r_n' |
                 DelegateToBag_AbsR
                   (UpdateUnConstrRelation r_o idx (EnsembleDelete
                                                      (GetUnConstrRelation r_o idx)
                                                      DT)) r_n'}
                (l <- (CallBagMethod idx {|bindex := "Delete" |} r_n search_pattern);
                 ret (UpdateIndexedRelation r_n idx (fst l))).
  Proof.
  Admitted.


End BagsOfTuplesRefinements.

Section SharpenedBag.

  Context {heading : Heading}.
  Variable SearchTermTypePlus : Type.
  Variable UpdateTermTypePlus : Type.
  Variable BagTypePlus : Type.
  Variable RepInvPlus : BagTypePlus -> Prop.
  Variable ValidUpdatePlus : UpdateTermTypePlus -> Prop.

  Variable BagPlus : Bag BagTypePlus (@Tuple heading) SearchTermTypePlus UpdateTermTypePlus.
  Variable CorrectBagPlus : CorrectBag RepInvPlus ValidUpdatePlus BagPlus.

  Lemma refine_Empty_set_bempty :
    Empty_set IndexedElement ≃ benumerate bempty.
  Proof.
    split.
    - exists 1; unfold UnConstrFreshIdx; intros elements H; destruct H.
    - eexists nil; simpl; intuition.
      + erewrite benumerate_empty_eq_nil by eauto; reflexivity.
      + repeat constructor; simpl; intros; intuition.
        unfold In in H; destruct H.
  Qed.

  Lemma refine_Add_binsert
  : forall or nr iel,
      or ≃ benumerate nr
      -> UnConstrFreshIdx or (elementIndex iel)
      -> RepInvPlus nr
      -> Add IndexedElement or iel ≃ benumerate (binsert nr (indexedElement iel)).
  Proof.
    simpl; intros; destruct_EnsembleIndexedListEquivalence; clear H.
    split.
    - exists (S (elementIndex iel) ).
      unfold UnConstrFreshIdx, Add in *; intros.
      inversion H; subst; unfold In in *.
      + apply H0 in H2; auto with arith.
      + inversion H2; subst; auto with arith.
    - destruct (permutation_map_cons
                    indexedElement
                    (binsert_enumerate (indexedElement iel) nr H1)
                    iel lor eq_refl eqv_or)
        as [lor' (eqv_lor' & perm_lor') ].
      exists lor'; intuition; eauto.
      split; intuition.
      + setoid_rewrite NoDup_modulo_permutation; eexists (_ :: _); intuition; eauto.
        constructor; eauto.
        setoid_rewrite <- eqv_nr; unfold not; intros.
        unfold In in *; apply H0 in H; exfalso; omega.
      + unfold In, Add in *; eapply Permutation_in;
          [ symmetry; eassumption
          | simpl; rewrite <- eqv_nr; inversion H; subst; intuition;
            unfold In in *; inversion H2; subst; eauto].
      + eapply Permutation_in in H; eauto; simpl in *; intuition.
        * constructor 2; subst; constructor.
        * constructor; rewrite eqv_nr; eauto.
  Qed.

  Lemma refine_Delete_bdelete
  : forall or nr search_term,
      or ≃ benumerate nr
      -> RepInvPlus nr
      -> EnsembleDelete or (fun tup => bfind_matcher search_term tup = true) ≃
                        benumerate (snd (bdelete nr search_term)).
  Proof.
    simpl; intros; destruct_EnsembleIndexedListEquivalence; clear H.
    split.
    - exists bnd; unfold UnConstrFreshIdx in *; intros; apply fresh_bnd;
    destruct H; eauto.
    - pose proof (bdelete_correct nr search_term H0); intuition.
      rewrite partition_filter_neq in H1; symmetry in H1.
      destruct (permutation_filter _ _ _ H1) as [l [l_eq Perm_l]].
      symmetry in Perm_l.
      destruct (permutation_map_base indexedElement Perm_l _ eqv_or)
               as [l' [l'_eq Perm_l']].
      exists (filter (fun a => negb (bfind_matcher search_term (indexedElement a))) l'); repeat split.
      + rewrite <- l_eq, <- l'_eq, filter_map; reflexivity.
      + apply NoDupFilter; eapply NoDup_Permutation_rewrite.
          symmetry; eauto.
          eauto.
      + unfold In, EnsembleDelete; intros.
        inversion H; subst.
        unfold In, Complement, In in *.
        rewrite <- partition_filter_neq.
        rewrite <- partition_filter_neq in l_eq.
        rewrite eqv_nr in H3.
        rewrite (In_partition (fun itup => bfind_matcher search_term (indexedElement itup))) in H3; intuition.
        rewrite partition_filter_eq, filter_In in H5; intuition.
        rewrite partition_filter_neq, filter_In in H5;
          rewrite partition_filter_neq, filter_In; intuition.
        symmetry in Perm_l'; eapply Permutation_in; eauto.
      + unfold In, EnsembleDelete; intros.
        rewrite filter_In in H; intuition.
        apply eqv_nr; eapply Permutation_in; eauto.
      + unfold In, Complement, In in *.
        rewrite filter_In in H; intuition.
        rewrite H3 in H5; discriminate.
  Qed.

  Lemma filter_then_map
  : forall {A B} (m: A -> B) (f: B -> bool) (x: list A),
      filter f (map m x) = map m (filter (fun t => f (m t)) x).
  Proof.
    intros; induction x as [| x' xs'].
    - simpl; reflexivity.
    - simpl; case_eq (f (m x')).
      + simpl; rewrite IHxs'; auto.
      + auto.
  Qed.

  Lemma map_then_map
  : forall {heading} (m: @Tuple heading -> @Tuple heading) (x: list IndexedElement),
      map m (map indexedElement x) = map indexedElement (map (fun t =>
         {| indexedElement := m (indexedElement t); elementIndex := elementIndex t|}) x).
  Proof.
    intro; induction x as [| x' xs'].
    - simpl. reflexivity.
    - simpl. rewrite IHxs'. reflexivity.
  Qed.

  Lemma permu_exists
  : forall {heading} br (x: list (@IndexedElement (@Tuple heading))),
    Permutation br (map indexedElement x) -> exists x', map indexedElement x' = br
      /\ Permutation x' x.
  Proof.
    intros.
    pose proof (permutation_map_base indexedElement H x).
    destruct H0.
    - reflexivity.
    - exists x0. intuition.
  Qed.

  Lemma refine_Update_bupdate
  : forall or nr search_term update_term,
      or ≃ benumerate nr
      -> RepInvPlus nr
      -> ValidUpdatePlus update_term
      -> IndexedEnsembleUpdate or (fun tup => bfind_matcher search_term tup = true)
             (bupdate_transform update_term)
             ≃ benumerate (bupdate nr search_term update_term).
  Proof.
    simpl; intros; destruct_EnsembleIndexedListEquivalence;
    split.
    - exists bnd; unfold UnConstrFreshIdx in *;
      intros; destruct H2; destruct H2; intuition.
      rewrite H4; apply fresh_bnd; auto; intuition.
    - pose proof (bupdate_correct nr search_term update_term H0 H1).
      rewrite partition_filter_neq in H2; rewrite partition_filter_eq in H2.
      unfold UnIndexedEnsembleListEquivalence in *.
      unfold EnsembleListEquivalence in *.
      rewrite <- eqv_or in H2.
      repeat rewrite filter_then_map in H2.
      rewrite map_then_map in H2.
      rewrite <- map_app in H2.
      pose proof (permu_exists _ H2).
      destruct H3 as [? [? ?]].
      exists x.
      intuition.
      + admit.
      + admit.
      (** l ~ map f (K) -> exists l1, l = map f l' ... bring this using destruct and
          then use it with exists (something) + intuition **)
      + admit.
  Qed.

  Definition SharpenedBagImpl
  : Sharpened (@BagSpec (@Tuple heading) SearchTermTypePlus
                        bfind_matcher).
  Proof.
    unfold BagSpec.
    hone representation using
         (fun r_o r_n =>
            r_o ≃ benumerate (Bag := BagPlus) r_n
            /\ RepInvPlus r_n).
    hone constructor "EmptyBag".
    {
      simplify with monad laws.
      refine pick val bempty.
      finish honing.
      intuition eauto using bempty_RepInv; eapply refine_Empty_set_bempty.
    }

    hone method "Enumerate".
    {
      simplify with monad laws.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val r_n; intuition;
      simplify with monad laws; simpl.
      finish honing.
    }

    hone method "Count".
    {
      simplify with monad laws.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val r_n; intuition;
      simplify with monad laws; simpl.
      erewrite Permutation_length
        by (rewrite bfind_correct; eauto; reflexivity).
      rewrite bcount_correct; eauto.
      finish honing.
    }

    hone method "Insert".
    {
      simplify with monad laws; intuition.
      destruct_EnsembleIndexedListEquivalence.
      refine pick val bnd; eauto; simplify with monad laws.
      simpl; refine pick val (binsert r_n n).
      simplify with monad laws.
      finish honing.
      split; eauto using binsert_RepInv.
      eapply refine_Add_binsert; simpl; eauto.
    }

    hone method "Find".
    {
      simplify with monad laws.
      intuition.
      pose proof (bfind_correct r_n n H2).
      destruct (permutation_filter _ _ _ (bfind_correct r_n n H2)) as [l [l_eq Perm_l]].
      refine pick val l.
      simplify with monad laws; simpl.
      refine pick val r_n; eauto.
      simplify with monad laws; simpl.
      rewrite l_eq.
      finish honing.
      eapply Permutation_EnsembleIndexedListEquivalence; simpl; eauto.
    }

    hone method "Delete".
    {
      simplify with monad laws; intuition.
      destruct (bdelete_correct r_n n H2).
      rewrite partition_filter_eq in H3.
      rewrite partition_filter_neq in H0.
      symmetry in H0; symmetry in H3.
      destruct (permutation_filter _ _ _ H0) as [l [l_eq Perm_l]].
      destruct (permutation_filter _ _ _ H3) as [l' [l'_eq Perm_l']].
      refine pick val l'.
      simplify with monad laws; simpl.
      refine pick val (snd (bdelete r_n n)).
      simplify with monad laws; simpl.
      rewrite l'_eq.
      finish honing.
      intuition auto using bdelete_RepInv.
      eapply refine_Delete_bdelete; simpl; eauto.
      eapply Permutation_EnsembleIndexedListEquivalence; simpl; eauto.
    }

    Admitted.

  (*FullySharpenEachMethod (@nil ADTSig) (inil ADT); simpl.

  Defined.

  Definition BagADTImpl : ComputationalADT.cADT (BagSig (@Tuple heading) SearchTermTypePlus).
    extract implementation of SharpenedBagImpl using (inil _).
  Defined. *)

End SharpenedBag.

Opaque CallBagMethod.
Arguments CallBagMethod : simpl never.
