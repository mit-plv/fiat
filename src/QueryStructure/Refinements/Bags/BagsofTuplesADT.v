Require Export BagsInterface CountingListBags TreeBags Tuple Heading List Program ilist.
Require Import String_as_OT IndexedEnsembles DecideableEnsembles.
Require Import Bool String OrderedTypeEx BagsOfTuples.
Require Import GeneralQueryRefinements.
Require Import QueryStructureNotations ListImplementation.
Require Import AdditionalLemmas AdditionalPermutationLemmas Arith BagADT.

Section SharpenedBag.

  Context {heading : Heading}.
  Variable SearchTermTypePlus : Type.
  Variable UpdateTermTypePlus : Type.
  Variable BagTypePlus : Type.
  Variable RepInvPlus : BagTypePlus -> Prop.
  Variable ValidUpdatePlus : UpdateTermTypePlus -> Prop.
      
  Variable BagPlus : Bag BagTypePlus (@Tuple heading) SearchTermTypePlus UpdateTermTypePlus.
  Variable CorrectBagPlus : CorrectBag RepInvPlus ValidUpdatePlus BagPlus.

  Definition SharpenedBagImpl 
  : Sharpened (@BagSpec (@Tuple heading) SearchTermTypePlus
                        bfind_matcher).
  Proof.
    unfold BagSpec.
    hone representation using 
         (fun r_o r_n => 
            r_o ≃ benumerate (Bag := BagPlus) r_n
            /\ RepInvPlus r_n).
    hone constructor "EmptyCache".
    {
      simplify with monad laws.
      refine pick val bempty.
      finish honing.

      erewrite benumerate_empty_eq_nil by eauto.
      repeat split.
      exists 1; unfold UnConstrFreshIdx; intros; destruct H0.
      eexists nil; simpl; intuition.
      repeat constructor.
      intros; destruct H0.
      simpl; intuition.
      apply bempty_RepInv.
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
      Check in_ensemble_insert_iff.

      Check permutation_map.

  setoid_rewrite get_update_unconstr_eq.
  setoid_rewrite in_ensemble_insert_iff.
  setoid_rewrite NoDup_modulo_permutation.

      
      simplify with monad laws; simpl.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val (snd (bdelete r_n n)); intuition;
      try simplify with monad laws.

    hone method "Delete".
    {
      simplify with monad laws; simpl.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val (snd (bdelete r_n n)); intuition;
      try simplify with monad laws.
      
      
      simpl.

      econstructor.
      split.
      unfold EnsembleIndexedListEquivalence.
      apply EnsembleIndexedListEquivalence_Empty.

      setoid_rewrite val_refine.
      Check bempty.
      exists bempty.
    }

(* An equivalence relation between Ensembles of Tuples and Bags
   which incorporates the bag's representation invariant. *)

Definition EnsembleBagEquivalence
           {heading : Heading}
           (bagplus : BagPlusProof (@Tuple heading))
           (ens : Ensemble (@IndexedTuple heading))
           (store : BagTypePlus bagplus)
: Prop :=
      ens ≃ benumerate (Bag := BagPlus bagplus) store /\
  RepInvPlus bagplus store.

Instance EnsembleIndexedTreeEquivalence_AbsR
           {heading : Heading}
           {bagplus : BagPlusProof (@Tuple heading)}
: @UnConstrRelationAbsRClass (@IndexedTuple heading) (BagTypePlus bagplus) :=
  {| UnConstrRelationAbsR := EnsembleBagEquivalence bagplus |}.

(* We now prove that [empty] is a valid abstraction of the
   empty database. *)

Lemma bempty_correct_DB :
  forall {TContainer TSearchTerm TUpdateTerm : Type}
         {db_schema : QueryStructureSchema}
         {index : BoundedString}
         {store_is_bag : Bag TContainer Tuple TSearchTerm TUpdateTerm}
         (RepInv : TContainer -> Prop)
         (ValidUpdate : TUpdateTerm -> Prop),
    CorrectBag RepInv ValidUpdate store_is_bag
    -> EnsembleIndexedListEquivalence
      (GetUnConstrRelation (DropQSConstraints (QSEmptySpec db_schema)) index)
      (benumerate bempty).
Proof.
  intros.
  erewrite benumerate_empty_eq_nil by eauto.
  apply EnsembleIndexedListEquivalence_Empty.
Qed.

Corollary bemptyPlus_correct_DB :
  forall {db_schema : QueryStructureSchema}
         {index : BoundedString}
         {bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index))},
    GetUnConstrRelation (DropQSConstraints (QSEmptySpec db_schema)) index ≃
                        bempty (Bag := BagPlus bag_plus).
Proof.
  destruct bag_plus; intros; simpl; constructor.
  eapply bempty_correct_DB; eauto.
  apply bempty_RepInv.
Qed.

(* We now prove that [binsert] is a valid abstraction of the
   adding a tuple to the ensemble modeling the database. *)

Require Import OperationRefinements.

Lemma binsert_correct_DB
      db_schema qs index
      (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
:  forall (store: BagTypePlus bag_plus),
     GetUnConstrRelation qs index ≃ store
     -> forall tuple bound
        (ValidBound : UnConstrFreshIdx (GetUnConstrRelation qs index) bound),
      EnsembleIndexedListEquivalence
        (GetUnConstrRelation
           (@UpdateUnConstrRelation db_schema qs index
                                   (EnsembleInsert
                                      {| elementIndex := bound;
                                         indexedElement := tuple |}
                                      (GetUnConstrRelation qs index))) index)
        (benumerate (binsert (Bag := BagPlus bag_plus) store tuple)).
Proof.
  intros * store_eqv; destruct store_eqv as (store_eqv, store_WF).
  unfold EnsembleIndexedTreeEquivalence_AbsR, UnConstrFreshIdx,
  EnsembleBagEquivalence, EnsembleIndexedListEquivalence,
  UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.

  setoid_rewrite get_update_unconstr_eq.
  setoid_rewrite in_ensemble_insert_iff.
  setoid_rewrite NoDup_modulo_permutation.
  split; intros.

  unfold UnConstrFreshIdx; exists (S bound); intros; intuition; subst; simpl.
  unfold EnsembleInsert in *; intuition; subst; simpl; omega.
  (* erewrite binsert_enumerate_length by eauto with typeclass_instances.
    intuition; subst;
    [ | apply lt_S];
    intuition. *)

  destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto.


  (* destruct store_eqv as (indices & [ l' (map & nodup & equiv) ]); eauto. *)

  destruct (permutation_map_cons indexedElement (binsert_enumerate tuple store store_WF)
                                 {| elementIndex := bound;
                                    indexedElement := tuple |} l' eq_refl map)
    as [ l'0 (map' & perm) ].

  exists l'0.
  split; [ assumption | split ].

  eexists; split; try apply perm.

  constructor;
    [ rewrite <- equiv; intro abs; apply H in abs;
      simpl in abs; omega | assumption ].

  setoid_rewrite perm.
  setoid_rewrite equiv.
  setoid_rewrite eq_sym_iff at 1.
  reflexivity.
Qed.

Corollary binsertPlus_correct_DB :
  forall {db_schema : QueryStructureSchema}
         qs
         (index : BoundedString)
         (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
         store,
    GetUnConstrRelation qs index ≃ store
    -> forall
      tuple bound
      (ValidBound : UnConstrFreshIdx (GetUnConstrRelation qs index) bound),
      GetUnConstrRelation
       (@UpdateUnConstrRelation db_schema qs index
                                (EnsembleInsert
                                   {| elementIndex := bound;
                                      indexedElement := tuple |}
                                   (GetUnConstrRelation qs index))) index
      ≃ binsert (Bag := BagPlus bag_plus) store tuple.
Proof.
  simpl; intros; constructor.
  - eapply binsert_correct_DB; eauto.
  - eapply binsert_RepInv; apply H.
Qed.

    Lemma bdelete_correct_DB_fst {qsSchema}
    : forall (qs : UnConstrQueryStructure qsSchema)
             (Ridx : @BoundedString (map relName (qschemaSchemas qsSchema)))
             bag_plus
             bag
             (equiv_bag : EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs Ridx) bag)
             (DT : Ensemble Tuple)
             (DT_Dec : DecideableEnsemble DT)
             search_term,
        ExtensionalEq (@dec _ _ DT_Dec)
                              (bfind_matcher (Bag := BagPlus bag_plus) search_term)
             -> refine {x | QSDeletedTuples qs Ridx DT x}
                       (ret (fst (bdelete bag search_term))).
    Proof.
      intros; setoid_rewrite DeletedTuplesFor; auto.
      destruct equiv_bag as [[[bound ValidBound] [l [eq_bag [NoDup_l equiv_l]]]] RepInv_bag];
        subst.
      rewrite refine_List_Query_In by repeat (econstructor; intuition eauto).
      rewrite refine_List_Query_In_Where, refine_List_For_Query_In_Return_Permutation,
      (filter_by_equiv _ _ H), map_id, <- partition_filter_eq.
      rewrite refine_pick_val.
      reflexivity.
      destruct (bdelete_correct bag search_term RepInv_bag) as [_ Perm_bdelete].
      unfold BagPlusProofAsBag, QSGetNRelSchemaHeading, GetNRelSchemaHeading,
      GetNRelSchema in *.
        rewrite Perm_bdelete, eq_bag; reflexivity.
    Qed.

    Lemma bdelete_correct_DB_snd
          db_schema qs index
          (bag_plus : BagPlusProof (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
    :  forall (store: BagTypePlus bag_plus),
         GetUnConstrRelation qs index ≃ store
         -> forall (DeletedTuples : Ensemble (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
                   (DT_Dec : DecideableEnsemble DeletedTuples),
              EnsembleIndexedListEquivalence
                (GetUnConstrRelation
                   (@UpdateUnConstrRelation db_schema qs index
                                            (EnsembleDelete (GetUnConstrRelation qs index)
                                                            DeletedTuples)) index)
                (snd (List.partition (@dec _ _ DT_Dec)
                                     (benumerate store))).
    Proof.
      simpl; unfold EnsembleDelete, EnsembleBagEquivalence, In, Complement; simpl;
      unfold EnsembleIndexedListEquivalence, UnIndexedEnsembleListEquivalence,
      EnsembleListEquivalence; intros; intuition; destruct_ex; intuition; subst.
      repeat setoid_rewrite get_update_unconstr_eq; simpl; intros.
      exists x0.
      unfold UnConstrFreshIdx in *; intros; apply H; destruct H3; eauto.
      exists (snd (partition (@dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ ) x)); intuition.
      - unfold BagPlusProofAsBag; rewrite <- H2.
        repeat rewrite partition_filter_neq.
        clear; induction x; simpl; eauto.
        unfold indexedTuple in *;
        find_if_inside; simpl; eauto; rewrite <- IHx; reflexivity.
      - revert H0; clear; induction x; simpl; eauto.
        intros; inversion H0; subst.
        case_eq (partition (fun x0 => @dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ x0) x); intros; simpl in *; rewrite H.
        rewrite H in IHx; apply IHx in H3;
        case_eq (@dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ a);
        intros; simpl in *; rewrite H1; simpl; eauto.
        constructor; eauto.
        unfold not; intros; apply H2; eapply In_partition with
        (f := fun x0 : IndexedTuple => @dec IndexedTuple (fun t => DeletedTuples (indexedElement t)) _ x0).
        simpl in *; rewrite H; eauto.
      - rewrite get_update_unconstr_eq in H3.
        destruct H3; unfold In in *.
        apply H4 in H3; eapply In_partition in H3; intuition; try apply H6.
        apply In_partition_matched in H6; apply dec_decides_P in H6; exfalso; eauto.
      - rewrite get_update_unconstr_eq; constructor.
        eapply H4; eapply In_partition; eauto.
        unfold In; intros.
        apply In_partition_unmatched in H3.
        simpl in *; apply dec_decides_P in H5.
        unfold indexedTuple, QSGetNRelSchemaHeading, GetNRelSchemaHeading, GetNRelSchema in *;
          rewrite H3 in H5; congruence.
    Qed.

    Require Import AdditionalMorphisms.

    Lemma bdeletePlus_correct_DB_snd
          db_schema qs index
          bag_plus
    :  forall (store: BagTypePlus bag_plus),
         EnsembleBagEquivalence bag_plus (GetUnConstrRelation qs index) store
         -> forall (DeletedTuples : Ensemble (@Tuple (@QSGetNRelSchemaHeading db_schema index)))
                   (DT_Dec : DecideableEnsemble DeletedTuples)
                   search_term,
              ExtensionalEq (@dec _ _ DT_Dec)
                            (bfind_matcher (Bag := BagPlus bag_plus) search_term)
              -> EnsembleBagEquivalence
                   bag_plus
                   (GetUnConstrRelation
                      (@UpdateUnConstrRelation db_schema qs index
                                               (EnsembleDelete (GetUnConstrRelation qs index)
                                                               DeletedTuples)) index)
                   (snd (bdelete store search_term)).
    Proof.
      intros; unfold ExtensionalEq, EnsembleBagEquivalence in *.
      unfold EnsembleBagEquivalence.
      repeat rewrite get_update_unconstr_eq; simpl; intros.

      split;
        [
        | eapply bdelete_RepInv; intuition ].
      simpl in *;
        unfold EnsembleListEquivalence, EnsembleIndexedListEquivalence,
        UnConstrFreshIdx, EnsembleDelete, Complement in *; intuition; destruct_ex; intuition; intros.
      exists x; intros; eapply H; destruct H1; unfold In in *; eauto.
      unfold UnIndexedEnsembleListEquivalence, EnsembleListEquivalence in *.
      generalize (bdelete_correct store search_term H2); destruct_ex; intuition.
      rewrite partition_filter_neq in H1.
      unfold BagPlusProofAsBag in *; simpl in *; rewrite <- H4 in H1.
      clear H6 H H2 H4.
      remember (GetUnConstrRelation qs index).
      generalize DeletedTuples DT_Dec x0 u H1 H0 H3 H7; clear.
      induction (benumerate (snd (bdelete store search_term))); intros.
      eexists []; simpl; intuition.
      constructor.
      destruct H; destruct H2; unfold In in *.
      apply H7 in H.
      apply Permutation_nil in H1.
      apply dec_decides_P; rewrite H0.
      revert H1 H; clear; induction x0; simpl; eauto.
      case_eq (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a)); simpl; intros.
      intuition; subst; eauto.
      discriminate.
      assert (exists a',
                List.In a' x0 /\ indexedElement a' = a
                /\ (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a') = false)).
      generalize (@Permutation_in _ _ _ a H1 (or_introl (refl_equal _))).
      rewrite filter_map; clear; induction x0; simpl;
      intuition.
      revert H;
        case_eq (bfind_matcher (Bag := BagPlus bag_plus) search_term (indexedElement a0)); simpl; intros; eauto.
      apply IHx0 in H0; destruct_ex; intuition eauto.
      subst; intuition eauto.
      destruct_ex; intuition eauto.
      destruct_ex.
      assert (exists x0',
                Permutation x0 (x :: x0') /\
                ~ List.In x x0').
      {
        intuition; subst.
        repeat rewrite filter_map; generalize x H2 H3; clear;
        induction x0; intros; simpl in *|-; intuition; subst; eauto.
        inversion H3; subst; exists x0; intuition.
        inversion H3; subst.
        destruct (IHx0 _ H H4); intuition; eexists (a :: x1).
        rewrite H1; intuition.
        constructor.
        simpl in H0; intuition; subst; eauto.
      }
      destruct_ex; intuition; subst.
      rewrite filter_map in H1; rewrite H in H1; simpl in *.
      rewrite H8 in *; simpl in *.
      destruct (IHl DeletedTuples DT_Dec x1
                    (fun tup => In _ u tup /\ tup <> x)); eauto;
      clear IHl.
      rewrite filter_map; eapply Permutation_cons_inv; eauto.
      apply NoDup_Permutation_rewrite in H; eauto.
      inversion H; eauto.
      intuition; intros.
      destruct H2; apply H7 in H2.
      eapply Permutation_in in H; eauto.
      simpl in *; intuition.
      constructor.
      eapply H7.
      symmetry in H; eapply Permutation_in; eauto.
      simpl; eauto.
      intros; subst.
      apply NoDup_Permutation_rewrite in H; eauto.
      eexists (x :: x2); intuition.
      simpl; congruence.
      constructor; eauto.
      unfold not; intros.
      unfold In in *.
      apply H10 in H9; inversion H9; subst; unfold In in *;
      intuition.
      unfold In in H9; inversion H9; subst; unfold In in *;
      intuition.
      generalize (Permutation_in _ H (proj1 (H7 _) H11)); intros In_x0.
      destruct In_x0; simpl; subst; eauto.
      right.
      apply H10; constructor; unfold In; intuition eauto.
      subst; eauto.
      constructor; intros.
      apply H7.
      simpl in *; intuition; subst; eauto.
      apply H10 in H11; unfold In in *; inversion H11;
      unfold In in *; subst; intuition eauto.
      apply H7; eauto.
      unfold In.
      simpl in *; intuition; subst; eauto.
      apply dec_decides_P in H11; rewrite H0 in H11;
      unfold BagPlusProofAsBag, QSGetNRelSchemaHeading,
      GetNRelSchemaHeading, GetNRelSchema in *; simpl in *;
      congruence.
      apply H10 in H12; unfold In in *; inversion H12;
      unfold In in *; subst; intuition eauto.
    Qed.

    Arguments bdelete : simpl never.
