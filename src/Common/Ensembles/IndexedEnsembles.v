Require Import Coq.Lists.List
        Coq.Strings.String
        Coq.omega.Omega
        Coq.Logic.FunctionalExtensionality
        Coq.Sorting.Permutation Coq.Sets.Ensembles
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.PermutationFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.List.ListFacts.

Class UnConstrRelationAbsRClass {A B : Type} :=
  { UnConstrRelationAbsR : Ensemble A -> B -> Prop }.

Definition EnsembleInsert {A : Type}
           (a : A)
           (R : Ensemble A)
           (a' : A) :=
  a' = a \/ R a'.

Lemma in_ensemble_insert_iff :
  forall {A} table tup inserted,
    In A (EnsembleInsert inserted table) tup <->
    tup = inserted \/ In A table tup.
Proof.
  firstorder.
Qed.

Section IndexedEnsembles.

  Context {ElementType : Type}.

  Record IndexedElement :=
    { elementIndex : nat;
      indexedElement : ElementType }.

  Definition IndexedEnsemble := Ensemble IndexedElement.

  Definition IndexedEnsemble_In
             (ensemble : IndexedEnsemble)
             (item : ElementType) :=
    exists idx, In _ ensemble {| elementIndex := idx; indexedElement := item |}.

  Definition IndexedEnsembleSubtract
             (element : ElementType)
             (ens : IndexedEnsemble)
    : IndexedEnsemble :=
    fun element' => indexedElement element' <> element /\ ens element'.

  (* 'Deleting' a set of tuples [R] from a relation [F] is the same
   as taking the intersection of [F] and the complement of [R]. *)
  Definition EnsembleDelete
             (F : IndexedEnsemble)
             (R : Ensemble ElementType)
    := Intersection _ F (Complement _ (fun iel => R (indexedElement iel))).

  Definition IndexedEnsembleUpdate
             (ens : IndexedEnsemble)
             (cond : Ensemble ElementType)
             (updateR : relation ElementType)
    : IndexedEnsemble
    := fun e => (exists f: IndexedElement, ((ens f) /\ cond (indexedElement f) /\ updateR (indexedElement f) (indexedElement e))
                                           /\ elementIndex e = elementIndex f) \/
                ((ens e) /\ Complement _ (fun f => cond (indexedElement f)) e).

  Definition UnIndexedEnsembleListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType)  :=
    exists l', (map indexedElement l') = l /\
               (forall x, Ensembles.In _ ensemble x <-> List.In x l') /\
               NoDup (map elementIndex l').

  Definition UnConstrFreshIdx
             (ensemble : IndexedEnsemble)
             (bound : nat) :=
    forall element,
      ensemble element
      -> lt (elementIndex element) bound.

  Definition EnsembleIndexedListEquivalence
             (ensemble : IndexedEnsemble)
             (l : list ElementType) :=
    (exists bound, UnConstrFreshIdx ensemble bound)
    /\ UnIndexedEnsembleListEquivalence ensemble l.

  Global Instance EnsembleListEquivalence_AbsR :
    @UnConstrRelationAbsRClass (IndexedElement)
                               (list ElementType) :=
    {| UnConstrRelationAbsR := EnsembleIndexedListEquivalence|}.

  Ltac destruct_EnsembleIndexedListEquivalence :=
    match goal with
      H : EnsembleIndexedListEquivalence ?or ?nr |- _ =>
      let bnd := fresh "bnd" in
      let fresh_bnd := fresh "fresh_bnd" in
      let lor := fresh "l" or in
      let eqv_or := fresh "eqv_" or in
      let NoDup_lor := fresh "NoDup_" or in
      let eqv_r_n := fresh "eqv_nr" in
      let H' := fresh in
      pose proof H as H';
        destruct H' as [[bnd fresh_bnd] [lor [eqv_or [eqv_r_n NoDup_lor]]]]
    end.

  Lemma Permutation_EnsembleIndexedListEquivalence
    : forall ensemble (l l' : list _),
      EnsembleIndexedListEquivalence ensemble l
      -> Permutation l l'
      -> EnsembleIndexedListEquivalence ensemble l'.
  Proof.
    simpl; intros.
    destruct_EnsembleIndexedListEquivalence.
    econstructor; eauto.
    symmetry in H0.
    destruct (permutation_map_base indexedElement H0 _ eqv_ensemble) as [l'' [l''_eq H']].
    econstructor; split; eauto.
    constructor.
    - intros; rewrite eqv_nr.
      split; apply Permutation_in; intuition.
    - apply NoDup_modulo_permutation.
      exists (map elementIndex lensemble).
      intuition. apply Permutation_map. auto.
  Qed.

  Lemma NoDup_IndexedElement :
    forall (l1 : list IndexedElement),
      NoDup (map elementIndex l1) ->
      NoDup l1.
  Proof.
    induction l1; simpl; constructor; inversion H; subst; eauto using in_map.
  Qed.

  Definition IndexedEnsemble_Intersection
             (ens : IndexedEnsemble)
             (ens' : Ensemble ElementType)
    : IndexedEnsemble :=
    fun element' => ens element' /\ ens' (indexedElement element').

  Lemma IndexedEnsemble_Intersection_And
    : forall (ens : IndexedEnsemble)
             (P Q : Ensemble ElementType),
      Same_set _ (IndexedEnsemble_Intersection (IndexedEnsemble_Intersection ens P) Q)
               (IndexedEnsemble_Intersection ens (fun el => P el /\ Q el)).
  Proof.
    unfold Same_set, Included, IndexedEnsemble_Intersection, In; intuition.
  Qed.

  Definition FiniteEnsemble (P : IndexedEnsemble)
    := exists l, UnIndexedEnsembleListEquivalence P l.

  Lemma NoDup_filter_map :
    forall (f : _ -> bool)
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

  Lemma UnIndexedEnsembleListEquivalence_filter
    : forall R P (P_dec : DecideableEnsemble (A := ElementType) P) l,
      UnIndexedEnsembleListEquivalence R l
      -> UnIndexedEnsembleListEquivalence (IndexedEnsemble_Intersection R P)
                                          (filter (@DecideableEnsembles.dec _ P P_dec) l).
  Proof.
    destruct 1.
    eexists (filter (fun x => DecideableEnsembles.dec (indexedElement x)) x); simpl; intuition.
    - rewrite <- filter_map, H0; reflexivity.
    - inversion H1.
      rewrite H in H3.
      revert H3 H4; clear; induction x; simpl; intuition subst.
      + apply dec_decides_P in H4; rewrite H4; simpl; intuition.
      + find_if_inside; simpl; eauto.
    - apply filter_In in H1; intuition.
      apply dec_decides_P in H4; econstructor; eauto.
      apply H; eauto.
    - eauto using NoDup_filter_map.
  Qed.

  Lemma Permutation_UnIndexedEnsembleListEquivalence
    : forall ensemble (l l' : list ElementType),
      UnIndexedEnsembleListEquivalence ensemble l
      -> Permutation l l'
      -> UnIndexedEnsembleListEquivalence ensemble l'.
  Proof.
    simpl; intros.
    destruct H; intuition; symmetry in H0.
    destruct (PermutationFacts.permutation_map_base _ H0 _ H1)
      as [l'' [l''_eq H']].
    econstructor; split; intuition eauto.
    rewrite H'; eapply H; eauto.
    rewrite H' in H2; eapply H; eauto.
    eapply PermutationFacts.NoDup_modulo_permutation.
    eexists (map elementIndex x).
    intuition. apply Permutation_map. auto.
  Qed.

  Lemma Permutation_UnIndexedEnsembleListEquivalence'
    : forall ensemble (l l' : list _),
      UnIndexedEnsembleListEquivalence ensemble l
      -> UnIndexedEnsembleListEquivalence ensemble l'
      -> Permutation l l'.
  Proof.
    simpl; intros.
    destruct H; destruct H0; intuition subst.
    setoid_rewrite H0 in H2.
    eapply Permutation_map.
    eapply NoDup_Permutation; eauto using NoDup_IndexedElement.
  Qed.

  Lemma UnIndexedEnsembleListEquivalence_Empty_set
    : UnIndexedEnsembleListEquivalence (Empty_set IndexedElement) [].
  Proof.
    unfold UnIndexedEnsembleListEquivalence; eexists [ ];
    simpl; intuition.
    destruct H.
    econstructor.
  Qed.

  Lemma UnIndexedEnsembleListEquivalence_Same_set
    : forall ens ens' l,
      Same_set _ ens ens' ->
      UnIndexedEnsembleListEquivalence ens l ->
      UnIndexedEnsembleListEquivalence ens' l.
  Proof.
    unfold UnIndexedEnsembleListEquivalence, Same_set, Included; intros;
    destruct_ex; intuition; subst.
    eexists _; intuition eauto.
    eapply H0; eauto.
    eapply H1; eapply H0; eauto.
  Qed.

  Lemma UnIndexedEnsembleListEquivalence_Insert
    : forall ens (l : list _) a,
      UnConstrFreshIdx ens (elementIndex a)
      -> UnIndexedEnsembleListEquivalence ens l
      -> UnIndexedEnsembleListEquivalence (EnsembleInsert a ens) (indexedElement a :: l).
  Proof.
    unfold UnIndexedEnsembleListEquivalence; intros; intuition.
    destruct_ex; intuition.
    subst.
    eexists (_ :: _); simpl; intuition.
    - destruct H1; subst; eauto.
      right; eapply H0; eauto.
    - econstructor; congruence.
    - right; eapply H0; eauto.
    - econstructor.
      intro.
      eapply in_map_iff in H1; destruct_ex; intuition; subst.
      eapply H0 in H4; apply H in H4.
      omega.
      eauto.
  Qed.

  Lemma UnIndexedEnsembleListEquivalence_Delete
    : forall ens (l : list ElementType) P (P_dec : DecideableEnsemble P),
      UnIndexedEnsembleListEquivalence ens l
      -> UnIndexedEnsembleListEquivalence
           (EnsembleDelete ens P)
           (filter (fun a : ElementType => negb (DecideableEnsembles.dec a)) l).
  Proof.
    unfold UnIndexedEnsembleListEquivalence; intros; intuition.
    destruct_ex; intuition; subst.
    eexists; simpl; intuition.
    symmetry; eapply filter_map.
    simpl.
    - destruct H0; subst; eauto.
      unfold Complement, In in H1.
      eapply filter_In; split; eauto.
      eapply H; eauto.
      rewrite <- Decides_false in H1; rewrite H1; reflexivity.
    - eapply filter_In in H0; intuition.
      constructor; eauto.
      eapply H; eauto.
      eapply (@Decides_false _ P).
      destruct (DecideableEnsembles.dec (indexedElement x0)); simpl in *; eauto.
    - eauto using NoDup_filter_map.
  Qed.

  Lemma FiniteEnsemble_Insert
    : forall P el,
      UnConstrFreshIdx P (elementIndex el)
      -> FiniteEnsemble P
      -> FiniteEnsemble (EnsembleInsert el P ).
  Proof.
    unfold FiniteEnsemble, EnsembleInsert; intros; destruct_ex.
    eexists; eauto using UnIndexedEnsembleListEquivalence_Insert.
  Qed.

  Lemma FiniteEnsemble_Intersection
    : forall P Q,
      DecideableEnsemble Q
      -> FiniteEnsemble P
      -> FiniteEnsemble (IndexedEnsemble_Intersection P Q).
  Proof.
    unfold FiniteEnsemble; intros; destruct_ex.
    eauto using UnIndexedEnsembleListEquivalence_filter.
  Qed.

  Lemma UnConstrFreshIdx_Delete
    : forall (P : IndexedEnsemble) DeletedTuples bnd,
      UnConstrFreshIdx P bnd
      -> UnConstrFreshIdx (EnsembleDelete P DeletedTuples) bnd.
  Proof.
    unfold EnsembleDelete, UnConstrFreshIdx; intros.
    inversion H0; subst; eauto.
  Qed.

  Lemma unindexed_OK_exists_index' :
    forall x lIndexed (t t' : _) n n',
      n <> n'
      -> nth_error x n = Some t
      -> nth_error x n' = Some t'
      -> Permutation x (map indexedElement lIndexed)
      -> exists m m' idx idx',
          m <> m'
          /\ nth_error lIndexed m = Some {| elementIndex := idx; indexedElement := t |}
          /\ nth_error lIndexed m' = Some {| elementIndex := idx'; indexedElement := t' |}.
  Proof.
    intros.
    eapply PermutationFacts.permutation_map_base in H2; intuition eauto.
    destruct_ex; intuition; subst.
    revert t t' n n' H H0 H1; induction H4; intros.
    - destruct n; simpl in *; discriminate.
    - destruct n; destruct n'; simpl in *.
      + intuition.
      + assert (exists m', nth_error (map indexedElement l') m' = Some t') by
            (eapply in_list_exists; rewrite <- H4; eapply exists_in_list; eauto).
        destruct H2.
        eapply nth_error_map' in H2; destruct_ex; intuition.
        injections.
        eexists 0, (S x0), (elementIndex x), (elementIndex x1); intuition; simpl; eauto.
        destruct x; eauto.
        rewrite H3; destruct x1; eauto.
      + assert (exists m, nth_error (map indexedElement l') m = Some t) by
            (eapply in_list_exists; rewrite <- H4; eapply exists_in_list; eauto).
        destruct H2.
        eapply nth_error_map' in H2; destruct_ex; intuition.
        injections.
        eexists (S x0), 0, (elementIndex x1), (elementIndex x); intuition; simpl; eauto.
        rewrite H3; destruct x1; eauto.
        destruct x; eauto.
      + destruct (IHPermutation t t' n n') as [m [m' [idx [idx' ?] ] ] ]; eauto.
        eexists (S m), (S m'), idx, idx'; simpl; intuition eauto.
    - eapply nth_error_map' in H0; destruct_ex; intuition.
      eapply nth_error_map' in H1; destruct_ex; intuition.
      rewrite <- H3, <- H4; destruct x0; destruct x1; simpl in *.
      destruct n as [ | [ | n ] ];  destruct n' as [ | [ | n' ] ];
        injections; simpl in *.
      + intuition.
      + eexists 1, 0, _, _; simpl; eauto.
      + eexists 1, (S (S n')), _, _; simpl; repeat split; try eassumption; omega.
      + eexists 0, 1, _, _; simpl; eauto.
      + intuition.
      + eexists 0, (S (S n')), _, _; simpl; repeat split; try eassumption; omega.
      + eexists (S (S n)), 1, _, _; simpl; repeat split; try eassumption; omega.
      + eexists (S (S n)), 0, _, _; simpl; repeat split; try eassumption; omega.
      + eexists (S (S n)), (S (S n')), _, _; simpl; repeat split; try eassumption; omega.
    -  destruct (IHPermutation1 _ _ _ _ H H0 H1) as [m [m' [idx [idx' ?] ] ] ];
         intuition.
       clear H.
       eapply IHPermutation2; eauto.
       eapply map_nth_error with (f := indexedElement) in H2; simpl in *; eauto.
       eapply map_nth_error with (f := indexedElement) in H5; simpl in *; eauto.
  Qed.

End IndexedEnsembles.

Ltac destruct_EnsembleIndexedListEquivalence :=
  match goal with
    H : EnsembleIndexedListEquivalence ?or ?nr |- _ =>
    let bnd := fresh "bnd" in
    let fresh_bnd := fresh "fresh_bnd" in
    let lor := fresh "l" or in
    let eqv_or := fresh "eqv_" or in
    let NoDup_lor := fresh "NoDup_" or in
    let eqv_r_n := fresh "eqv_nr" in
    let H' := fresh in
    pose proof H as H';
      destruct H' as [[bnd fresh_bnd] [lor [eqv_or [eqv_r_n NoDup_lor]]]]
  end.
