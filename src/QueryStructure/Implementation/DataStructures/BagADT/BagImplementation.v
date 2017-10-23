Require Export
        Coq.Lists.List Coq.Program.Program
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsInterface
        Fiat.QueryStructure.Implementation.DataStructures.Bags.CountingListBags
        Fiat.QueryStructure.Implementation.DataStructures.Bags.TreeBags
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.Common.ilist.
Require Import Coq.Bool.Bool Coq.Strings.String
        Coq.Arith.Arith Coq.Structures.OrderedTypeEx
        Fiat.Common.String_as_OT
        Fiat.Common.i2list
        Fiat.Common.DecideableEnsembles
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.Ensembles.EnsembleListEquivalence
        Fiat.ADTRefinement.GeneralBuildADTTactics
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Implementation.DataStructures.Bags.BagsOfTuples
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT.

Section SharpenedBagImplementation.

  Context {heading : RawHeading}.
  Variable SearchTermTypePlus : Type.
  Variable UpdateTermTypePlus : Type.
  Variable BagTypePlus : Type.
  Variable RepInvPlus : BagTypePlus -> Prop.
  Variable ValidUpdatePlus : UpdateTermTypePlus -> Prop.
  Variable CheckUpdatePlus : UpdateTermTypePlus -> bool.

  Variable BagPlus : Bag BagTypePlus (@RawTuple heading) SearchTermTypePlus UpdateTermTypePlus.
  Variable CorrectBagPlus : CorrectBag RepInvPlus ValidUpdatePlus BagPlus.

  Variable CheckUpdatePlusValid : forall u: UpdateTermTypePlus,
                                    CheckUpdatePlus u = true -> ValidUpdatePlus u.

  Lemma refine_Empty_set_bempty :
    Empty_set IndexedElement ≃ benumerate bempty.
  Proof.
    split.
    - exists 1; unfold UnConstrFreshIdx; intros elements H; destruct H.
    - eexists nil; simpl; intuition.
      + erewrite benumerate_empty_eq_nil by eauto; reflexivity.
      + repeat constructor; simpl; intros; intuition.
        unfold In in H; destruct H.
      + apply NoDup_nil.
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
      intuition.
      + unfold In, Add in *; eapply Permutation_in;
          [ symmetry; eassumption
          | simpl; rewrite <- eqv_nr; inversion H; subst; intuition;
            unfold In in *; inversion H2; subst; eauto].
      + eapply Permutation_in in H; eauto; simpl in *; intuition.
        * constructor 2; subst; constructor.
        * constructor; rewrite eqv_nr; eauto.
      + unfold UnConstrFreshIdx in H0.
        apply NoDup_Permutation_rewrite with (l:=map elementIndex (iel :: lor)).
        apply Permutation_map; symmetry; assumption.
        simpl; apply NoDup_cons; clear eqv_or.
        unfold not; intros.
        apply in_map_iff in H; destruct H; destruct H.
        apply eqv_nr in H2.
        apply H0 in H2.
        omega.
        * assumption.
  Qed.

  Lemma NoDup_filter_in_map : forall (A B: Type) (f: A -> bool) (m: A -> B) (l: list A),
    NoDup (map m l) -> NoDup (map m (filter f l)).
  Proof.
    intros; induction l.
    - intuition.
    - simpl in *. destruct (f a).
      + simpl; apply NoDup_cons.
        * apply NoDup_remove_2 with (l:=[]) in H; simpl in H.
          unfold not; intros.
          apply in_map_iff in H0; destruct H0; destruct H0.
          apply filter_In in H1; destruct H1.
          apply in_map with (f:=m) in H1.
          rewrite -> H0 in H1.
          contradiction.
        * apply IHl; apply NoDup_remove_1 with (l:=[]) (a:=m a); intuition.
      + apply IHl; apply NoDup_remove_1 with (l:=[]) (a:=m a); intuition.
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
      Require Import Fiat.Common.List.ListFacts.
      rewrite partition_filter_neq in H1; symmetry in H1.
      destruct (permutation_filter _ _ _ H1) as [l [l_eq Perm_l] ].
      symmetry in Perm_l.
      destruct (permutation_map_base indexedElement Perm_l _ eqv_or)
               as [l' [l'_eq Perm_l'] ].
      exists (filter (fun a => negb (bfind_matcher search_term (indexedElement a))) l'); repeat split.
      + rewrite <- l_eq, <- l'_eq, filter_map; reflexivity.
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
      + apply Permutation_map with (f:=elementIndex) in Perm_l'.
        symmetry in Perm_l'; apply NoDup_Permutation_rewrite in Perm_l'.
        apply NoDup_filter_in_map; assumption.
        assumption.
  Qed.

  Lemma map_then_map
  : forall {heading} (m: @RawTuple heading -> @RawTuple heading) (x: list IndexedElement),
      map m (map indexedElement x) = map indexedElement (map (fun t =>
         {| indexedElement := m (indexedElement t); elementIndex := elementIndex t|}) x).
  Proof.
    intro; induction x as [| x' xs'].
    - simpl. reflexivity.
    - simpl. rewrite IHxs'. reflexivity.
  Qed.

  Lemma permu_exists
  : forall {heading} br (x: list (@IndexedElement (@RawTuple heading))),
    Permutation br (map indexedElement x) -> exists x', map indexedElement x' = br
      /\ Permutation x' x.
  Proof.
    intros.
    pose proof (permutation_map_base indexedElement H x).
    destruct H0.
    - reflexivity.
    - exists x0. intuition.
  Qed.

  Lemma permu_filter_rewrite
  : forall (A: Type) (l: list A) (f: A -> bool),
    Permutation l ((filter (fun x => negb (f x)) l) ++ (filter f l)).
  Proof.
    induction l; intros; simpl in *.
    - intuition.
    - case_eq (f a); intros; simpl in *.
      + rewrite <- Permutation_middle; rewrite <- IHl; reflexivity.
      + rewrite <- IHl; reflexivity.
  Qed.

  Lemma NoDup_two_partitions : forall (A B: Type) (m: A -> B) (f: A -> bool) (l: list A),
    NoDup (map m l) ->
    NoDup (map m ((filter (fun x => negb (f x)) l) ++ (filter (fun x => f x) l))).
  Proof.
    induction l; intros; simpl.
    - intuition.
    - simpl in *.
      pose proof (NoDup_remove_1 [] (map m l) (m a) H); simpl in H0.
      apply IHl in H0; apply NoDup_remove_2 with (l:=[]) in H; simpl in *; unfold not in *.
      case_eq (f a); intros; simpl in *.
      + rewrite -> map_app; apply NoDup_app_swap; rewrite <- map_app; simpl.
        apply NoDup_cons. unfold not; intros. pose proof (permu_filter_rewrite l f).
        rewrite Permutation_app_comm in H3.
        apply Permutation_map with (f:=m) in H3; symmetry in H3.
        pose proof (@Permutation_in _ _ _ _ H3 H2). contradiction.
        rewrite -> map_app; apply NoDup_app_swap; rewrite <- map_app; assumption.
      + apply NoDup_cons. unfold not; intros. pose proof (permu_filter_rewrite l f).
        apply Permutation_map with (f:=m) in H3; symmetry in H3.
        pose proof (@Permutation_in _ _ _ _ H3 H2).
        contradiction. assumption.
  Qed.

  Lemma refine_Update_bupdate
  : forall or nr search_term update_term,
      or ≃ benumerate nr
      -> RepInvPlus nr
      -> ValidUpdatePlus update_term
      -> IndexedEnsembleUpdate or (fun tup => bfind_matcher search_term tup = true)
                               (fun old new => new = (bupdate_transform update_term old))
             ≃ benumerate (snd (bupdate nr search_term update_term)).
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
      repeat rewrite filter_map in H2.
      rewrite map_then_map in H2.
      rewrite <- map_app in H2.
      destruct H2 as [H2 H2'].
      pose proof (permu_exists _ H2).
      destruct H3 as [? [? ?] ].
      exists x.
      intuition.
      + eapply Permutation_in.
        symmetry; apply H4.
        unfold IndexedEnsembleUpdate in H5; unfold In in H5. inversion H5.
        * destruct H6. destruct H6 as [ [? [? ?] ] ?].
          apply in_app_iff; right; apply in_map_iff.
          exists x1; intuition.
          rewrite <- H9. rewrite <- H8; destruct x0; intuition.
          apply filter_In; intuition.
          apply eqv_nr; apply H6.
          rewrite <- H9; rewrite <- H8; destruct x0; intuition.
          apply filter_In; intuition.
          apply eqv_nr; apply H6.
        * destruct H6; unfold Complement in H7; unfold not in H7.
          apply in_app_iff; left.
          apply filter_In; intuition; apply eqv_nr; apply H6.
      + apply Permutation_in with (x:=x0) in H4.
        rewrite <- H3 in H2.
        unfold In; unfold IndexedEnsembleUpdate.
        apply in_app_iff in H4; destruct H4.
        * right; split; apply filter_In in H4; destruct H4.
          apply eqv_nr in H4; assumption.
          unfold Complement; unfold In; intuition.
          rewrite H7 in H6; inversion H6.
        * left; apply in_map_iff in H4; destruct H4; destruct H4.
          exists x1; intuition; apply filter_In in H6; destruct H6.
          apply eqv_nr; assumption.
          assumption.
          rewrite <- H4; intuition.
          rewrite <- H4; intuition.
        * assumption.
      + apply Permutation_map with (f:=elementIndex) in H4.
        symmetry in H4.
        apply NoDup_Permutation_rewrite in H4.
        * assumption.
        * rewrite -> map_app; rewrite -> map_map; simpl; rewrite <- map_app.
          apply NoDup_two_partitions; assumption.
  Qed.

  Lemma filter_pred_negb_pred
  : forall (A: Type) pred (l: list A), filter pred (filter (fun x => negb (pred x)) l) = [].
  Proof.
    induction l; intros; simpl in *.
    - reflexivity.
    - case_eq (pred a); intros; simpl in *.
      + assumption.
      + rewrite -> H; assumption.
  Qed.

  Lemma filter_negb_pred_pred
  : forall (A: Type) pred (l: list A), filter (fun x => negb (pred x)) (filter pred l) = [].
  Proof.
    induction l; intros; simpl in *.
    - reflexivity.
    - case_eq (pred a); intros; simpl in *.
      + rewrite -> H; assumption.
      + assumption.
  Qed.

  Lemma filter_pred_pred
  : forall (A: Type) pred (l: list A), filter pred (filter pred l) = filter pred l.
  Proof.
    induction l; intros; simpl in *.
    - reflexivity.
    - case_eq (pred a); intros; simpl in *.
      + rewrite -> H; rewrite -> IHl; reflexivity.
      + assumption.
  Qed.

  Lemma permutation_double_filter
  : forall (A: Type) pred (l f1 f2: list A), Permutation (filter pred l) f1 ->
                           Permutation (filter (fun x => negb (pred x)) l) f2 ->
      exists f', filter pred f' = f1 /\ filter (fun x => negb (pred x)) f' = f2 /\ Permutation l f'.
  Proof.
    intros.
    pose proof (permu_filter_rewrite l pred).
    exists ((f1 ++ f2)%list).
    apply permutation_filter in H; destruct H; destruct H.
    apply permutation_filter in H0; destruct H0; destruct H0.
    intuition.
    - rewrite <- H0; rewrite -> filter_app; rewrite -> filter_pred_negb_pred.
      rewrite -> app_nil_r; repeat rewrite <- H; rewrite -> filter_pred_pred; reflexivity.
    - rewrite <- H; rewrite -> filter_app; rewrite -> filter_negb_pred_pred.
      simpl; repeat rewrite <- H0; rewrite -> filter_pred_pred; reflexivity.
    - rewrite <- H; rewrite <- H0; rewrite -> Permutation_app_comm.
      rewrite <- H2; rewrite <- H3; assumption.
  Qed.

  Lemma benumerate_fold_left_sub
  : forall l a b, RepInvPlus b ->
                Permutation (a :: benumerate (fold_left (fun b0 i => binsert b0 i) l b))
                            (benumerate (fold_left (fun b0 i => binsert b0 i) l (binsert b a))).
  Proof.
    induction l; intros; simpl in *.
    - rewrite <- binsert_enumerate; intuition.
    - repeat rewrite <- IHl.
      rewrite -> perm_swap; reflexivity.
      assumption.
      apply binsert_RepInv; assumption.
      assumption.
  Qed.

  Lemma benumerate_fold_left
  : forall l b, RepInvPlus b ->
                Permutation (benumerate
                               (fold_left (fun (b0 : BagTypePlus) (i : RawTuple) => binsert b0 i) l b))
                            (l ++ (benumerate b)).
  Proof.
    intros; induction l; simpl in *.
    - intuition.
    - rewrite <- IHl.
      rewrite -> benumerate_fold_left_sub.
      reflexivity.
      assumption.
  Qed.

  Local Instance DecideableEnsemble_bool
        {A} (f : A -> bool)
    : DecideableEnsemble (fun a => f a = true) :=
    {| dec := f |}. Proof. intuition. Defined.

  Lemma refine_Update_invalid
  : forall or nr search_term update_term,
      or ≃ benumerate nr
      -> RepInvPlus nr
      -> IndexedEnsembleUpdate or (fun tup => bfind_matcher search_term tup = true)
             (fun old new => new = (bupdate_transform update_term old))
             ≃ benumerate (fold_left (fun (b0 : BagTypePlus) (i : RawTuple) => binsert b0 i)
                                     (map (bupdate_transform update_term) (fst (bdelete nr search_term)))
                                     (snd (bdelete nr search_term))).
  Proof.
    simpl; intros; destruct_EnsembleIndexedListEquivalence; split.
    - exists bnd; unfold UnConstrFreshIdx in *.
      intros; destruct H1; destruct H1; intuition.
      rewrite H3; apply fresh_bnd; auto; intuition.
    - pose proof (bdelete_correct nr search_term H0); intuition.
      unfold UnIndexedEnsembleListEquivalence in *.
      rewrite <- eqv_or in H2, H3.
      rewrite partition_filter_neq in H2; symmetry in H2.
      rewrite partition_filter_eq in H3; symmetry in H3.
      pose proof (permutation_double_filter _ _ H3 H2).
      destruct H1; destruct H1 as [? [? ?] ].
      symmetry in H5. pose proof (permu_exists _ H5); destruct H6; destruct H6.
      pose proof (permutation_map indexedElement ((
                    filter (fun t => negb (bfind_matcher search_term (indexedElement t))) x0) ++
                  map (fun t => {|indexedElement := (bupdate_transform update_term) (indexedElement t);
                    elementIndex := elementIndex t|}) (filter (fun t => bfind_matcher search_term (indexedElement t)) x0))
                                  (benumerate
                                     (fold_left (fun (b0 : BagTypePlus) (i : RawTuple) => binsert b0 i)
                                                (map (bupdate_transform update_term)
                                                     (fst (bdelete nr search_term)))
                                                (snd (bdelete nr search_term))))).
      assert (
          Permutation
            (benumerate
               (fold_left (fun (b0 : BagTypePlus) (i : RawTuple) => binsert b0 i)
                          (map (bupdate_transform update_term)
                  (fst (bdelete nr search_term)))
                          (snd (bdelete nr search_term))))
            (map indexedElement
                 (filter
                    (fun t : IndexedElement =>
                       negb (bfind_matcher search_term (indexedElement t))) x0 ++
                    map
                    (fun t : IndexedElement =>
                       {|
                         elementIndex := elementIndex t;
                         indexedElement := bupdate_transform update_term
                                                             (indexedElement t) |})
                    (filter
                       (fun t : IndexedElement =>
                          bfind_matcher search_term (indexedElement t)) x0)))).
      rewrite -> benumerate_fold_left.
      rewrite <- H1; rewrite <- H4; rewrite -> map_app.
      let lem := constr:(fun A => @filter_map A _ (fun t => negb (bfind_matcher search_term t))) in
      rewrite <- lem.
      rewrite <- map_then_map; rewrite <- filter_map.
      repeat rewrite <- H6; rewrite -> Permutation_app_comm; intuition.
      apply bdelete_RepInv; assumption.
      destruct H8. intuition.
      pose proof (permu_exists _ H9); destruct H10 as [? [? ?] ]; clear H9.
      exists x2.
      intuition.
      + unfold In, IndexedEnsembleUpdate in *.
        intuition.
        * destruct H12; intuition.
          rewrite -> H8 in H10; symmetry in H10; apply eqv_nr in H9; symmetry in H7.
          pose proof (Permutation_in _ H7 H9).
          eapply Permutation_in.
          symmetry; apply H11.
          apply in_app_iff; right; apply in_map_iff.
          exists x4; intuition.
          rewrite <- H13; rewrite <- H15; destruct x3; reflexivity.
          apply filter_In; intuition.
        * unfold Complement, not, In in *.
          eapply Permutation_in.
          symmetry; apply H11.
          apply in_app_iff; left.
          apply eqv_nr in H9; rewrite <- H7 in H9.
          apply filter_In; intuition.
      + unfold In, IndexedEnsembleUpdate, Complement.
        apply Permutation_in with (x:=x3) in H11.
        apply in_app_iff in H11; destruct H11.
        * right; rewrite filter_In in H11; destruct H11; split. rewrite -> eqv_nr; rewrite <- H7.
          assumption. unfold not, In; intros. rewrite -> H13 in H12; simpl in H12; intuition.
        * left; apply in_map_iff in H11; destruct H11; destruct H11; exists x4.
          rewrite filter_In in H12; destruct H12; intuition.
          apply eqv_nr; rewrite <- H7; assumption.
          rewrite <- H11; intuition.
          rewrite <- H11; intuition.
        * assumption.
      + apply Permutation_map with (f:=elementIndex) in H7; symmetry in H7.
        apply Permutation_map with (f:=elementIndex) in H11.
        eapply NoDup_Permutation_rewrite. symmetry; apply H11.
        rewrite -> map_app; rewrite -> map_map; simpl; rewrite <- map_app; apply NoDup_two_partitions.
        apply NoDup_Permutation_rewrite in H7; assumption.
  Qed.

  Lemma RepInv_fold
  : forall (f: BagTypePlus -> (@RawTuple heading) -> BagTypePlus) (l: list (@RawTuple heading)) (r: BagTypePlus),
      (forall x y, RepInvPlus x -> RepInvPlus (f x y)) -> RepInvPlus r -> RepInvPlus (fold_left f l r).
  Proof.
    induction l.
    - intuition.
    - simpl; intros.
      apply IHl. apply H. apply H; apply H0.
  Qed.

  Definition SharpenedBagImpl'
  : FullySharpened (@BagSpec (@RawTuple heading) SearchTermTypePlus UpdateTermTypePlus
                             bfind_matcher bupdate_transform).
  Proof.
    unfold BagSpec.
    start sharpening ADT.

    hone representation using
         (fun r_o r_n =>
            r_o ≃ benumerate (Bag := BagPlus) r_n
            /\ RepInvPlus r_n).

    (* sEmpty *)
    {
      simplify with monad laws.
      refine pick val bempty.
      finish honing.
      intuition eauto using bempty_RepInv; eapply refine_Empty_set_bempty.
    }

    (* sFind *)
    {
      simplify with monad laws.
      intuition.
      pose proof (bfind_correct r_n d H2).
      destruct (permutation_filter _ _ _ (bfind_correct r_n d H2)) as [l [l_eq Perm_l] ].
      refine pick val (bfind r_n d).
      simplify with monad laws; simpl.
      refine pick val r_n; eauto.
      simplify with monad laws; simpl.
      finish honing.
      rewrite <- l_eq.
      destruct H1; constructor.
      - destruct H1 as [idx H1]; eexists idx.
        unfold UnConstrFreshIdx; intros; eapply H1.
        unfold IndexedEnsemble_Intersection in *; intuition.
      - eapply UnIndexedEnsembleListEquivalence_filter with
        (P_dec := DecideableEnsemble_bool (bfind_matcher d)); eauto.
        eapply Permutation_UnIndexedEnsembleListEquivalence; simpl in *; eauto.
    }

    (* sEnumerate. *)
    {
      simplify with monad laws.
      refine pick val (benumerate r_n); intuition;
      simplify with monad laws; simpl.
      refine pick val r_n.
      simplify with monad laws; simpl.
      finish honing.
      intuition.
    }

    (* sInsert *)
    {
      simplify with monad laws; intuition.
      simpl in *; destruct_EnsembleIndexedListEquivalence.
      refine pick val bnd; eauto; simplify with monad laws.
      simpl; refine pick val (binsert r_n d).
      finish honing.
      split; eauto using binsert_RepInv.
      eapply refine_Add_binsert; simpl; eauto.
    }

    (* sCount. *)
    {
      simplify with monad laws.
      intuition.
      destruct (permutation_filter _ _ _ (bfind_correct r_n d H2)) as [l [l_eq Perm_l] ].
      refine pick val (bfind r_n d).
      simplify with monad laws; simpl.
      refine pick val r_n; eauto.
      simplify with monad laws; simpl.
      finish honing.
      rewrite <- l_eq.
      destruct H1; constructor.
      - destruct H0 as [idx H0]; eexists idx.
        unfold UnConstrFreshIdx; intros; eapply H0.
        unfold IndexedEnsemble_Intersection in *; intuition.
      - eapply UnIndexedEnsembleListEquivalence_filter with
        (P_dec := DecideableEnsemble_bool (bfind_matcher d)); eauto.
        eapply Permutation_UnIndexedEnsembleListEquivalence; simpl in *; eauto.
    }

    (* sDelete *)
    {
      simplify with monad laws; intuition.
      simpl in *.
      destruct (bdelete_correct r_n d H2).
      rewrite partition_filter_eq in H3.
      rewrite partition_filter_neq in H0.
      symmetry in H0; symmetry in H3.
      destruct (permutation_filter _ _ _ H0) as [l [l_eq Perm_l] ].
      destruct (permutation_filter _ _ _ H3) as [l' [l'_eq Perm_l'] ].
      refine pick val l'.
      simplify with monad laws; simpl.
      refine pick val (snd (bdelete r_n d)).
      simplify with monad laws; simpl.
      rewrite l'_eq.
      finish honing.
      intuition auto using bdelete_RepInv.
      eapply refine_Delete_bdelete; simpl; eauto.
      eapply Permutation_EnsembleIndexedListEquivalence; simpl; eauto.
    }

    (* sUpdate *)
    {
      simplify with monad laws; simpl in *; intuition.
      pose proof (bupdate_correct (CorrectBag:=CorrectBagPlus) r_n d d0 H2).
      etransitivity.
      apply refine_if with (b:=CheckUpdatePlus d0).
      intros; apply CheckUpdatePlusValid in H3; simpl.
      pose proof (H0 H3); destruct H4.
      rewrite partition_filter_eq in H5; symmetry in H5.
      destruct (permutation_filter _ _ _ H5) as [l [l_eq Perm_l] ].
      refine pick val l.
      simplify with monad laws.
      refine pick val (snd (bupdate r_n d d0)).
      simplify with monad laws.
      rewrite l_eq; reflexivity.
      split.
      eapply refine_Update_bupdate; intuition.
      apply bupdate_RepInv; intuition.
      eapply Permutation_EnsembleIndexedListEquivalence; eauto.
      intros G; pose proof (bdelete_correct (CorrectBag:=CorrectBagPlus) r_n d H2).
      destruct H3. rewrite partition_filter_eq in H4; symmetry in H4.
      destruct (permutation_filter _ _ _ H4) as [l [l_eq Perm_l] ].
      refine pick val l.
      simplify with monad laws.
      refine pick val (let r := bdelete r_n d in
                       fold_left (fun b i => binsert b i) (map (bupdate_transform d0) (fst r)) (snd r)).
      simplify with monad laws; intuition; simpl.
      rewrite l_eq; reflexivity.
      split.
      eapply refine_Update_invalid; intuition.
      apply RepInv_fold.
      apply binsert_RepInv. apply bdelete_RepInv; assumption.
      eapply Permutation_EnsembleIndexedListEquivalence; eauto.
      finish honing.
    }

    finish_SharpeningADT_WithoutDelegation.

  Defined.

  Time Definition BagADTImpl : ComputationalADT.cADT (BagSig (@RawTuple heading) SearchTermTypePlus UpdateTermTypePlus) :=
    Eval simpl in projT1 SharpenedBagImpl'.

  Require Import TransparentAbstract.

  Definition SharpenedBagImpl
  : FullySharpened (@BagSpec (@RawTuple heading) SearchTermTypePlus UpdateTermTypePlus
                             bfind_matcher bupdate_transform).
  Proof.
    AbstractADT SharpenedBagImpl'.
  Defined.

End SharpenedBagImplementation.

Lemma FullySharpenedBagsEquivMatchers
  : forall (ElementType SearchTermType UpdateTermType : Type)
           (MatchSearchTerm MatchSearchTerm' : SearchTermType -> ElementType -> bool)
           (ApplyUpdateTerm ApplyUpdateTerm' : UpdateTermType -> ElementType -> ElementType),
    (forall st item, MatchSearchTerm st item = MatchSearchTerm' st item)
    -> (forall ut item, ApplyUpdateTerm ut item = ApplyUpdateTerm' ut item)
    -> FullySharpened (BagSpec MatchSearchTerm ApplyUpdateTerm)
    -> FullySharpened (BagSpec MatchSearchTerm' ApplyUpdateTerm').
Proof.
  intros; exists (projT1 X).
  pose (projT2 X); simpl in *.
  assert (MatchSearchTerm = MatchSearchTerm') as M_eq by
        (apply functional_extensionality; intros; apply functional_extensionality;
         eauto); destruct M_eq.
  assert (ApplyUpdateTerm = ApplyUpdateTerm') as A_eq by
        (apply functional_extensionality; intros; apply functional_extensionality;
         eauto); destruct A_eq.
  exact r.
Defined.
