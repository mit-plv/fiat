Require Export ADTSynthesis.QueryStructure.Refinements.Bags.BagsInterface ADTSynthesis.QueryStructure.Refinements.Bags.CountingListBags ADTSynthesis.QueryStructure.Refinements.Bags.TreeBags ADTSynthesis.QueryStructure.Tuple ADTSynthesis.QueryStructure.Heading Coq.Lists.List Coq.Program.Program ADTSynthesis.Common.ilist ADTSynthesis.Common.i2list.
Require Import ADTSynthesis.Common.String_as_OT ADTSynthesis.QueryStructure.IndexedEnsembles ADTSynthesis.Common.DecideableEnsembles.
Require Import Coq.Bool.Bool Coq.Strings.String Coq.Structures.OrderedTypeEx ADTSynthesis.QueryStructure.Refinements.Bags.BagsOfTuples.
Require Import ADTSynthesis.QueryStructure.Refinements.GeneralQueryRefinements.
Require Import ADTSynthesis.QueryStructure.QueryStructureNotations ADTSynthesis.QueryStructure.Refinements.ListImplementation.
Require Import ADTSynthesis.QueryStructure.AdditionalLemmas ADTSynthesis.QueryStructure.AdditionalPermutationLemmas Coq.Arith.Arith ADTSynthesis.QueryStructure.Refinements.BagADT.BagADT.

Section SharpenedBagImplementation.

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
      + constructor.
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
      + unfold In, Add in *; eapply Permutation_in;
          [ symmetry; eassumption
          | simpl; rewrite <- eqv_nr; inversion H; subst; intuition;
            unfold In in *; inversion H2; subst; eauto].
      + eapply Permutation_in in H; eauto; simpl in *; intuition.
        * constructor 2; subst; constructor.
        * constructor; rewrite eqv_nr; eauto.
      + setoid_rewrite NoDup_modulo_permutation; eexists (_ :: _); intuition;
        [ | rewrite perm_lor'; simpl; reflexivity].
        constructor; eauto.
        unfold not; intros.
        rewrite in_map_iff in *; destruct_ex; intuition; subst.
        rewrite <- eqv_nr in *; apply_in_hyp H0; omega.
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
      +

        apply NoDupFilter; eapply NoDup_Permutation_rewrite.
        symmetry; eauto.
        eauto.

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

End SharpenedBagImplementation.
