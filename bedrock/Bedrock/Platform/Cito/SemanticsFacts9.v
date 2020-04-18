Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Coq.Lists.List.

  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.
  Require Import Bedrock.Platform.Cito.WordMapFacts.
  Import FMapNotations.
  Open Scope fmap_scope.

  Require Import Bedrock.Platform.Cito.GeneralTactics4.

  Arguments empty {_}.

  Require Import Bedrock.Platform.Cito.SemanticsUtil.

  Definition make_heap' := fold_right (fun x m => @store_pair ADTValue m x) empty.

  Definition no_clash A (p1 p2 : A * Value ADTValue) :=
    match snd p1, snd p2 with
      | ADT _, ADT _ => (fst p1 <> fst p2)%type
      | _, _ => True
    end.

  Definition no_clash_ls A p := List.Forall (@no_clash A p).

  Definition not_in_heap elt w (v : Value ADTValue) (h : WordMap.t elt) :=
    match v with
      | SCA _ => True
      | ADT _ => ~ WordMap.In w h
    end.

  Require Import Coq.Setoids.Setoid.

  Add Morphism (@store_pair ADTValue) with signature Equal ==> eq ==> Equal as store_pair_Equal_m.
  Proof.
    intros st1 st2 Heq [w v].
    unfold store_pair.
    destruct v.
    eauto.
    simpl.
    rewrite Heq.
    reflexivity.
  Qed.

  Add Parametric Morphism elt : (@not_in_heap elt) with signature eq ==> eq ==> Equal ==> iff as not_in_heap_Equal_m.
  Proof.
    intros w v st1 st2 Heq.
    destruct v; simpl in *.
    intuition.
    rewrite Heq.
    intuition.
  Qed.
  Require Import Bedrock.Word.

  Lemma store_pair_comm p1 p2 h : no_clash p1 p2 -> store_pair (store_pair h p1) p2 == store_pair (store_pair h p2) p1.
  Proof.
    intros Hnc.
    intros p.
    destruct p1 as [w1 v1].
    destruct p2 as [w2 v2].
    unfold store_pair.
    simpl.
    destruct v1 as [? | a1]; destruct v2 as [? | a2]; eauto.
    unfold no_clash in *.
    simpl in *.
    destruct (weq p w2) as [? | Hne2].
    {
      subst.
      rewrite add_eq_o by eauto.
      rewrite add_neq_o by eauto.
      rewrite add_eq_o by eauto.
      eauto.
    }
    rewrite add_neq_o by eauto.
    destruct (weq p w1) as [? | Hne1].
    {
      subst.
      rewrite add_eq_o by eauto.
      rewrite add_eq_o by eauto.
      eauto.
    }
    rewrite add_neq_o by eauto.
    rewrite add_neq_o by eauto.
    rewrite add_neq_o by eauto.
    eauto.
  Qed.

  Definition DisjointPtrs A := List.ForallOrdPairs (@no_clash A).

  Require Import Bedrock.Memory.

  Definition disjoint_ptrs_ls (p : W * Value ADTValue) (pairs : list (W * Value ADTValue)):=
    match (snd p) with
      | SCA _ => True
      | ADT _ => ~ List.In (fst p) (List.map fst (List.filter (fun p => is_adt (snd p)) pairs))
    end.

  Require Import Bedrock.Platform.Cito.Semantics.

  Lemma disjoint_ptrs_cons_elim' pairs : forall p, disjoint_ptrs (p :: pairs) -> disjoint_ptrs_ls p pairs /\ disjoint_ptrs pairs.
  Proof.
    induction pairs; simpl; intros [w1 v1] H.
    {
      split.
      unfold disjoint_ptrs_ls; simpl.
      destruct v1; intuition.
      unfold disjoint_ptrs; simpl.
      econstructor.
    }
    destruct a as [w2 v2]; simpl in *.
    destruct v1 as [? | a1]; destruct v2 as [? | a2]; simpl in *; try solve [unfold disjoint_ptrs, disjoint_ptrs_ls in *; simpl in *; eauto].
    {
      inversion H; subst; clear H.
      split; eauto.
    }
    {
      inversion H; subst; clear H.
      split; eauto.
    }
  Qed.

  Lemma disjoint_ptrs_ls_no_clash_ls pairs : forall p, disjoint_ptrs_ls p pairs -> no_clash_ls p pairs.
  Proof.
    induction pairs; simpl; intros [w1 v1] H.
    {
      econstructor.
    }
    destruct a as [w2 v2]; simpl in *.
    destruct v1 as [? | a1]; destruct v2 as [? | a2]; simpl in *; eauto.
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *.
      econstructor.
      eauto.
      eapply Forall_forall.
      intuition.
    }
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *.
      econstructor.
      eauto.
      eapply Forall_forall.
      intuition.
    }
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *; simpl in *.
      econstructor; simpl in *.
      eauto.
      eapply (IHpairs (w1, ADT a1)); eauto.
    }
    {
      unfold disjoint_ptrs_ls, no_clash_ls, no_clash in *; simpl in *.
      intuition.
      econstructor; simpl in *.
      eauto.
      eapply (IHpairs (w1, ADT a1)); eauto.
    }
  Qed.
  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Lemma disjoint_ptrs_cons_elim pairs : forall p, disjoint_ptrs (p :: pairs) -> no_clash_ls p pairs /\ disjoint_ptrs pairs.
    intros p H.
    eapply disjoint_ptrs_cons_elim' in H.
    openhyp.
    split; eauto.
    eapply disjoint_ptrs_ls_no_clash_ls; eauto.
  Qed.

  Lemma disjoint_ptrs_DisjointPtrs ls : disjoint_ptrs ls -> DisjointPtrs ls.
  Proof.
    induction ls; simpl; intros H.
    {
      econstructor.
    }
    eapply disjoint_ptrs_cons_elim in H.
    openhyp.
    econstructor; eauto.
    eapply IHls; eauto.
  Qed.

  Lemma no_clash_ls_not_in_heap pairs : forall w v, no_clash_ls (w, v) pairs -> not_in_heap w v (make_heap' pairs).
  Proof.
    induction pairs; simpl; intros w v H.
    {
      destruct v; simpl.
      eauto.
      intros Hin.
      eapply empty_in_iff in Hin.
      eauto.
    }
    inversion H; subst.
    destruct a as [w' v'].
    destruct v as [? | a]; simpl in *.
    { eauto. }
    unfold store_pair.
    destruct v' as [? | a']; simpl in *.
    {
      eapply IHpairs in H3.
      simpl in *.
      eauto.
    }
    unfold no_clash in H2; simpl in *.
    intros Hin.
    eapply add_in_iff in Hin.
    destruct Hin as [Hin | Hin].
    {
      subst; intuition.
    }
    eapply IHpairs in H3.
    simpl in *.
    intuition.
  Qed.

  Arguments store_pair {_} _ _.

  Lemma fold_left_store_pair_comm pairs : forall w v h1 h2, no_clash_ls (w, v) pairs -> h2 == store_pair h1 (w, v) -> fold_left store_pair pairs h2 == store_pair (fold_left store_pair pairs h1) (w, v).
  Proof.
    induction pairs; simpl; intros w v h1 h2 Hnin Hh.
    rewrite Hh; reflexivity.
    destruct a as [w' v'].
    inversion Hnin; subst.
    eapply IHpairs; eauto.
    rewrite Hh.
    rewrite store_pair_comm by eauto.
    reflexivity.
  Qed.

  Lemma make_heap_make_heap' pairs : disjoint_ptrs pairs -> make_heap pairs == make_heap' pairs.
  Proof.
    induction pairs; simpl; intros Hdisj.
    reflexivity.
    unfold make_heap in *.
    simpl.
    destruct a as [w v].
    eapply disjoint_ptrs_cons_elim in Hdisj.
    destruct Hdisj as [Hnin Hdisj].
    rewrite <- IHpairs by eauto.
    eapply fold_left_store_pair_comm; eauto.
    reflexivity.
  Qed.

  Add Morphism (@Semantics.word_adt_match ADTValue) with signature Equal ==> eq ==> iff as word_adt_match_Equal_m.
  Proof.
    intros st1 st2 Heq [w v].
    unfold Semantics.word_adt_match.
    simpl.
    destruct v.
    {
      intuition.
    }
    rewrite Heq.
    intuition.
  Qed.

  Lemma mapsto_make_heap'_intro pairs :
    disjoint_ptrs pairs ->
    forall k (v : ADTValue),
      List.In (k, ADT v) pairs ->
      find k (make_heap' pairs) = Some v.
  Proof.
    induction pairs; intros Hdisj k v Hk; simpl in *.
    {
      intuition.
    }
    eapply disjoint_ptrs_cons_elim in Hdisj.
    destruct Hdisj as [Hnc Hdisj].
    destruct a as [k' v']; simpl in *.
    unfold store_pair in *; simpl in *.
    destruct Hk as [Hk | Hk].
    {
      inject Hk.
      rewrite add_eq_o in * by eauto.
      eauto.
    }
    destruct v' as [w | v']; simpl in *.
    {
      eapply IHpairs; eauto.
    }
    destruct (weq k k') as [? | Hne]; subst.
    {
      eapply no_clash_ls_not_in_heap in Hnc.
      unfold not_in_heap in *.
      eapply IHpairs in Hk; eauto.
      contradict Hnc.
      eapply find_Some_in; eauto.
    }
    rewrite add_neq_o in * by eauto.
    eapply IHpairs in Hk; eauto.
  Qed.

  Lemma mapsto_make_heap'_elim pairs :
    disjoint_ptrs pairs ->
    forall k (v : ADTValue),
      find k (make_heap' pairs) = Some v ->
      List.In (k, ADT v) pairs.
  Proof.
    induction pairs; intros Hdisj k v Hk; simpl in *.
    {
      rewrite empty_o in *.
      discriminate.
    }
    eapply disjoint_ptrs_cons_elim in Hdisj.
    destruct Hdisj as [Hnc Hdisj].
    destruct a as [k' v']; simpl in *.
    unfold store_pair in *; simpl in *.
    destruct v' as [w | v']; simpl in *.
    {
      unfold store_pair in *; simpl in *.
      right.
      eapply IHpairs; eauto.
    }
    destruct (weq k k') as [? | Hne]; subst.
    {
      rewrite add_eq_o in * by eauto.
      inject Hk.
      left; eauto.
    }
    rewrite add_neq_o in * by eauto.
    eapply IHpairs in Hk; eauto.
  Qed.

  Lemma mapsto_make_heap'_iff pairs :
    disjoint_ptrs pairs ->
    forall k (v : ADTValue),
      List.In (k, ADT v) pairs <->
      find k (make_heap' pairs) = Some v.
  Proof.
    intros Hdisj k v; split; intros H.
    - eapply mapsto_make_heap'_intro; eauto.
    - eapply mapsto_make_heap'_elim; eauto.
  Qed.

  Arguments word_scalar_match {ADTValue} _.

  Lemma DisjointPtrs_good_scalars_forall_word_adt_match : forall pairs h, DisjointPtrs pairs -> List.Forall word_scalar_match pairs -> List.Forall (word_adt_match (fold_left store_pair pairs h)) pairs.
  Proof.
    induction pairs; simpl; try solve [intuition].
    intros h Hdisj H.
    inversion H; subst.
    inversion Hdisj; subst.
    destruct a as [w v]; simpl in *.
    econstructor.
    {
      rewrite fold_left_store_pair_comm; try reflexivity; trivial.
      unfold word_adt_match.
      unfold Semantics.word_adt_match.
      unfold word_scalar_match in *.
      simpl in *.
      destruct v; simpl in *; trivial.
      unfold store_pair; simpl.
      rewrite add_eq_o by eauto.
      eauto.
    }
    eapply IHpairs; eauto.
  Qed.

  Lemma disjoint_ptrs_good_scalars_good_inputs pairs :
    @disjoint_ptrs ADTValue pairs ->
    good_scalars pairs ->
    good_inputs (make_heap pairs) pairs.
  Proof.
    intros Hdisj Hgs.
    split; eauto.
    eapply DisjointPtrs_good_scalars_forall_word_adt_match; eauto.
    eapply disjoint_ptrs_DisjointPtrs; eauto.
  Qed.

  Lemma good_inputs_add addr (a : ADTValue) h : ~ In addr h -> good_inputs (add addr a h) ((addr, ADT a) :: nil).
  Proof.
    intros Hnin.
    unfold good_inputs.
    unfold Semantics.good_inputs.
    unfold Semantics.disjoint_ptrs.
    unfold Semantics.word_adt_match.
    simpl.
    split.
    - repeat econstructor; simpl.
      rewrite add_eq_o by eauto.
      eauto.
    - repeat econstructor; eauto.
  Qed.

  Local Open Scope fmap_scope.

  Lemma good_inputs_make_heap_submap h pairs :
    good_inputs (ADTValue := ADTValue) h pairs ->
    make_heap pairs <= h.
  Proof.
    intros Hgi.
    destruct Hgi as [Hforall Hdisj].
    unfold good_inputs in *.
    intros k1 v Hk1.
    rewrite make_heap_make_heap' in * by eauto.
    eapply mapsto_make_heap'_iff in Hk1; eauto.
    eapply Forall_forall in Hforall; eauto.
    unfold word_adt_match in *.
    simpl in *.
    eauto.
  Qed.

  Lemma forall_word_adt_match_good_scalars : forall h pairs, List.Forall (word_adt_match h) pairs -> List.Forall (@word_scalar_match ADTValue) pairs.
    intros.
    eapply Locals.Forall_weaken.
    2 : eassumption.
    intros.
    destruct x.
    unfold word_adt_match, Semantics.word_adt_match, word_scalar_match in *; simpl in *.
    destruct v; simpl in *; intuition.
  Qed.

  Require Import ListFacts3.

  Lemma core_eq_func_eq f1 (H1 : is_no_dup (FuncCore.ArgVars f1) = true) f2 (H2 : is_no_dup (FuncCore.ArgVars f2) = true) : f1 = f2 -> {| Fun := f1; NoDupArgVars := H1 |} = {| Fun := f2; NoDupArgVars := H2 |}.
  Proof.
    intros.
    subst.
    f_equal.
    Require Import BoolFacts.
    eapply bool_irre.
  Qed.

End ADTValue.
