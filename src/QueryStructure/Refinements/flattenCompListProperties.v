Require Export QueryStructureNotations QueryQSSpecs.
Require Import List AdditionalLemmas AdditionalMorphisms.

Unset Implicit Arguments.

Definition boxed_option {heading} 
           (P: @Tuple heading -> Prop) 
           (x: @IndexedTuple heading) :=
  Pick (fun l : list Tuple => (P (indexedTuple x) -> ret [indexedTuple x] ↝ l) /\ (~ P (indexedTuple x) -> l = [])).

Lemma flatten_CompList_app :
  forall {A} x1 x2 x1' x2',
    flatten_CompList x1 ↝ x1' ->
    flatten_CompList x2 ↝ x2' ->
    @flatten_CompList A (x1 ++ x2) ↝ (x1' ++ x2').
Proof.
  induction x1; simpl; intros.
  inversion_by computes_to_inv; subst.

  rewrite !app_nil_l; assumption.
  inversion_by computes_to_inv.

  specialize (IHx1 x2 x0 x2' H2 H0). 
  econstructor; eauto.
  econstructor; eauto.
  subst; rewrite app_assoc; constructor.
Qed.

Lemma boxed_option_nil :
  forall {heading} (P: @Tuple heading -> Prop),
  forall x,
    boxed_option (fun x : Tuple => P x) x ↝ [] ->
    (~ P (indexedTuple x)).
Proof.
  unfold boxed_option; simpl; intros.
  apply computes_to_inv in H.
  rewrite ret_computes_to, singleton_neq_nil in H.
  intuition.
Qed.

Lemma flatten_CompList_nil :
  forall {heading} (P: @Tuple heading -> Prop),
  forall (seq : list (@IndexedTuple heading)),
    flatten_CompList (map (boxed_option P) seq) ↝ [] ->
    forall x, List.In x seq -> (~ P (indexedTuple x)).
Proof.
  induction seq; simpl; intros flatten_comp * in_seq.
  - exfalso; assumption.
  - inversion_by computes_to_inv.
    symmetry in H2; rewrite app_eq_nil_iff in H2; destruct H2; subst.
    destruct in_seq; subst.
    + apply boxed_option_nil; assumption.
    + apply IHseq; assumption.
Qed.

Lemma flatten_CompList_app_inv :
  forall {heading} P,
    (forall a, P a \/ ~ P a) ->
    forall x1 x0_before x0_after,
      flatten_CompList 
        (map (@boxed_option heading P) x1) ↝ (x0_before ++ x0_after) ->
      exists x1_before x1_after,
        x1 = x1_before ++ x1_after /\
        flatten_CompList (map (boxed_option P) x1_before) ↝ x0_before /\
        flatten_CompList (map (boxed_option P) x1_after ) ↝ x0_after.
Proof.
  intros * excl; induction x1; simpl; intros.

  - inversion_by computes_to_inv.
    rewrite app_eq_nil_iff in H.
    setoid_rewrite app_eq_nil_iff.
    eexists; eexists; intuition; subst; intuition constructor.
  - inversion_by computes_to_inv.
    pose proof H0; unfold boxed_option in H0.
    apply computes_to_inv in H0; simpl in H0.
    destruct H0 as (spec1 & spec2).
    destruct (excl (indexedTuple a)) as [ Ptrue | Pfalse ];
      [ specialize (spec1 Ptrue); apply computes_to_inv in spec1
      | specialize (spec2 Pfalse) ]; subst.
    + rewrite app_singleton in H2. 
      destruct x0_before as [ | a' x0_before' ] eqn:eq_before; subst.
      * rewrite app_nil_l in H2.
        destruct x0_after as [ | a' x0_after]; try discriminate.
        injection H2; intros; subst.
        exists (@nil (@IndexedTuple heading)).
        eexists; repeat split; eauto; simpl; repeat econstructor; eauto.
      * rewrite <- app_comm_cons in H2.
        injection H2; intros; subst.
        destruct (IHx1 x0_before' x0_after H1) as [ x1_before [ x1_after (_eq & comp1 & comp2) ] ];
          subst.
        exists (a :: x1_before); exists x1_after.
        simpl; repeat split; repeat (first [eassumption | econstructor]).
    + rewrite app_nil_l in H2; subst.
      destruct (IHx1 x0_before x0_after H1) as [ x1_before [ x1_after (_eq & comp1 & comp2) ] ];
        subst.
      exists (a :: x1_before); exists x1_after.
      simpl; repeat split; repeat (first [eassumption | econstructor]).
Qed.

Lemma flatten_CompList_singleton :
  forall {heading} P,
  forall middle (head: @Tuple heading),
    flatten_CompList (map (boxed_option P) middle) ↝ [head] ->
    exists x,
      List.In x middle /\
      flatten_CompList (map (boxed_option P) [x]) ↝ [head].
Proof.
  induction middle; unfold flatten_CompList; simpl; intros.
  - apply ret_computes_to in H; discriminate.
  - inversion_by computes_to_inv.
    destruct x.
    + rewrite app_nil_l in H2; subst.
      destruct (IHmiddle _ H1) as [ x (x_in & flat_comp) ].
      eexists; eauto.
    + rewrite <- app_comm_cons in H2; injection H2; intros.
      symmetry in H; rewrite app_eq_nil_iff in H; destruct H; subst. 
      exists a; repeat (econstructor; eauto).
Qed.

Lemma flatten_CompList_app_cons_inv :
  forall {heading} P,
    (forall a, P a \/ ~ P a) ->
    forall x1 x0_before (head: @Tuple heading) x0_after,
      flatten_CompList 
        (map (boxed_option P) x1) ↝ (x0_before ++ head :: x0_after) ->
      exists x1_before x1_middle head' x1_after,
        x1 = x1_before ++ x1_middle ++ x1_after /\
        List.In head' x1 /\
        flatten_CompList (map (boxed_option P) x1_before) ↝ x0_before /\
        flatten_CompList (map (boxed_option P) [head']  ) ↝ [head]    /\
        flatten_CompList (map (boxed_option P) x1_after ) ↝ x0_after.
Proof.
  intros.
  apply flatten_CompList_app_inv in H0; try assumption.
  destruct H0 as [ x1_before [ x1_after (eq_split & comp1 & comp2) ] ]; subst.
  rewrite <- app_singleton in comp2; apply flatten_CompList_app_inv in comp2; try assumption.
  destruct comp2 as [ middle [ x1_after' (eq_split' & comp2 & comp3) ] ]; subst.
  apply flatten_CompList_singleton in comp2.
  destruct comp2 as [ head' (in_middle & comp2) ].
  repeat setoid_rewrite in_app_iff.
  repeat eexists; repeat split; try eassumption; intuition. 
Qed.
