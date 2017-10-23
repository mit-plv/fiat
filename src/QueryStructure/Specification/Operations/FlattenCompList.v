Require Import Coq.Lists.List
        Coq.Program.Program
        Coq.Sets.Ensembles.
Require Import Fiat.Common
        Fiat.Common.List.ListFacts
        Fiat.Common.List.ListMorphisms
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.Computation.

Unset Implicit Arguments.

Definition flatten_CompList {A} (c : list (Comp (list A))) :=
  fold_right (fun (b : Comp (list A)) (a : Comp (list A)) =>
                l <- b;
                  l' <- a;
                  ret (l ++ l')) (ret []) c.

Definition boxed_option {A}
           (P: A -> Prop)
           (x:  @IndexedElement A) :=
  Pick (fun l : list A => (P (indexedElement x) -> ret [indexedElement x] ↝ l) /\ (~ P (indexedElement x) -> l = [])).

Lemma flatten_CompList_app :
  forall {A} x1 x2 x1' x2',
    flatten_CompList x1 ↝ x1' ->
    flatten_CompList x2 ↝ x2' ->
    @flatten_CompList A (x1 ++ x2) ↝ (x1' ++ x2').
Proof.
  induction x1; simpl; intros.
  computes_to_inv; subst.

  rewrite !app_nil_l; assumption.
  computes_to_inv.
  specialize (IHx1 x2 _ _ H' H0).
  repeat (computes_to_econstructor; eauto).
  subst; rewrite app_assoc; constructor.
Qed.

Lemma boxed_option_nil {A} :
  forall (P: A -> Prop),
  forall x,
    boxed_option (fun x : A => P x) x ↝ [] ->
    (~ P (indexedElement x)).
Proof.
  unfold boxed_option; simpl; intros.
  apply Pick_inv in H; intuition.
  computes_to_inv; intuition; discriminate.
Qed.

Lemma flatten_CompList_nil {A} :
  forall (P: A -> Prop),
  forall (seq : list (@IndexedElement A)),
    flatten_CompList (map (boxed_option P) seq) ↝ [] ->
    forall x, List.In x seq -> (~ P (indexedElement x)).
Proof.
  induction seq; simpl; intros flatten_comp * in_seq.
  - exfalso; assumption.
  - computes_to_inv; subst.
    symmetry in flatten_comp''; rewrite app_eq_nil_iff in flatten_comp'';
      destruct flatten_comp''; subst.
    destruct in_seq; subst.
    + apply boxed_option_nil; assumption.
    + apply IHseq; assumption.
Qed.

Lemma flatten_CompList_app_inv :
  forall {A} (P : A -> Prop),
    (forall a, P a \/ ~ P a) ->
    forall x1 x0_before x0_after,
      flatten_CompList
        (map (@boxed_option A P) x1) ↝ (x0_before ++ x0_after) ->
      exists x1_before x1_after,
        x1 = x1_before ++ x1_after /\
        flatten_CompList (map (boxed_option P) x1_before) ↝ x0_before /\
        flatten_CompList (map (boxed_option P) x1_after ) ↝ x0_after.
Proof.
  intros * excl; induction x1; simpl; intros.

  -  computes_to_inv.
     rewrite app_eq_nil_iff in H.
     setoid_rewrite app_eq_nil_iff.
     eexists; eexists; intuition; subst; intuition constructor.
  -  computes_to_inv.
     pose proof H; unfold boxed_option in H0.
     computes_to_inv; destruct H0 as (spec1 & spec2).
     destruct (excl (indexedElement a)) as [ Ptrue | Pfalse ];
       [ specialize (spec1 Ptrue); computes_to_inv
       | specialize (spec2 Pfalse) ]; subst.
     + rewrite app_singleton in H''.
       destruct x0_before as [ | a' x0_before' ] eqn:eq_before; subst.
       * rewrite app_nil_l in H''.
         destruct x0_after as [ | a' x0_after]; try discriminate.
         injection H''; intros; subst.
         exists (@nil (@IndexedElement A)).
         eexists; repeat split; eauto; simpl; repeat econstructor; eauto.
       * rewrite <- app_comm_cons in H''.
         injection H''; intros; subst.
         destruct (IHx1 x0_before' x0_after H') as [ x1_before [ x1_after (_eq & comp1 & comp2) ] ];
           subst.
         exists (a :: x1_before); exists x1_after.
         simpl; repeat split; repeat (first [eassumption | econstructor]).
     + rewrite app_nil_l in H''; subst.
       destruct (IHx1 x0_before x0_after H') as [ x1_before [ x1_after (_eq & comp1 & comp2) ] ];
         subst.
       exists (a :: x1_before); exists x1_after.
       simpl; repeat split; repeat (first [eassumption | econstructor]).
Qed.

Lemma flatten_CompList_app_inv'
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
  -  computes_to_inv; subst.
     destruct (IHl _ _ H') as [e [e' [v_eq [Comp_l Comp_l'] ] ] ].
     rewrite v_eq.
     eexists (app v0 e), e'; intuition.
     repeat computes_to_econstructor; eauto.
Qed.

Lemma flatten_CompList_singleton {A}:
  forall P,
  forall middle (head: A),
    flatten_CompList (map (boxed_option P) middle) ↝ [head] ->
    exists x,
      List.In x middle /\
      flatten_CompList (map (boxed_option P) [x]) ↝ [head].
Proof.
  induction middle; unfold flatten_CompList; simpl; intros.
  -  computes_to_inv; discriminate.
  -  computes_to_inv.
     destruct v.
     + rewrite app_nil_l in H''; subst.
       destruct (IHmiddle _ H') as [ x (x_in & flat_comp) ].
       eexists; eauto.
     + rewrite <- app_comm_cons in H''; injection H''; intros.
       symmetry in H0; rewrite app_eq_nil_iff in H0; destruct H0; subst.
       exists a; repeat (econstructor; eauto).
Qed.

Lemma flatten_CompList_app_cons_inv {A}:
  forall P,
    (forall a, P a \/ ~ P a) ->
    forall x1 x0_before (head: A) x0_after,
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
  eexists _, _ ,_ ,_; repeat split; intuition; try eassumption; intuition.
Qed.


Lemma refine_flatten_CompList_func' :
  forall (A B : Type) (l : list A) (f f' : A -> Comp (list B)),
    (forall v, List.In v l -> refine (f v) (f' v))
    -> refine (flatten_CompList (map f l)) (flatten_CompList (map f' l)).
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - rewrite H by eauto.
    f_equiv; intro.
    rewrite IHl by eauto.
    reflexivity.
Qed.

Lemma flatten_CompList_nil':
  forall (A B : Type)(seq : list A),
    refine (flatten_CompList (map (fun _ => ret nil) seq)) (ret (@nil B)).
Proof.
  induction seq; simpl; unfold refine; intros; computes_to_inv; subst; eauto.
Qed.
