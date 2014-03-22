Require Import List Omega ADTExamples.BinaryOperationSpec
        ADTExamples.BinaryOperationImpl ADTRefinement
        ADTCache.

Section BinOpRefine.

  Variable opSpec : nat -> nat -> Prop.
  Variable defaultSpec : nat -> Prop.

  Variable op : nat -> nat -> nat.
  Variable defaultValue : nat.

  Hypothesis op_commutes : forall x y, op x y = op y x.
  Hypothesis op_assoc : forall x y z, op (op x y) z = op x (op y z).
  Hypothesis default_satisfies_defaultSpec : defaultSpec defaultValue.
  Hypothesis op_returns_arg : forall n m,
    op n m = n \/ op n m = m.
  Hypothesis op_preserves_op1 : forall n m,
    opSpec (op n m) m.
  Hypothesis op_preserves_op2 : forall n m,
    opSpec (op n m) n.
  Hypothesis op_refl : Reflexive opSpec.
  Hypothesis op_trans : Transitive opSpec.

  Lemma fold_left_op_preserves_opSpec l :
    forall a n', opSpec a n' -> opSpec (fold_left op l a) n'.
  Proof.
    induction l; simpl; auto.
    intros; eapply IHl; etransitivity; [ | eassumption]; eauto.
  Qed.

  Hint Resolve fold_left_op_preserves_opSpec.

  Lemma fold_left_op_preserves_opSpec' l
    : forall acc,
      opSpec (fold_left op l acc) acc.
  Proof.
    eauto.
  Qed.

  Hint Resolve fold_left_op_preserves_opSpec'.

  Lemma fold_left_op_In_preserves_opSpec :
    forall m n' a,
      In n' m -> opSpec (fold_left op m a) n'.
  Proof.
    induction m; simpl; intuition; subst.
    destruct (op_returns_arg a0 n'); rewrite H; eauto.
    generalize (op_preserves_op1 a0 n'); rewrite H; eauto.
  Qed.

  Hint Resolve fold_left_op_In_preserves_opSpec.

  Lemma fold_left_discards_less_oppy :
    forall m a, a <> fold_left op m a -> exists a', In (fold_left op m a) m /\ op a a' = a'.
  Proof.
    induction m; simpl; intuition.
    destruct (op_returns_arg a0 a); rewrite H0 in *|-*; eauto.
    destruct (IHm _ H) as [a' [In_a' op_a] ]; eauto.
    destruct (eq_nat_dec a (fold_left op m a)); eauto.
    destruct (IHm _ n); exists x; intuition.
    rewrite <- H3, <- op_assoc, H0; auto.
  Qed.

  Lemma fold_left_constains_more_oppy :
    forall m a, a <> fold_left op m a -> count_occ eq_nat_dec m (fold_left op m a) > 0.
  Proof.
    intros m a neq; destruct (fold_left_discards_less_oppy m neq) as [a' [In_a' op_a] ].
    eapply count_occ_In; eauto.
  Qed.

  Hint Resolve fold_left_constains_more_oppy.

  Program Definition absList2Multiset (l : list nat) : multiset := count_occ eq_nat_dec l.

  Arguments absList2Multiset l / n .
  Arguments add_spec m x m' / .

  Lemma absList2Multiset_perm m n l
  : absList2Multiset (m :: n :: l) = absList2Multiset (n :: m :: l).
  Proof.
    intros; simpl; apply functional_extensionality; intros; repeat find_if_inside; auto.
  Qed.

  Theorem refine_add_impl m n :
  refine {m' : list nat |
          add_spec (absList2Multiset m) n (absList2Multiset m')}
         (add_impl m n).
  Proof.
    unfold refine; intros; apply_in_hyp computes_to_inv; simpl in *;
    subst; constructor; auto.
  Qed.

  Hint Resolve refine_add_impl.

  Arguments empty_spec defaultSpec m n / .
  Arguments nonempty_spec opSpec m n / .
  Arguments bin_op_spec opSpec defaultSpec m x n / .

  Lemma add_bin_op_nonempty :
    forall m n o,
      nonempty_spec opSpec m n ->
      nonempty_spec opSpec (add m o) (op n o).
  Proof.
    simpl; intros; intuition;
    find_if_inside; auto with arith; substs; eauto.
    destruct (op_returns_arg n o) as [H' | H']; rewrite H'; congruence.
  Qed.

  Lemma add_bin_op_empty :
    forall m n o,
      empty_spec defaultSpec m n ->
      nonempty_spec opSpec (add m o) o.
  Proof.
    simpl; intros; intuition;
    find_if_inside; auto with arith; substs; eauto;
    [ congruence
      | generalize (H1 n'); omega].
  Qed.

  Lemma add_not_empty :
    forall m o n,
      ~ (empty_spec defaultSpec (add m o) n).
  Proof.
    simpl; intuition; generalize (H1 o); find_if_inside; omega.
  Qed.

  Lemma bin_op_spec_add_non_empty m n o p n' :
    bin_op_spec opSpec defaultSpec (add m o) p n' ->
    bin_op_spec opSpec defaultSpec (add (add m o) n) p (op n' n).
  Proof.
    right; eapply add_bin_op_nonempty; eauto; simpl in *; intuition;
    elimtype False; generalize (H1 o); find_if_inside; omega.
  Qed.

  Lemma bin_op_spec_unique m n n' v :
    bin_op_spec opSpec defaultSpec m n v ->
    refine {a | bin_op_spec opSpec defaultSpec m n' a} (ret v).
  Proof.
    unfold bin_op_spec in *; intuition;
    intros v' old_hyp; inversion_by computes_to_inv; subst; constructor; intuition;
    intros v' old_hyp; inversion_by computes_to_inv; subst; constructor;
    intuition.
  Qed.

  Theorem refine_bin_op_impl m n :
  refine {m' : nat |
          bin_op_spec opSpec defaultSpec (absList2Multiset m) n m'}
         (bin_op_impl op defaultValue m n).
  Proof.
    intros v old_hyp.
    apply computes_to_inv in old_hyp; simpl in old_hyp; subst.
    constructor; simpl; auto.
    destruct m; subst; intuition.
    right; revert n0; induction m; simpl; [intuition; (find_if_inside; substs; intuition) | intuition].
    - repeat (find_if_inside; substs; intuition).
      destruct (op_returns_arg n0 a); rewrite H in *|-*; eauto.
    - repeat find_if_inside; substs; eauto;
      destruct (op_returns_arg n0 a); rewrite H0 in *|-*; eauto.
      destruct (IHm n0) as [_ IHm']; specialize (IHm' n'); simpl in IHm';
      find_if_inside; intuition.
      destruct (IHm a) as [_ IHm']; specialize (IHm' n'); simpl in IHm';
      find_if_inside; intuition.
  Qed.

  Lemma refines_NatBinOp
  : refineADT (NatBinOpSpec opSpec defaultSpec) (NatBinOpImpl op defaultValue).
  Proof.
    unfold NatBinOpSpec.
    eapply transitivityT; [ apply (refines_rep_pickImpl absList2Multiset) | ].
    econstructor 1 with (SiR := @eq (list nat)); simpl; intros; subst.
    setoid_rewrite refineEquiv_pick_eq'; autorewrite with refine_monad;
    interleave_autorewrite_refine_monad_with ltac:(apply refine_add_impl).
    interleave_autorewrite_refine_monad_with ltac:(apply refine_bin_op_impl).
  Qed.

  (* If we are caching a bin_op_impl method, just need to op the cachedVal
     and the added value. *)

  Definition update_cachedOp
  : mutatorMethodType (cachedRep (list nat) nat) nat :=
    fun m n =>
      ret (match (origRep m) with
             | [] => {| origRep := n :: [];
                            cachedVal := n |}
             | m' :: ms' => {| origRep := n :: m' :: ms';
                                   cachedVal := op (cachedVal m) n |}
           end).

  Lemma bin_op_spec_add
  : forall l cv n,
      bin_op_spec opSpec defaultSpec (absList2Multiset l) defaultValue cv ->
      bin_op_spec opSpec defaultSpec (absList2Multiset (n :: l))  defaultValue
                                                       (match l with
                                                          | nil => n
                                                          | _ :: _ => op cv n
                                                        end).
  Proof.
    destruct l; intuition.
    right; eapply add_bin_op_empty with (n := defaultValue); simpl; intuition.
    destruct H;
      [ elimtype False; eapply add_not_empty
        | right; eapply add_bin_op_nonempty]; eassumption.
  Qed.

  Lemma refine_add_impl' :
    forall r n,
   refine
     {nr' : list nat |
      forall or : multiset,
        or = absList2Multiset r ->
        exists or' : multiset,
          {r' : multiset | add_spec or n r'} ↝ or' /\ or' = absList2Multiset nr'}
     (add_impl r n).
  Proof.
    intros; econstructor; intros.
    econstructor; split; subst; eauto.
    econstructor; unfold add_impl in *; inversion_by computes_to_inv; subst;
    unfold add_spec; simpl; eauto.
  Qed.

  Lemma refine_bin_op_spec' :
    forall r v n,
      bin_op_spec opSpec defaultSpec (absList2Multiset r) defaultValue v ->
      refine
        {n' : nat |
         forall or : multiset,
           or = absList2Multiset r ->
           {n'0 : nat | bin_op_spec opSpec defaultSpec or n n'0} ↝ n'}
        (ret v).
  Proof.
    intros; intros v' RetV; apply computes_to_inv in RetV; subst; econstructor; intros;
    econstructor; eauto; substs;
    intuition; destruct r; substs.
  Qed.

End BinOpRefine.

Hint Resolve bin_op_spec_unique : bin_op_refinements.
Hint Resolve refine_add_impl : bin_op_refinements.
Hint Resolve refine_add_impl' : bin_op_refinements.
Hint Resolve refine_bin_op_spec' : bin_op_refinements.
Hint Resolve add_bin_op_empty : bin_op_refinements.
Hint Resolve add_bin_op_nonempty : bin_op_refinements.
Hint Resolve bin_op_spec_add : bin_op_refinements.
