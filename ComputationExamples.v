Require Import List Ensembles String Setoid RelationClasses Morphisms Morphisms_Prop Program Equivalence Min Max Permutation Sorted.
Require Import Common Computation.

Section op_funcs.
  Variable op : nat -> nat -> Prop.
  Variable on_empty : nat -> Prop.
  Definition is_op (l : list nat) (v : nat)
    := Forall (fun n => op v n) l /\ (List.In v l \/ (l = nil /\ on_empty v)).

  Definition is_op0 (l : list nat) : Comp nat :=
    { x : nat
      | is_op l x }%comp.

  Variable concrete_op : nat -> nat -> nat.
  Variable concrete_on_empty : nat.
  Hypothesis concrete_op_commutes : forall x y, concrete_op x y = concrete_op y x.
  Hypothesis concrete_op_assoc : forall x y z, concrete_op (concrete_op x y) z = concrete_op x (concrete_op y z).
  Hypothesis on_empty_concrete_on_empty : on_empty concrete_on_empty.
  Hypothesis concrete_op_returns_arg : forall n m,
    concrete_op n m = n \/ concrete_op n m = m.
  Hypothesis concrete_op_preserves_op1 : forall n m,
    op (concrete_op n m) m.
  Hypothesis concrete_op_preserves_op2 : forall n m,
    op (concrete_op n m) n.
  Hypothesis op_refl : Reflexive op.
  Hypothesis op_trans : Transitive op.

  Definition is_op1 (l : list nat) : Comp (nat : Type) :=
    (ret (match l with
            | nil => concrete_on_empty
            | x::xs => fold_left concrete_op xs x
          end))%comp.

  Lemma fold_left_concrete_op_preserves_op l
    : forall acc,
      op (fold_left concrete_op l acc) acc.
  Proof.
    induction l; simpl; eauto.
  Qed.

  Hint Resolve fold_left_concrete_op_preserves_op.

  Local Hint Constructors or.

  Lemma fold_left_concrete_op_returns_in l
    : forall acc,
      acc = fold_left concrete_op l acc
      \/ List.In (fold_left concrete_op l acc) l.
  Proof.
    induction l; simpl; eauto.
    intro acc.
    destruct (IHl acc) as [ IH1' | IH1' ];
      try rewrite <- IH1';
      edestruct concrete_op_returns_arg as [H|H];
      erewrite H;
      eauto.
  Qed.

  Hint Resolve fold_left_concrete_op_returns_in.

  Lemma fold_left_concrete_op_commutes l
  : forall a n, fold_left concrete_op l (concrete_op a n) = concrete_op (fold_left concrete_op l n) a.
  Proof.
    induction l; simpl; trivial.
    intros.
    rewrite <- IHl.
    f_equal.
    auto.
  Qed.

  Lemma op_works l
  : Forall (fun n => match l with
                       | [] => True
                       | v::l => op (fold_left concrete_op l v) n
                     end)
           l.
  Proof.
    induction l; trivial.
    constructor; [ apply fold_left_concrete_op_preserves_op | ].
    destruct l; simpl in *; trivial.
    inversion_clear IHl.
    constructor;
      eauto.
    eapply Forall_impl; [ | eassumption ]; instantiate; simpl.
    intros.
    rewrite fold_left_concrete_op_commutes.
    etransitivity; [ | eassumption ]; eauto.
  Qed.

  Theorem is_op_0_1
    : pointwise_relation _ (refine) is_op0 is_op1.
  Proof.
    intros l v old_hyp.
    unfold is_op1, is_op0 in *.
    apply computes_to_inv in old_hyp.
    subst.
    constructor.
    destruct l; simpl.
    - hnf; simpl; intuition.
    - split; [ | left; apply fold_left_concrete_op_returns_in ].
      apply (op_works (_::_)).
  Qed.

  Theorem is_op_0_1' l
    : refine
             { x : nat
             | is_op l x }%comp
             (ret (match l with
                     | nil => concrete_on_empty
                     | x::xs => fold_left concrete_op xs x
                   end))%comp.
  Proof.
    apply is_op_0_1.
  Qed.
End op_funcs.

Create HintDb op discriminated.

Hint Unfold is_op0 is_op1 : op.

Section min_max_funcs.
  Notation is_minimum := (is_op le (eq 0)).
  Notation is_maximum := (is_op ge (eq 0)).
  Notation is_min_max l min_max :=
    (is_minimum l (fst (min_max : nat * nat)) /\ is_maximum l (snd min_max)).

  Hint Resolve min_comm max_comm min_assoc max_assoc.
  Hint Extern 0 => edestruct max_dec; solve [ left; eassumption | right; eassumption ].
  Hint Extern 0 => edestruct min_dec; solve [ left; eassumption | right; eassumption ].
  Hint Extern 0 => eapply min_glb_r; reflexivity.
  Hint Extern 0 => eapply min_glb_l; reflexivity.
  Hint Extern 0 => eapply max_lub_r; reflexivity.
  Hint Extern 0 => eapply max_lub_l; reflexivity.
  Hint Extern 0 => solve [ constructor ].
  Hint Extern 0 => compute; intros; etransitivity; eassumption.

  Program Definition refine_is_minimum l : refine _ _
    := @is_op_0_1' le (eq 0) min 0 _ _ _ _ _ _ _ _ l.

  Program Definition refine_is_maximum  l : refine _ _
    := @is_op_0_1' ge (eq 0) max 0 _ _ _ _ _ _ _ _ l.

  Definition is_min_max1 : { f : list nat -> Comp (nat * nat)
    | forall l, refine { x : _ | is_min_max l x }%comp (f l) }.
  Proof.
    eexists.
    intros.
    set_evars.
    setoid_rewrite refineEquiv_pick_pair.
    setoid_rewrite refine_is_minimum.
    setoid_rewrite refine_is_maximum.
    exact (reflexivity _).
  Defined.
End min_max_funcs.
