Require Import List Ensembles String Setoid RelationClasses Morphisms Morphisms_Prop Program Equivalence Min Max Permutation Sorted.
Require Import JMeq ProofIrrelevance.
Require Import Common Computation.

Section formulas.
  Inductive formula (vars : Type) :=
  | Atomic : vars -> formula vars
  | And : formula vars -> formula vars -> formula vars
  | Not : formula vars -> formula vars
  | TrueF : formula vars.

  Fixpoint get_vars vars (f : formula vars) : Ensemble vars :=
    match f with
      | Atomic x => Singleton _ x
      | And x y => Union _ (get_vars x) (get_vars y)
      | Not x => get_vars x
      | TrueF => Empty_set _
    end.

  Fixpoint denote_formula vars (bool_map : vars -> bool) (f : formula vars)
  : bool
    := match f with
         | Atomic x => bool_map x
         | And x y => andb (denote_formula bool_map x) (denote_formula bool_map y)
         | Not x => negb (denote_formula bool_map x)
         | TrueF => true
       end.

  Definition is_satisfiable vars (f : formula vars) : Prop
    := exists bool_map, denote_formula bool_map f = true.

  Fixpoint subst_vars vars (bool_map : vars -> vars + bool) (f : formula vars)
  : formula vars
    := match f with
         | TrueF => TrueF _
         | Atomic x => match bool_map x with
                         | inl x' => Atomic x'
                         | inr b => if b then TrueF _ else Not (TrueF _)
                       end
         | And x y => And (subst_vars bool_map x) (subst_vars bool_map y)
         | Not x => Not (subst_vars bool_map x)
       end.
End formulas.

Section op_funcs.
  Variable op : nat -> nat -> Prop.
  Variable on_empty : nat -> Prop.
  Definition is_op (l : list nat) (v : nat)
    := Forall (fun n => op v n) l /\ (List.In v l \/ (l = nil /\ on_empty v)).

  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

  Definition is_op0 (l : list nat) : Comp funcs nat :=
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

  Definition is_op1 (l : list nat) : Comp funcs (nat : Type) :=
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
    : pointwise_relation _ (refine denote_funcs denote_funcs) is_op0 is_op1.
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
    : refine denote_funcs denote_funcs
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

  Variable funcs : string -> Type * Type.
  Variable denote_funcs : forall name, fst (funcs name) -> Comp funcs (snd (funcs name)).

  Hint Resolve min_comm max_comm min_assoc max_assoc.
  Hint Extern 0 => edestruct max_dec; solve [ left; eassumption | right; eassumption ].
  Hint Extern 0 => edestruct min_dec; solve [ left; eassumption | right; eassumption ].
  Hint Extern 0 => eapply min_glb_r; reflexivity.
  Hint Extern 0 => eapply min_glb_l; reflexivity.
  Hint Extern 0 => eapply max_lub_r; reflexivity.
  Hint Extern 0 => eapply max_lub_l; reflexivity.
  Hint Extern 0 => solve [ constructor ].
  Hint Extern 0 => compute; intros; etransitivity; eassumption.

  Program Definition refine_is_minimum l : refine denote_funcs denote_funcs _ _
    := @is_op_0_1' le (eq 0) funcs denote_funcs min 0 _ _ _ _ _ _ _ _ l.
  Program Definition refine_is_maximum l : refine denote_funcs denote_funcs _ _
    := @is_op_0_1' ge (eq 0) funcs denote_funcs max 0 _ _ _ _ _ _ _ _ l.

  Definition is_min_max1 : { f : list nat -> Comp funcs (nat * nat)
    | forall l, refine denote_funcs denote_funcs { x : _ | is_min_max l x }%comp (f l) }.
  Proof.
    eexists.
    intros.
    set_evars.
    setoid_rewrite refine_pick_pair.
    setoid_rewrite refine_is_minimum.
    setoid_rewrite refine_is_maximum.
    exact (reflexivity _).
  Defined.
End min_max_funcs.

(*Section sort.
  Variable T : Type.
  Variable R : relation T.

  Definition sort0 funcs (l : list T) : Comp funcs (list T)
    := { l' : list T | Sorted R l' /\ Permutation l l' }%comp.

  Variable pre_funcs : string -> Type * Type.

  Definition funcs : string -> Type * Type
    := (fun s =>
          if string_dec s "sort"
          then (list T, list T)
          else pre_funcs s).

  Definition sort1 (l : list T) : Comp funcs (list T)
    := (x <- { x : T | List.In x l /\ Forall (R x) l };
        xs <- { xs : list T | Permutation (x::xs) l };
        xs' <- call "sort" from funcs [[ xs ]];
        ret (x::xs'))%comp.

  Definition sort2 (l : list T) : Comp funcs (list T)
*)


Section sat_funcs.
  Variable var : Type.
  Variable dec_eq : forall x y : var, {x = y} + {x <> y}.

  Definition sat0 funcs (f : formula var) : Comp funcs bool
    := { b : bool | b = true <-> is_satisfiable f }%comp.

  Definition funcs : string -> Type * Type
    := (fun s =>
          if string_dec s "sat"
          then (formula var, bool : Type)
          else (Datatypes.Empty_set : Type, unit : Type)).

  Definition sat1 (f : formula var)
  : Comp funcs bool :=
    (x0 <- { x0 : option var
           | (x0 = None /\ get_vars f = Empty_set _)
             \/ (exists x', x0 = Some x' /\ In _ (get_vars f) x') };
     match x0 with
       | None => ret (denote_formula (fun _ => false (* do we want to use a [Prop] here? *)) f)
       | Some x0 =>
         let bool_map_t v := if dec_eq x0 v then inr true else inl v in
         let bool_map_f v := if dec_eq x0 v then inr false else inl v in
         let formula_t := subst_vars bool_map_t f in
         let formula_f := subst_vars bool_map_f f in
         Or (call "sat" from funcs [[ formula_t ]]) (call "sat" from funcs [[ formula_f ]])
     end)%comp.

  Lemma sat_0_1 denote_funcs f : refine denote_funcs denote_funcs (sat0 funcs f) (sat1 f).
  Proof.
    unfold sat0.
  Admitted.
End sat_funcs.
