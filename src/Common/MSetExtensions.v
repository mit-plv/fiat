Require Export Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetProperties
        Coq.MSets.MSetFacts
        Coq.MSets.MSetDecide.
Require Import Fiat.Common.Instances.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.

Module MSetExtensionsOn (E: DecidableType) (Import M: WSetsOn E).
  Module Export BasicFacts := WFactsOn E M.
  Module Export BasicProperties := WPropertiesOn E M.
  Module Export BasicDec := WDecideOn E M.

  Definition of_list (ls : list E.t) : t
    := List.fold_right
         add
         empty
         ls.

  Global Instance Equal_Equivalence : Equivalence Equal := _.

  Global Instance equal_Equivalence : Equivalence equal.
  Proof.
    setoid_rewrite <- equal_iff; exact _.
  Qed.

  Tactic Notation "setoid_rewrite_in_all" "guarded" tactic3(guard_tac) open_constr(lem) :=
    idtac;
    match goal with
    | [ |- ?G ] => guard_tac G; rewrite !lem
    | [ H : ?T |- _ ] => guard_tac T; rewrite !lem in H
    | [ |- ?G ] => guard_tac G; setoid_rewrite lem
    | [ H : ?T |- _ ] => guard_tac T; setoid_rewrite lem in H
    end.
  Tactic Notation "setoid_rewrite_in_all" open_constr(lem) := setoid_rewrite_in_all guarded(fun T => idtac) lem.

  Tactic Notation "setoid_rewrite_in_all" "guarded" tactic3(guard_tac) "<-" open_constr(lem) :=
    idtac;
    match goal with
    | [ |- ?G ] => guard_tac G; rewrite <- !lem
    | [ H : ?T |- _ ] => guard_tac T; rewrite <- !lem in H
    | [ |- ?G ] => guard_tac G; setoid_rewrite <- lem
    | [ H : ?T |- _ ] => guard_tac T; setoid_rewrite <- lem in H
    end.
  Tactic Notation "setoid_rewrite_in_all" "<-" open_constr(lem) := setoid_rewrite_in_all guarded(fun T => idtac) <- lem.

  Ltac eq_bools_to_is_trues :=
    idtac;
    let x := match goal with |- ?x = ?y :> bool => x end in
    let y := match goal with |- x = ?y :> bool => y end in
    let Hx := fresh in
    let Hy := fresh in
    destruct x eqn:Hx;
    [ symmetry
    | destruct y eqn:Hy;
      [ rewrite <- Hx; clear Hx
      | reflexivity ] ];
    fold_is_true.

  Ltac eq_bools_to_is_trues_in H :=
    idtac;
    let x := match type of H with ?x = ?y :> bool => x end in
    let y := match type of H with x = ?y :> bool => y end in
    let Hx := fresh in
    let Hy := fresh in
    destruct x eqn:Hx;
    [ symmetry
    | destruct y eqn:Hy;
      [ rewrite <- Hx; clear Hx
      | reflexivity ] ];
    fold_is_true.
  Ltac eq_bools_to_is_trues_in_all :=
    idtac;
    match goal with
    | [ H : _ = _ :> bool |- _ ]
      => eq_bools_to_is_trues_in H
    end.

  Ltac to_caps_step :=
    first [ setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[subset _ _ = true] => idtac
                                                | context[is_true (subset _ _)] => idtac
                                                end)
                                  subset_spec
          | setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[equal _ _ = true] => idtac
                                                | context[is_true (equal _ _)] => idtac
                                                end)
                                  equal_spec
          | setoid_rewrite_in_all guarded(fun T => match T with context[_ = false] => idtac end)
                                  <- not_true_iff_false
          | setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[negb _ = true] => idtac
                                                | context[is_true (negb _)] => idtac
                                                end)
                                  negb_true_iff
          | setoid_rewrite_in_all guarded(fun T => match T with
                                                | context[mem _ _ = true] => idtac
                                                | context[is_true (mem _ _)] => idtac
                                                end)
                                  mem_spec
          | progress fold_is_true
          | progress eq_bools_to_is_trues
          | progress eq_bools_to_is_trues_in_all ].
  Ltac to_caps := repeat to_caps_step.

  Create HintDb sets discriminated.
  Create HintDb setsb discriminated.
  Global Hint Immediate union_subset_1 union_subset_2 inter_subset_1 inter_subset_2 equal_refl : sets.
  Global Hint Resolve (BasicFacts.inter_s_m : forall x y _ x' y' _, _) : sets.

  Ltac simplify_sets_step :=
    idtac;
    match goal with
    | [ H : ?x [<=] ?y, H' : ?y [<=] ?x |- _ ]
      => pose proof (subset_antisym H H');
         clear H H'
    | [ H : context[subset ?x ?y] |- _ ]
      => match type of H with
         | context[subset y x] => fail 1
         | _ => idtac
         end;
         progress replace (equal y x) with (equal x y)
           in H by auto with sets
    | [ |- context[subset ?x ?y] ]
      => match goal with
         | [ |- context[subset y x] ] => fail 1
         | _ => idtac
         end;
         progress replace (equal y x) with (equal x y)
           by auto with sets
    | _ => setoid_subst_rel Equal
    end.

  Ltac simplify_sets := repeat simplify_sets_step.

  Ltac push_In_step :=
    first [ progress unfold Equal in *
          | setoid_rewrite_in_all guarded(fun T => match T with context[In _ (union _ _)] => idtac end)
                                  union_spec
          | setoid_rewrite_in_all guarded(fun T => match T with context[In _ (inter _ _)] => idtac end)
                                  inter_spec
          | setoid_rewrite_in_all guarded(fun T => match T with context[In _ (filter _ _)] => idtac end)
                                  filter_spec; [ | let H := fresh in intros ?? H; hnf in H; substs; reflexivity.. ] ].

  Ltac push_In := repeat push_In_step.

  Lemma equal_refl_b x : equal x x.
  Proof. to_caps; auto with sets. Qed.

  Lemma equal_sym_b x y : equal x y = equal y x.
  Proof. to_caps; fsetdec. Qed.

  Hint Immediate equal_sym_b : sets.

  Lemma union_subset_1b
    : forall s s', subset s (union s s').
  Proof. to_caps; auto with sets. Qed.

  Lemma union_subset_2b
    : forall s s', subset s' (union s s').
  Proof. to_caps; auto with sets. Qed.

  Lemma inter_subset_1b
    : forall s s', subset (inter s s') s.
  Proof. to_caps; auto with sets. Qed.

  Lemma inter_subset_2b
    : forall s s', subset (inter s s') s'.
  Proof. to_caps; auto with sets. Qed.

  Hint Rewrite union_subset_1b union_subset_2b inter_subset_1b inter_subset_2b equal_refl_b : setsb.

  Lemma union_idempotent x : Equal (union x x) x.
  Proof. fsetdec. Qed.

  Lemma inter_idempotent x : Equal (inter x x) x.
  Proof. fsetdec. Qed.

  Hint Immediate union_idempotent inter_idempotent : sets.

  Lemma union_idempotent_b x : equal (union x x) x.
  Proof. to_caps; auto with sets. Qed.

  Lemma inter_idempotent_b x : equal (inter x x) x.
  Proof. to_caps; auto with sets. Qed.

  Hint Rewrite union_idempotent_b inter_idempotent_b : sets.

  Global Instance Subset_Proper_Equal_iff
    : Proper (Equal ==> Equal ==> iff) Subset.
  Proof. repeat intro; split; fsetdec. Qed.
  Global Instance Subset_Proper_Equal : Proper (Equal ==> Equal ==> impl) Subset | 1.
  Proof. repeat intro; fsetdec. Qed.
  Global Instance Subset_Proper_Equal_flip : Proper (Equal ==> Equal ==> flip impl) Subset | 1.
  Proof. repeat intro; fsetdec. Qed.

  Global Instance subset_Proper_equal
    : Proper (equal ==> equal ==> Logic.eq) subset.
  Proof. repeat intro; to_caps; fsetdec. Qed.

  Lemma equal_or_subset_and_not_equal_subset_b {x y}
    : (equal x y || (subset x y && negb (equal x y))) = subset x y.
  Proof. to_caps; bool_congr_setoid; to_caps; intuition; try fsetdec. Qed.

  Lemma equal_or_subset_and_not_equal_subset {x y}
    : (Equal x y \/ (Subset x y /\ ~Equal x y)) <-> Subset x y.
  Proof.
    destruct (equal x y) eqn:?; simpl; bool_congr; to_caps; simplify_sets;
      intuition.
  Qed.

  Hint Rewrite @equal_or_subset_and_not_equal_subset : sets.
  Hint Rewrite @equal_or_subset_and_not_equal_subset_b : setsb.

  Ltac handle_known_comparisons_step :=
    idtac;
    lazymatch goal with
    | [ |- context[subset (inter ?x ?y) ?x] ]
      => replace (subset (inter x y) x) with true by (symmetry; apply inter_subset_1b)
    | [ |- context[subset (inter ?x ?y) ?y] ]
      => replace (subset (inter x y) y) with true by (symmetry; apply inter_subset_2b)
    | [ |- context[subset ?x (union ?x ?y)] ]
      => replace (subset x (union x y)) with true by (symmetry; apply union_subset_1b)
    | [ |- context[subset ?y (union ?x ?y)] ]
      => replace (subset y (union x y)) with true by (symmetry; apply union_subset_2b)
    | [ |- context[equal (?f ?x ?y) ?x] ]
      => replace (equal (f x y) x) with (equal x (f x y)) by apply equal_sym_b
    | [ |- context[equal (?f ?x ?y) ?y] ]
      => replace (equal (f x y) y) with (equal y (f x y)) by apply equal_sym_b
    end.

  Ltac handle_known_comparisons := repeat handle_known_comparisons_step.

  Ltac cardinal_to_list_step :=
    idtac;
    match goal with
    | [ H : cardinal _ = _ |- _ ]
      => rewrite cardinal_spec in H
    | [ H : List.length ?ls = S _ |- _ ]
      => destruct ls eqn:?; simpl in H; inversion H; clear H
    | [ H : List.length ?ls = 0 |- _ ]
      => destruct ls eqn:?; simpl in H; inversion H; clear H
    | [ H : ?ls = nil |- _ ] => is_var ls; subst ls
    | [ H : ?ls = (_::_) |- _ ] => is_var ls; subst ls
    end.
  Ltac cardinal_to_list := repeat cardinal_to_list_step.
  Ltac in_to_elements :=
    repeat (setoid_rewrite_in_all guarded(fun T => match T with context[In _ _] => idtac end)
                                  BasicFacts.elements_iff);
    repeat match goal with
           | [ H : elements ?v = _ |- _ ]
             => rewrite !H
           | [ H : elements ?v = _, H' : appcontext[elements ?v] |- _ ]
             => rewrite !H in H'
           end.
  Ltac InA_concretize_step :=
    idtac;
    match goal with
    | _ => progress substs
    | [ H : SetoidList.InA _ _ nil |- _ ] => solve [ inversion H ]
    | [ H : SetoidList.InA _ _ (_::_) |- _ ] => inversion H; clear H
    | [ |- ~SetoidList.InA _ _ _ ] => intro
    end.
  Ltac InA_concretitze := repeat InA_concretize_step.

  Lemma cardinal_one_In_same v
        (H : cardinal v = 1)
    : forall x y, In x v -> In y v -> E.eq x y.
  Proof.
    cardinal_to_list.
    intros; in_to_elements; InA_concretitze.
    fsetdec.
  Qed.
End MSetExtensionsOn.

Module MSetExtensions (M: Sets) := MSetExtensionsOn M.E M.
