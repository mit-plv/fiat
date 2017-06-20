Require Coq.Lists.List.
Require Import Coq.Program.Basics.

Section LogicFacts.
  Lemma or_false :
    forall (P: Prop), P \/ False <-> P.
  Proof.
    tauto.
  Qed.

  Lemma false_or :
    forall (P Q: Prop),
      (False <-> P \/ Q) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma false_or' :
    forall (P Q: Prop),
      (P \/ Q <-> False) <-> (False <-> P) /\ (False <-> Q).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false :
    forall P,
      (False <-> P) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma equiv_false' :
    forall P,
      (P <-> False) <-> (~ P).
  Proof.
    tauto.
  Qed.

  Lemma and_True :
    forall P,
      (P /\ True) <-> P.
  Proof.
    tauto.
  Qed.

  Lemma not_exists_forall :
    forall {A} (P: A -> Prop),
      (~ (exists a, P a)) <-> (forall a, ~ P a).
  Proof.
    firstorder.
  Qed.

  Lemma not_and_implication :
    forall (P Q: Prop),
      ( ~ (P /\ Q) ) <-> (P -> ~ Q).
  Proof.
    firstorder.
  Qed.

  Lemma eq_sym_iff :
    forall {A} x y, @eq A x y <-> @eq A y x.
  Proof.
    split; intros; symmetry; assumption.
  Qed.

  Lemma fold_right_and_True {ls : list Prop}
  : List.fold_right and True ls <-> (forall P, List.In P ls -> P).
  Proof.
    split; induction ls; simpl in *; repeat (subst || intros [] || intro);
    repeat split; try assumption;
    try apply IHls; intros; eauto;
    match goal with
      | [ H : _ |- _ ]
        => apply H; solve [ left; reflexivity | right; assumption ]
    end.
  Qed.

  Lemma fold_right_and_True_map {A} {P : A -> Prop} {ls : list A}
  : List.fold_right and True (List.map P ls) <-> (forall x, List.In x ls -> P x).
  Proof.
    rewrite fold_right_and_True; split; intros H x Hx.
    { apply H, List.in_map, Hx. }
    { apply List.in_map_iff in Hx.
      destruct Hx as [? [? ?]]; subst; eauto. }
  Qed.

  Lemma forall_iff {A B C}
  : (forall x : A, (B x <-> C x)) -> ((forall x, B x) <-> (forall x, C x)).
  Proof.
    intro H; split; intros H' x; apply H, H'.
  Qed.

  Lemma forall_impl {A B C}
  : (forall x : A, (impl (B x) (C x))) -> (impl (forall x, B x) (forall x, C x)).
  Proof.
    intro H; intros H' x; apply H, H'.
  Qed.

  Lemma and_distr_or_r A B C
  : (A /\ (B \/ C)) <-> ((A /\ B) \/ (A /\ C)).
  Proof. tauto. Qed.
  Lemma and_distr_or_l A B C
  : ((B \/ C) /\ A) <-> ((B /\ A) \/ (C /\ A)).
  Proof. tauto. Qed.
  Lemma ex_distr_or A B C
  : (exists x : A, B x \/ C x) <-> ((exists x : A, B x) \/ (exists x : A, C x)).
  Proof.
    repeat ((intros [H0 H1]; revert H0 H1)
            || (intros [H|H]; revert H)
            || split
            || intro);
    first [ do 2 first [ left | esplit ]; eassumption
          | do 2 first [ right | esplit ]; eassumption ].
  Defined.

  Lemma and_TrueP_L {P Q : Prop} (H : P) : P /\ Q <-> Q.
  Proof. tauto. Qed.
  Lemma and_TrueP_R {P Q : Prop} (H : Q) : P /\ Q <-> P.
  Proof. tauto. Qed.
  Lemma impl_distr_or {A B C : Prop}
    : (A \/ B -> C) <-> ((A -> C) /\ (B -> C)).
  Proof. tauto. Qed.
  Lemma forall_distr_and {A B C}
    : (forall x : A, B x /\ C x) <-> ((forall x, B x) /\ (forall x, C x)).
  Proof.
    split; intro H; split; intros; apply H.
  Qed.
  Lemma ex_eq_and {A P} y
    : (exists x : A, y = x /\ P x) <-> P y.
  Proof.
    split; [ intros [? ?] | intro; eexists ];
      intuition try (tauto || congruence).
  Qed.
  Lemma ex_eq'_and {A P} y
    : (exists x : A, x = y /\ P x) <-> P y.
  Proof.
    split; [ intros [? ?] | intro; eexists ];
      intuition try (tauto || congruence).
  Qed.
  Lemma ex_eq_snd_and {A B C} x
    : (exists y : A * B, snd y = x /\ C y) <-> (exists y : A, C (y, x)).
  Proof.
    split; intros [y H]; try destruct y; eexists; repeat intuition (subst; eauto; simpl).
  Qed.
  Lemma ex_eq'_snd_and {A B C} x
    : (exists y : A * B, x = snd y /\ C y) <-> (exists y : A, C (y, x)).
  Proof.
    split; intros [y H]; try destruct y; eexists; repeat intuition (subst; eauto; simpl).
  Qed.
  Lemma ex_eq_fst_and {A B C} x
    : (exists y : A * B, fst y = x /\ C y) <-> (exists y : B, C (x, y)).
  Proof.
    split; intros [y H]; try destruct y; eexists; repeat intuition (subst; eauto; simpl).
  Qed.
  Lemma ex_eq'_fst_and {A B C} x
    : (exists y : A * B, x = fst y /\ C y) <-> (exists y : B, C (x, y)).
  Proof.
    split; intros [y H]; try destruct y; eexists; repeat intuition (subst; eauto; simpl).
  Qed.
  Lemma forall_eq_and {A C} {D : _ -> Prop} x
    : (forall y : A, y = x /\ C y -> D y) <-> (C x -> D x).
  Proof. repeat firstorder subst. Qed.
  Lemma forall_eq'_and {A C} {D : _ -> Prop} x
    : (forall y : A, x = y /\ C y -> D y) <-> (C x -> D x).
  Proof. repeat firstorder subst. Qed.
  Lemma forall_eq_snd_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, snd y = x /\ C y -> D y) <-> (forall y : A, C (y, x) -> D (y, x)).
  Proof. split; intros H y; try destruct y; repeat firstorder subst. Qed.
  Lemma forall_eq'_snd_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, x = snd y /\ C y -> D y) <-> (forall y : A, C (y, x) -> D (y, x)).
  Proof. split; intros H y; try destruct y; repeat firstorder subst. Qed.
  Lemma forall_eq_fst_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, fst y = x /\ C y -> D y) <-> (forall y : B, C (x, y) -> D (x, y)).
  Proof. split; intros H y; try destruct y; repeat firstorder subst. Qed.
  Lemma forall_eq'_fst_and {A B C} {D : _ -> Prop} x
    : (forall y : A * B, x = fst y /\ C y -> D y) <-> (forall y : B, C (x, y) -> D (x, y)).
  Proof. split; intros H y; try destruct y; repeat firstorder subst. Qed.
  Lemma True_iff {P : Prop}
    : P -> (P <-> True).
  Proof. firstorder. Qed.
  Lemma False_iff {P : Prop}
    : ~P -> (P <-> False).
  Proof. firstorder. Qed.
  Lemma nnTrue : ~~True.
  Proof. tauto. Qed.
  Lemma and_False_r {P} : (P /\ False) <-> False.
  Proof. tauto. Qed.
  Lemma and_False_l {P} : (False /\ P) <-> False.
  Proof. tauto. Qed.
  Lemma and_True_r {P} : (P /\ True) <-> P.
  Proof. tauto. Qed.
  Lemma and_True_l {P} : (True /\ P) <-> P.
  Proof. tauto. Qed.
  Lemma or_False_r {P} : (P \/ False) <-> P.
  Proof. tauto. Qed.
  Lemma or_False_l {P} : (False \/ P) <-> P.
  Proof. tauto. Qed.
  Lemma or_True_r {P} : (P \/ True) <-> True.
  Proof. tauto. Qed.
  Lemma or_True_l {P} : (True \/ P) <-> True.
  Proof. tauto. Qed.
  Lemma ex_False {T} : (exists x : T, False) <-> False.
  Proof. firstorder. Qed.
  Lemma forall_True {T} : (forall x : T, True) <-> True.
  Proof. firstorder. Qed.
  Lemma forall_iff_nondep {A B} {C : Prop} (H : exists x : A, B x)
    : (forall x : A, B x -> C) <-> C.
  Proof. firstorder. Qed.
  Lemma False_impl_iff_True {P : Prop}
    : (False -> P) <-> True.
  Proof. firstorder. Qed.
  Lemma ex_True {T} : (exists x : T, True) <-> inhabited T.
  Proof. firstorder. Qed.

  Lemma ex_ind_iff {T P} {Q : _ -> Prop}
    : (forall pf : @ex T P, Q pf) <-> forall (x : T) (y : P x), Q (ex_intro P x y).
  Proof.
    intuition; destruct_all (ex P); auto.
  Qed.

  Lemma pull_forall_iff {A} (P Q : A -> Prop)
    : (forall x : A, (P x <-> Q x))
      -> ((forall x : A, P x) <-> (forall x : A, Q x)).
  Proof. firstorder eauto. Qed.
End LogicFacts.

Create HintDb logic discriminated.
Hint Rewrite and_distr_or_l and_distr_or_r @ex_distr_or @impl_distr_or @forall_distr_and @ex_eq'_and @ex_eq_and @ex_eq'_fst_and @ex_eq'_snd_and @ex_eq_fst_and @ex_eq_snd_and @forall_eq'_fst_and @forall_eq'_snd_and @forall_eq_fst_and @forall_eq_snd_and and_assoc (True_iff (eq_refl true)) (False_iff nnTrue) @and_False_r @and_False_l @ex_False @and_True_l @and_True_r @or_False_l @or_False_r @or_True_l @or_True_r @forall_True (True_iff Bool.diff_false_true) (False_iff Bool.diff_false_true) @False_impl_iff_True @ex_True : logic.
Ltac setoid_rewrite_logic_step :=
  first [ rewrite_strat repeat topdown hints logic
        | setoid_rewrite ex_distr_or
        | setoid_rewrite forall_distr_and
        | setoid_rewrite ex_eq'_and
        | setoid_rewrite ex_eq'_fst_and
        | setoid_rewrite ex_eq'_snd_and
        | setoid_rewrite ex_eq_and
        | setoid_rewrite ex_eq_fst_and
        | setoid_rewrite ex_eq_snd_and
        | setoid_rewrite forall_eq'_and
        | setoid_rewrite forall_eq'_fst_and
        | setoid_rewrite forall_eq'_snd_and
        | setoid_rewrite forall_eq_and
        | setoid_rewrite forall_eq_fst_and
        | setoid_rewrite forall_eq_snd_and
        | setoid_rewrite False_impl_iff_True ].
Ltac setoid_rewrite_logic := repeat setoid_rewrite_logic_step.
