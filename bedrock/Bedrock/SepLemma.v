Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import Bedrock.Expr Bedrock.SepExpr.
Require Import Bedrock.Reflection.
Require Import Bedrock.Folds.

Set Implicit Arguments.
Set Strict Implicit.

Module Type SepLemma.
  Declare Module SE : SepExpr.

  Section typed.
    Variable types : list type.
    Variables pcType stateType : tvar.

    (** The type of one unfolding lemma *)
    Record lemma := {
      Foralls : variables;
      (* The lemma statement begins with this sequence of [forall] quantifiers over these types. *)
      Hyps : list (expr types);
      (* Next, we have this sequence of pure hypotheses. *)
      Lhs : SE.sexpr types pcType stateType;
      Rhs : SE.sexpr types pcType stateType
      (* Finally, we have this separation implication, with lefthand and righthand sides. *)
    }.

    Definition WellTyped_lemma tfuncs tpreds (l : lemma) : bool :=
      allb (fun x => is_well_typed tfuncs nil (Foralls l) x tvProp) (Hyps l) &&
      SE.WellTyped_sexpr tfuncs tpreds nil (Foralls l) (Lhs l) &&
      SE.WellTyped_sexpr tfuncs tpreds nil (Foralls l) (Rhs l).

    Variable funcs : functions types.

    (** Helper function to add a sequence of implications in front of a [Prop] *)
    Definition hypD (H : expr types) (meta_env var_env : env types) : Prop :=
      match exprD funcs meta_env var_env H tvProp with
        | None => False
        | Some P => P
      end.

    Fixpoint implyEach (Hs : list (expr types)) (meta_env var_env : env types) (P : Prop) : Prop :=
      match Hs with
        | nil => P
        | H :: Hs' => hypD H meta_env var_env -> implyEach Hs' meta_env var_env P
      end.

    (** The meaning of a lemma statement *)

    (* Redefine to use the opposite quantifier order *)
    Fixpoint forallEachR (ls : variables) : (env types -> Prop) -> Prop :=
      match ls with
        | nil => fun cc => cc nil
        | a :: b => fun cc =>
          forallEachR b (fun r => forall x : tvarD types a, cc (existT _ a x :: r))
      end.

    Variable preds : SE.predicates types pcType stateType.

    Definition lemmaD (meta_base var_base : env types) (lem : lemma) : Prop :=
      WellTyped_lemma (typeof_funcs funcs) (SE.typeof_preds preds) lem = true /\
      forallEachR (Foralls lem) (fun env =>
        implyEach (Hyps lem) meta_base (var_base ++ env)
        (forall specs, SE.himp funcs preds meta_base (var_base ++ env) specs (Lhs lem) (Rhs lem))).

    (** Lemmas **)
    Axiom forallEachR_sem : forall vs P,
      forallEachR vs P <-> (forall e, map (@projT1 _ _) e = vs -> P e).

    Axiom implyEach_instantiate : forall HYPS U G,
      AllProvable funcs U G HYPS ->
      forall cc,
        implyEach HYPS U G cc ->
        cc.

    Axiom implyEach_sem : forall cc U G es,
      implyEach es U G cc <-> (AllProvable funcs U G es -> cc).

  End typed.
End SepLemma.

Module Make (SE : SepExpr) : SepLemma with Module SE := SE.
  Module SE := SE.

  Section typed.
    Variable types : list type.
    Variables pcType stateType : tvar.

    (** The type of one unfolding lemma *)
    Record lemma := {
      Foralls : variables;
      (* The lemma statement begins with this sequence of [forall] quantifiers over these types. *)
      Hyps : list (expr types);
      (* Next, we have this sequence of pure hypotheses. *)
      Lhs : SE.sexpr types pcType stateType;
      Rhs : SE.sexpr types pcType stateType
      (* Finally, we have this separation implication, with lefthand and righthand sides. *)
    }.

    Definition WellTyped_lemma tfuncs tpreds (l : lemma) : bool :=
      allb (fun x => is_well_typed tfuncs nil (Foralls l) x tvProp) (Hyps l) &&
      SE.WellTyped_sexpr tfuncs tpreds nil (Foralls l) (Lhs l) &&
      SE.WellTyped_sexpr tfuncs tpreds nil (Foralls l) (Rhs l).

    Variable funcs : functions types.

    (** Helper function to add a sequence of implications in front of a [Prop] *)
    Definition hypD (H : expr types) (meta_env var_env : env types) : Prop :=
      match exprD funcs meta_env var_env H tvProp with
        | None => False
        | Some P => P
      end.

    Fixpoint implyEach (Hs : list (expr types)) (meta_env var_env : env types) (P : Prop) : Prop :=
      match Hs with
        | nil => P
        | H :: Hs' => hypD H meta_env var_env -> implyEach Hs' meta_env var_env P
      end.

    (** The meaning of a lemma statement *)

    (* Redefine to use the opposite quantifier order *)
    Fixpoint forallEachR (ls : variables) : (env types -> Prop) -> Prop :=
      match ls with
        | nil => fun cc => cc nil
        | a :: b => fun cc =>
          forallEachR b (fun r => forall x : tvarD types a, cc (existT _ a x :: r))
      end.

    Variable preds : SE.predicates types pcType stateType.

    Definition lemmaD (meta_base var_base : env types) (lem : lemma) : Prop :=
      WellTyped_lemma (typeof_funcs funcs) (SE.typeof_preds preds) lem = true /\
      forallEachR (Foralls lem) (fun env =>
        implyEach (Hyps lem) meta_base (var_base ++ env)
        (forall specs, SE.himp funcs preds meta_base (var_base ++ env) specs (Lhs lem) (Rhs lem))).

    (** Lemmas **)
    Lemma forallEachR_sem : forall vs P,
      forallEachR vs P <-> (forall e, map (@projT1 _ _) e = vs -> P e).
    Proof.
      clear. split; revert P; induction vs; simpl; intros.
      destruct e; simpl in *; try congruence.
      destruct e; simpl in *; try congruence. inversion H0; clear H0; subst. eapply IHvs in H; eauto.
      destruct s; eapply H.
      eapply H; reflexivity.
      eapply IHvs; intros. eapply H. simpl. f_equal; auto.
    Qed.

    Lemma implyEach_instantiate : forall HYPS U G,
      AllProvable funcs U G HYPS ->
      forall cc,
        implyEach HYPS U G cc ->
        cc.
    Proof.
      induction HYPS; simpl; intros; auto;
        repeat match goal with
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ H : _ && _ = _ |- _ ] =>
                   apply andb_true_iff in H; destruct H
               end.
      eapply IHHYPS; eauto.
    Qed.

    Lemma implyEach_sem : forall cc U G es,
      implyEach es U G cc <-> (AllProvable funcs U G es -> cc).
    Proof. clear; induction es; simpl; intuition. Qed.

  End typed.
End Make.
