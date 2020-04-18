Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Make E.

  Section TopSection.

    Require Import Bedrock.Platform.Cito.Syntax.
    Require Import Bedrock.Platform.AutoSep.
    Require Import Bedrock.Platform.Cito.GLabel.

    Definition Env := ((glabel -> option W) * (W -> option Callee))%type.

    (* shallow embedding *)
    Definition assert := Env -> State -> State -> Prop.
    Definition entailment := Env -> Prop.

    Inductive StmtEx :=
    | SkipEx : StmtEx
    | SeqEx : StmtEx -> StmtEx -> StmtEx
    | IfEx : Expr -> StmtEx -> StmtEx -> StmtEx
    | WhileEx : assert -> Expr -> StmtEx -> StmtEx
    | AssignEx : string -> Expr -> StmtEx
    | AssertEx : assert -> StmtEx
    | CallEx : option string -> Expr -> list Expr -> StmtEx
    | LabelEx : string -> glabel -> StmtEx.

    Definition and_lift (a b : assert) : assert := fun env v v' => a env v v' /\ b env v v'.
    Definition or_lift (a b : assert) : assert := fun env v v' => a env v v' \/ b env v v'.
    Definition imply_close (a b : assert) : entailment := fun env => forall v v', a env v v' -> b env v v'.

    Infix "/\" := and_lift : assert_scope.
    Infix "\/" := or_lift : assert_scope.
    Infix "-->" := imply_close (at level 90) : assert_scope.

    Require Import Bedrock.Platform.Cito.SemanticsExpr.

    Close Scope equiv_scope.

    Definition is_true e : assert := fun _ _ v => eval (fst v) e <> $0.
    Definition is_false e : assert := fun _ _ v => eval (fst v) e = $0.

    Open Scope assert_scope.

    Fixpoint to_stmt s :=
      match s with
        | SkipEx => Syntax.Skip
        | SeqEx a b => Syntax.Seq (to_stmt a) (to_stmt b)
        | IfEx e t f => Syntax.If e (to_stmt t) (to_stmt f)
        | WhileEx _ e b => Syntax.While e (to_stmt b)
        | AssignEx x e => Syntax.Assign x e
        | AssertEx _ => Syntax.Skip
        | CallEx x f args => Syntax.Call x f args
        | LabelEx x lbl => Syntax.Label x lbl
      end.

    Coercion to_stmt : StmtEx >-> Stmt.

    Fixpoint sp (stmt : StmtEx) (p : assert) : assert :=
      match stmt with
        | SeqEx a b => sp b (sp a p)
        | IfEx e t f => sp t (p /\ is_true e) \/ sp f (p /\ is_false e)
        | WhileEx inv e _ => inv /\ is_false e
        | AssertEx a => a
        | SkipEx => p
        | _ =>
          (fun env v0 v' =>
             exists v,
               p env v0 v /\
               RunsTo env stmt v v')%type
      end.

    Fixpoint vc stmt (p : assert) : list entailment :=
      match stmt with
        | SeqEx a b => vc a p ++ vc b (sp a p)
        | IfEx e t f => vc t (p /\ is_true e) ++ vc f (p /\ is_false e)
        | WhileEx inv e body =>
          (p --> inv) :: (sp body (inv /\ is_true e) --> inv) :: vc body (inv /\ is_true e)
        | AssertEx a => (p --> a) :: nil
        | SkipEx => nil
        | AssignEx _ _ => nil
        | _ => (p --> (fun env _ v => Safe env stmt v)) :: nil
      end.

    Definition and_all : list entailment -> entailment := fold_right (fun a b env => a env /\ b env)%type (fun _ => True).

    Require Import Bedrock.Platform.Cito.GeneralTactics.

    Lemma and_all_app : forall ls1 ls2 env, and_all (ls1 ++ ls2) env -> and_all ls1 env /\ and_all ls2 env.
      induction ls1; simpl; intuition.
      eapply IHls1 in H1; openhyp; eauto.
      eapply IHls1 in H1; openhyp; eauto.
    Qed.

    Lemma is_true_intro : forall e env v v', wneb (eval (fst v') e) $0 = true -> (is_true e) env v v'.
      intros.
      unfold is_true.
      unfold wneb in *.
      destruct (weq _ _) in *; intuition.
    Qed.

    Hint Resolve is_true_intro.

    Lemma is_false_intro : forall e env v v', wneb (eval (fst v') e) $0 = false -> (is_false e) env v v'.
      intros.
      unfold is_false.
      unfold wneb in *.
      destruct (weq _ _) in *; intuition.
    Qed.

    Hint Resolve is_false_intro.

    Hint Unfold RunsTo.
    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe.
    Hint Constructors Semantics.Safe.

    Ltac unfold_all :=
      repeat match goal with
               | H := _ |- _ => unfold H in *; clear H
             end.

    Ltac inject :=
      match goal with
        | H : _ = _ |- _ => unfold_all; injection H; intros; subst
      end.

    Lemma sound_runsto' : forall env (s : Stmt) v v', RunsTo env s v v' -> forall s' : StmtEx, s = s' -> forall p, and_all (vc s' p) env -> forall v0, p env v0 v -> (sp s' p) env v0 v'.
      induction 1; simpl; intros; destruct s'; try discriminate; simpl in *; try inject.

      (* skip *)
      eauto.

      openhyp.
      eauto.

      (* seq *)
      eapply and_all_app in H2; openhyp.
      eauto.

      (* if *)
      eapply and_all_app in H2; openhyp.
      left.
      eapply IHRunsTo; eauto.
      split; eauto.

      eapply and_all_app in H2; openhyp.
      right.
      eapply IHRunsTo; eauto.
      split; eauto.

      (* while *)
      openhyp.
      eapply (IHRunsTo2 (WhileEx _ e s')); simpl in *; eauto.
      eapply IHRunsTo1; simpl in *; eauto.
      split; eauto.

      openhyp.
      split; eauto.

      Focus 4.
      (* assign *)
      eauto.

      Focus 3.
      (* label *)
      eauto.

      (* call *)
      eauto.
      eauto.
    Qed.

    Theorem sound_runsto : forall env (s : StmtEx) v v' p v0, RunsTo env s v v' -> and_all (vc s p) env -> p env v0 v -> (sp s p) env v0 v'.
      intros.
      eapply sound_runsto'; eauto.
    Qed.

    Theorem sound_safe : forall env (s : Stmt) (s' : StmtEx) v p v0, s = s' -> and_all (vc s' p) env -> p env v0 v -> Safe env s v.
      intros.
      Close Scope assert_scope.
      eapply (Safe_coind (fun s v => Safe env s v \/ exists (s' : StmtEx) p v0, s = s' /\ and_all (vc s' p) env /\ p env v0 v)); [ .. | right; descend; eauto]; clear; intros; openhyp.

      (* seq *)
      inversion H; subst.
      descend; left; eauto.

      destruct x; try discriminate; simpl in *; try inject.
      eapply and_all_app in H0; openhyp.
      descend.
      right; descend; eauto.
      intros.
      eapply sound_runsto' with (p := x0) in H3; eauto.
      right; descend; eauto.

      (* if *)
      inversion H; subst.
      openhyp; subst.
      left; descend.
      eauto.
      left; eauto.
      right; descend.
      eauto.
      left; eauto.

      destruct x; try discriminate; simpl in *; try inject.
      eapply and_all_app in H0; openhyp.
      unfold wneb.
      destruct (weq (eval (fst v) e) $0) in *.
      right.
      descend; eauto.
      right; descend; eauto.
      split; eauto.
      left.
      descend; eauto.
      right; descend; eauto.
      split; eauto.

      (* while *)
      inversion H; unfold_all; subst.
      left; descend.
      eauto.
      left; eauto.
      left; eauto.
      right; eauto.

      destruct x; try discriminate; simpl in *; try inject.
      openhyp.
      unfold wneb.
      destruct (weq (eval (fst v) e) $0) in *.
      right.
      eauto.
      left.
      descend; eauto.
      right.
      descend; eauto.
      split; eauto.
      right.
      eapply sound_runsto' with (p := and_lift a (is_true e)) in H4; eauto.
      descend.
      instantiate (1 := WhileEx _ e x).
      eauto.
      2 : eauto.
      simpl.
      descend; eauto.
      split; eauto.

      (* call *)
      inversion H; unfold_all; subst.
      left; descend; eauto.
      right; descend; eauto.

      destruct x; try discriminate; simpl in *; try inject.
      openhyp.
      eapply H0 in H1.
      inversion H1; unfold_all; subst.
      left; descend; eauto.
      right; descend; eauto.

      (* label *)
      inversion H; unfold_all; subst.
      eauto.

      destruct x0; try discriminate; simpl in *; try inject.
      eapply H0 in H1.
      inversion H1; unfold_all; subst.
      eauto.
    Qed.

  End TopSection.

End Make.
