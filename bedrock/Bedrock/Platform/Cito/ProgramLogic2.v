Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.Transit.
  Require Import Bedrock.Platform.Cito.Semantics.

  Require Import Bedrock.Platform.Cito.Syntax.
  Require Import Bedrock.Platform.Cito.GLabel.
  Require Import Bedrock.Platform.Cito.GLabelMap.
  Import GLabelMap.
  Require Import Bedrock.Platform.Cito.SemanticsExpr.
  Require Import Bedrock.Platform.Cito.GeneralTactics Bedrock.Platform.Cito.GeneralTactics2 Bedrock.Platform.Cito.GeneralTactics3.

  Notation Callee := (@Callee ADTValue).

  Definition Specs := GLabelMap.t Callee.

  Definition f_var := "_f".

  Notation State := (@State ADTValue).

  Definition RunsToDCall specs retvar f args (v v' : State) :=
    match find f specs with
      | Some (Semantics.Foreign spec) =>
        exists inputs outputs ret_w ret_a f_w,
          let vs := upd (fst v) f_var f_w in
          TransitTo spec (List.map (eval vs) args) inputs outputs ret_w ret_a (snd v) (snd v') /\
          fst v' = upd_option vs retvar ret_w
      | _ => True
    end.

  Definition SafeDCall specs f args (v : State) :=
    match find f specs with
      | Some (Semantics.Foreign spec) =>
        forall f_w,
          let vs := upd (fst v) f_var f_w in
          exists inputs, TransitSafe spec (List.map (eval vs) args) inputs (snd v)
      | _ => False
    end.

  (* shallow embedding *)
  Definition assert := Specs -> State -> State -> Prop.
  Definition entailment := Specs -> Prop.

  Inductive StmtEx :=
  | SkipEx : StmtEx
  | SeqEx : StmtEx -> StmtEx -> StmtEx
  | IfEx : Expr -> StmtEx -> StmtEx -> StmtEx
  | WhileEx : assert -> Expr -> StmtEx -> StmtEx
  | AssignEx : string -> Expr -> StmtEx
  | AssertEx : assert -> StmtEx
  | DCallEx : option string -> glabel -> list Expr -> StmtEx.

  Definition and_lift (a b : assert) : assert := fun specs v v' => a specs v v' /\ b specs v v'.
  Definition or_lift (a b : assert) : assert := fun specs v v' => a specs v v' \/ b specs v v'.
  Definition imply_close (a b : assert) : entailment := fun specs => forall v v', a specs v v' -> b specs v v'.

  Infix "/\" := and_lift : assert_scope.
  Infix "\/" := or_lift : assert_scope.
  Infix "-->" := imply_close (at level 90) : assert_scope.

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
      | DCallEx x f args => Syntax.Seq (Syntax.Label f_var f) (Syntax.Call x (Var f_var) args)
    end.

  Coercion to_stmt : StmtEx >-> Stmt.

  Fixpoint sp (stmt : StmtEx) (p : assert) : assert :=
    match stmt with
      | SeqEx a b => sp b (sp a p)
      | IfEx e t f => sp t (p /\ is_true e) \/ sp f (p /\ is_false e)
      | WhileEx inv e _ => inv /\ is_false e
      | AssertEx a => a
      | SkipEx => p
      | AssignEx x e =>
        (fun specs v0 v' =>
           exists v,
             p specs v0 v /\
             v' = (upd (fst v) x (eval (fst v) e), snd v))%type
      | DCallEx x f args =>
        (fun specs v0 v' =>
           exists v,
             p specs v0 v /\
             RunsToDCall specs x f args v v')%type
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
      | DCallEx x f args => (p --> (fun specs _ v => SafeDCall specs f args v)) :: nil
    end.

  Definition and_all : list entailment -> entailment := fold_right (fun a b specs => a specs /\ b specs)%type (fun _ => True).

  Lemma and_all_app : forall ls1 ls2 specs, and_all (ls1 ++ ls2) specs -> and_all ls1 specs /\ and_all ls2 specs.
    induction ls1; simpl; intuition.
    eapply IHls1 in H1; openhyp; eauto.
    eapply IHls1 in H1; openhyp; eauto.
  Qed.

  Lemma is_true_intro : forall e specs v v', wneb (eval (fst v') e) $0 = true -> (is_true e) specs v v'.
    intros.
    unfold is_true.
    unfold wneb in *.
    destruct (weq _ _) in *; intuition.
  Qed.

  Hint Resolve is_true_intro.

  Lemma is_false_intro : forall e specs v v', wneb (eval (fst v') e) $0 = false -> (is_false e) specs v v'.
    intros.
    unfold is_false.
    unfold wneb in *.
    destruct (weq _ _) in *; intuition.
  Qed.

  Hint Resolve is_false_intro.

  Hint Constructors Semantics.RunsTo.
  Hint Constructors Semantics.Safe.

  Ltac inject :=
    match goal with
      | H : _ = _ |- _ => unfold_all; injection H; intros; subst
    end.

  Definition Env := ((glabel -> option W) * (W -> option Callee))%type.

  Open Scope type.

  Definition specs_fs_agree (specs : Specs) (env : Env) :=
    let labels := fst env in
    let fs := snd env in
    forall p spec,
      fs p = Some spec <->
      exists (lbl : glabel),
        labels lbl = Some p /\
        find lbl specs = Some spec.

  Definition labels_in_scope (specs : Specs) (labels : glabel -> option W) :=
    forall lbl, In lbl specs -> labels lbl <> None.

  Definition specs_stn_injective (specs : Specs) stn := forall lbl1 lbl2 (w : W), In lbl1 specs -> In lbl2 specs -> stn lbl1 = Some w -> stn lbl2 = Some w -> lbl1 = lbl2.

  Definition specs_env_agree (specs : Specs) (env : Env) :=
    labels_in_scope specs (fst env) /\
    specs_stn_injective specs (fst env) /\
    specs_fs_agree specs env.

  Require Import Bedrock.Platform.Cito.GLabelMapFacts.
  Require Import Bedrock.Platform.Cito.Option.

  Require Import Bedrock.Platform.Cito.BedrockTactics.

  Lemma RunsTo_RunsToDCall :
    forall specs env r f args v v',
      specs_env_agree specs env ->
      RunsTo env (DCallEx r f args) v v' ->
      RunsToDCall specs r f args v v'.
  Proof.
    intros.
    simpl in *.
    unfold RunsToDCall.
    inv_clear H0.
    inv_clear H3.
    destruct (option_dec(find f specs)).
    destruct s; rewrite e; simpl in *.
    destruct x; simpl in *.
    destruct H; simpl in *.
    destruct env; simpl in *.
    rename a into f0.
    assert (o0 w = Some (Foreign f0)).
    eapply H0.
    descend; eauto.
    generalize H6; intro HH.
    inv_clear H6; simpl in *.
    sel_upd_simpl; rewrite H7 in H1; discriminate.
    sel_upd_simpl; rewrite H7 in H1; injection H1; intros; subst.
    eapply RunsTo_TransitTo in HH.
    Focus 2.
    simpl; sel_upd_simpl; eauto.
    openhyp.
    destruct r; simpl in *.
    subst; simpl in *.
    descend.
    eauto.
    sel_upd_simpl; eauto.
    descend.
    eauto.
    eauto.
    eauto.
    rewrite e; eauto.
  Qed.

  Lemma SafeDCall_Safe :
    forall specs env r f args v,
      specs_env_agree specs env ->
      SafeDCall specs f args v ->
      Safe env (DCallEx r f args) v.
  Proof.
    intros.
    destruct H.
    destruct env; simpl in *.
    unfold SafeDCall in *.
    destruct (option_dec(find f specs)).
    destruct s; rewrite e in *; simpl in *.
    destruct x.
    econstructor.
    econstructor.
    eapply H.
    eapply MapsTo_In; eapply find_mapsto_iff; eauto.
    intros.
    inv_clear H2.
    specialize (H0 w); clear H.
    destruct H0 as [inputs Htsf].
    eapply TransitSafe_Safe; eauto.
    sel_upd_simpl.
    eapply H1.
    descend; eauto.
    intuition.
    rewrite e in *; eauto.
    intuition.
  Qed.

  Lemma sound_runsto' : forall env (s : Stmt) v v', RunsTo env s v v' -> forall s' : StmtEx, s = s' -> forall specs, specs_env_agree specs env -> forall p, and_all (vc s' p) specs -> forall v0, p specs v0 v -> (sp s' p) specs v0 v'.
    induction 1; simpl; intros; destruct s'; try discriminate; simpl in *; try inject.

    (* skip *)
    eauto.

    openhyp.
    eauto.

    (* seq *)
    eapply_in_any and_all_app; openhyp.
    eauto.

    (* call *)
    openhyp.
    descend.
    eauto.
    eapply RunsTo_RunsToDCall; simpl; eauto.

    (* if *)
    eapply_in_any and_all_app; openhyp.
    left.
    eapply IHRunsTo; eauto.
    split; eauto.

    eapply_in_any and_all_app; openhyp.
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

    (* assign *)
    descend; eauto.
  Qed.

  Theorem sound_runsto : forall env (s : StmtEx) v v' specs p, RunsTo env s v v' -> specs_env_agree specs env -> and_all (vc s p) specs -> p specs v v -> (sp s p) specs v v'.
    intros.
    eapply sound_runsto'; eauto.
  Qed.

  Close Scope assert_scope.

  Theorem sound_safe : forall specs env (s : Stmt) (s' : StmtEx) v p v0, s = s' -> specs_env_agree specs env -> and_all (vc s' p) specs -> p specs v0 v -> Safe env s v.
    intros.
    eapply (Safe_coind (fun s v => Safe env s v \/ exists (s' : StmtEx) p v0, s = s' /\ and_all (vc s' p) specs /\ p specs v0 v)); [ .. | right; descend; eauto]; generalize H0; clear; intros; openhyp.

    (* seq *)
    inversion H; subst.
    descend; left; eauto.

    destruct x; try discriminate; simpl in *; try inject.
    eapply_in_any and_all_app; openhyp.
    descend.
    right; descend; eauto.
    intros.
    eapply sound_runsto' with (p := x0) in H4; eauto.
    right; descend; eauto.

    (* dcall *)

    openhyp.
    eapply H1 in H2.
    eapply SafeDCall_Safe in H2; eauto.
    simpl in *.
    inv_clear H2.
    split.
    eauto.
    intros.
    eauto.

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
    eapply_in_any and_all_app; openhyp.
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
    eapply sound_runsto' with (p := and_lift a (is_true e)) in H5; eauto.
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

    (* label *)
    inversion H; unfold_all; subst.
    eauto.

    destruct x0; try discriminate; simpl in *; try inject.
  Qed.

End ADTValue.
