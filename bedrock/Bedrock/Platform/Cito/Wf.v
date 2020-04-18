(* This file gives a syntactic condition for semantic good behavior of a function body,
 * with respect to not reading uninitialized variables. *)

Set Implicit Arguments.

Require Import Coq.Bool.Bool.
Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Cito.SyntaxExpr Bedrock.Platform.Cito.SemanticsExpr Bedrock.Platform.Cito.Syntax Bedrock.Platform.Cito.Semantics.

Fixpoint expReads (unwritten : string -> Prop) (e : Expr) (x : string) : Prop :=
  match e with
    | Var y => x = y /\ unwritten x
    | Const _ => False
    | Binop _ e1 e2 => expReads unwritten e1 x \/ expReads unwritten e2 x
    | TestE _ e1 e2 => expReads unwritten e1 x \/ expReads unwritten e2 x
  end.

Import Syntax.

Fixpoint writes (s : Stmt) (x : string) : Prop :=
  match s with
    | Assign y _ => x = y
    | Label y _ => x = y
    | Seq s1 s2 => writes s1 x \/ writes s2 x
    | Skip => False
    | Syntax.If _ s1 s2 => writes s1 x /\ writes s2 x
    | Syntax.While _ _ => False
    | Syntax.Call yo _ _ => match yo with
                              | None => False
                              | Some y => x = y
                            end
  end.

Section ExistsR.
  Variable A : Type.
  Variable P : A -> Prop.

  Fixpoint ExistsR (ls : list A) : Prop :=
    match ls with
      | nil => False
      | x :: ls => P x \/ ExistsR ls
    end.

  Theorem ExistsR_Exists : forall ls, ExistsR ls -> List.Exists P ls.
    induction ls; simpl; intuition.
  Qed.

  Theorem Exists_ExistsR : forall ls, List.Exists P ls -> ExistsR ls.
    induction 1; simpl; intuition.
  Qed.
End ExistsR.

Section ExistsR_weaken.
  Variable A : Type.
  Variables P Q : A -> Prop.

  Hypothesis P_Q : forall x, P x -> Q x.

  Theorem ExistsR_weaken : forall ls, ExistsR P ls -> ExistsR Q ls.
    induction ls; simpl; intuition.
  Qed.
End ExistsR_weaken.

Fixpoint reads (unwritten : string -> Prop) (s : Stmt) (x : string) : Prop :=
  match s with
    | Assign _ e => expReads unwritten e x
    | Label _ _ => False
    | Seq s1 s2 => reads unwritten s1 x \/ reads (fun x => unwritten x /\ ~writes s1 x) s2 x
    | Skip => False
    | Syntax.If e s1 s2 => expReads unwritten e x \/ reads unwritten s1 x \/ reads unwritten s2 x
    | Syntax.While e s1 => expReads unwritten e x \/ reads unwritten s1 x
    | Syntax.Call _ e1 es => expReads unwritten e1 x \/ ExistsR (fun e => expReads unwritten e x) es
  end.

Lemma eval_irrel : forall unwritten vs vs' e,
  (forall x, ~expReads unwritten e x)
  -> (forall x, sel vs' x <> sel vs x -> unwritten x)
  -> eval vs e = eval vs' e.
  induction e; simpl; intuition.
  change (sel vs s = sel vs' s).
  specialize (H0 s).
  destruct (weq (sel vs' s) (sel vs s)).
  eauto.
  exfalso; eapply H.
  descend.
  eauto.
  eauto.
  f_equal; eauto.
  rewrite IHe1 by eauto.
  rewrite IHe2 by eauto.
  auto.
Qed.

Local Hint Constructors RunsTo.

Ltac irr E vs vs' :=
  replace (eval vs E) with (eval vs' E) in *
    by (eapply eval_irrel; (cbv beta; eauto)).

Ltac irrel := simpl in *;
  match goal with
    | [ _ : context[eval ?vs' ?E] |- context[eval ?vs ?E ] ] =>
      match vs with
        | vs' => fail 1
        | _ => irr E vs vs'
      end
  end.

Lemma expReads_weaken : forall x (unwritten1 unwritten2 : _ -> Prop),
  (forall y, unwritten1 y -> unwritten2 y)
  -> forall e, expReads unwritten1 e x
    -> expReads unwritten2 e x.
  induction e; simpl; intuition.
Qed.

Ltac user' :=
  try (eapply ExistsR_weaken; [ | eauto ]; cbv beta; intros);
    match goal with
      | _ => eapply expReads_weaken
      | [ H : _ |- _ ] => eapply H
    end; [ | solve [ eauto ] ]; cbv beta; solve [ intuition ].

Ltac user := user' || (left; user) || (right; user).

Lemma reads_weaken : forall x s (unwritten1 unwritten2 : _ -> Prop),
  (forall y, unwritten1 y -> unwritten2 y)
  -> reads unwritten1 s x
  -> reads unwritten2 s x.
  induction s; simpl; intuition eauto; user.
Qed.

Ltac use E := eapply E; [ | eauto ]; cbv beta; tauto.

Section ADTValue.
  Variable ADTValue : Type.

  Lemma expReads_trivial : forall x e unwritten,
    (forall x, ~unwritten x)
    -> expReads unwritten e x
    -> False.
    induction e; simpl; intuition eauto.
  Qed.

  Hint Resolve expReads_trivial.

  Lemma reads_trivial' : forall x s unwritten,
    (forall x, ~unwritten x)
    -> ~reads unwritten s x.
    induction s; simpl; intuition; eauto.
    eapply IHs2.
    2: eauto.
    simpl; intuition eauto.
    induction l; simpl in *; intuition eauto.
  Qed.

  Lemma reads_trivial : forall x s,
    ~reads (fun _ => False) s x.
    intros; apply reads_trivial'; auto.
  Qed.

  Lemma map_eval_irrel : forall unwritten vs vs' es,
    (forall x, ~ExistsR (fun e => expReads unwritten e x) es)
    -> (forall x, sel vs' x <> sel vs x -> unwritten x)
    -> map (eval vs) es = map (eval vs') es.
    induction es; simpl; intuition.
    f_equal.
    eapply eval_irrel; eauto.
    eauto.
  Qed.

  Lemma prove_NoUninitializedRunsTo' : forall fs s st st', RunsTo (ADTValue := ADTValue) fs s st st'
  -> forall unwritten vs'', (forall x, ~reads unwritten s x)
    -> (forall x, sel vs'' x <> sel (fst st) x -> unwritten x)
    -> exists vs''', RunsTo fs s (vs'', snd st) (vs''', snd st')
      /\ (forall x, sel vs''' x <> sel (fst st') x -> unwritten x /\ ~writes s x).
    induction 1; simpl; intuition;
      repeat match goal with
               | [ x := _ |- _ ] => subst x
             end; eauto.

    edestruct (IHRunsTo1 unwritten); clear IHRunsTo1; eauto; intuition idtac.
    edestruct (IHRunsTo2 (fun x => unwritten x /\ ~writes a x)); eauto; intuition idtac.
    eexists; split.
    eauto.
    firstorder.

    edestruct IHRunsTo; eauto; intuition idtac.
    eexists; split.
    econstructor; repeat irrel; eauto.
    firstorder.

    edestruct IHRunsTo; eauto; intuition idtac.
    eexists; split.
    eapply RunsToIfFalse; repeat irrel; eauto.
    firstorder.

    edestruct IHRunsTo1; clear IHRunsTo1; eauto; intuition idtac.
    edestruct (IHRunsTo2 (fun x => unwritten x /\ ~writes body x)); clear IHRunsTo2; eauto; intuition idtac.
    simpl in *; intuition.
    eapply H2; left.
    use expReads_weaken.
    eapply H2; right.
    use reads_weaken.
    eexists; split.
    eapply RunsToWhileTrue.
    simpl.
    irrel; auto.
    eauto.
    eauto.
    firstorder.

    eexists; split.
    eapply RunsToWhileFalse.
    simpl.
    irrel; auto.
    intuition.

    edestruct IHRunsTo.
    Focus 3.
    intuition idtac.
    eexists; split.
    econstructor.
    simpl; irrel; eauto.
    simpl.
    erewrite <- map_eval_irrel; eauto.
    eauto.
    simpl.
    intros.
    destruct var; simpl in *.
    2: eauto.
    destruct (string_dec s x0); subst.
    Focus 2.
    repeat rewrite sel_upd_ne in H4 by auto.
    eauto.
    repeat rewrite sel_upd_eq in H4 by reflexivity.
    apply H6 in H4.
    generalize dependent H4.
    instantiate (1 := fun _ => False); simpl in *.
    intuition.
    2: tauto.
    intro; apply reads_trivial.

    eexists; split.
    change (heap_upd_option
      (fold_left (store_out (ADTValue:=ADTValue)) triples (snd v))
      (fst (decide_ret addr ret)) (snd (decide_ret addr ret)))
    with (heap_upd_option (fold_left (@store_out _) triples (snd (vs'', snd v)))
      (fst (decide_ret addr ret)) (snd (decide_ret addr ret))).
    eapply RunsToCallForeign; simpl.
    simpl; irrel; eauto.
    simpl; erewrite <- map_eval_irrel; eauto.
    eauto.
    simpl.
    auto.
    eauto.
    eauto.
    eauto.
    intros.
    destruct var; simpl in *.
    2: eauto.
    destruct (string_dec s x); subst.
    Focus 2.
    repeat rewrite sel_upd_ne in H8 by auto.
    eauto.
    repeat rewrite sel_upd_eq in H8 by reflexivity.
    tauto.

    eexists; split.
    change (snd v) with (snd (vs'', snd v)) at 2.
    eauto.
    simpl; intros.
    destruct (string_dec x0 x); subst.
    repeat rewrite sel_upd_eq in H0 by reflexivity; tauto.
    repeat rewrite sel_upd_ne in H0 by auto.
    eauto.

    eexists; split.
    change (snd v) with (snd (vs'', snd v)) at 2.
    econstructor.
    simpl; intros.
    destruct (string_dec x0 x); subst.
    repeat rewrite sel_upd_eq in H1 by reflexivity.
    exfalso; apply H1.
    irrel; auto.
    repeat rewrite sel_upd_ne in H1 by auto.
    eauto.
  Qed.

  Theorem prove_NoUninitializedRunsTo : forall arg_vars rvar s,
    (forall x, ~reads (fun s => ~In s arg_vars) s x)
    -> writes s rvar
    -> forall fs vs a vs' a', RunsTo (ADTValue := ADTValue) fs s (vs, a) (vs', a')
      -> forall vs'', agree_on vs vs'' arg_vars
        -> exists vs''', RunsTo fs s (vs'', a) (vs''', a') /\ sel vs''' rvar = sel vs' rvar.
    intros.
    eapply prove_NoUninitializedRunsTo' in H1; eauto.
    Focus 2.
    instantiate (1 := vs''); simpl in *.
    unfold not; intros.
    eapply Forall_forall in H2; eauto.
    post.
    descend.
    eauto.
    destruct (weq (sel x rvar) (sel vs' rvar)); auto.
    apply H4 in n; tauto.
  Qed.

  Local Hint Constructors Safe.

  Ltac dont_go_crazy H := (inversion H; []) || (inversion H; [ | ]).

  Ltac hammer :=
    repeat match goal with
             | [ H : Logic.ex _ |- _ ] => destruct H; intuition idtac
           end; simpl in *;
    match goal with
      | [ H : Safe _ _ _ |- _ ] => dont_go_crazy H; clear H;
        repeat match goal with
                 | [ x : _ |- _ ] => subst x
                 end; simpl in *; cbv beta; intuition idtac
      end.

  Lemma prove_NoUninitializedSafe' : forall s unwritten,
    (forall x, ~reads unwritten s x)
    -> forall fs vs a, Safe (ADTValue := ADTValue) fs s (vs, a)
      -> forall vs', (forall x, sel vs' x <> sel vs x -> unwritten x)
        -> Safe fs s (vs', a).
    intros; apply (@Safe_coind _ fs (fun s st =>
      exists unwritten,
        (forall x, ~reads unwritten s x)
        /\ exists vs, Safe fs s (vs, snd st)
          /\ (forall x, sel (fst st) x <> sel vs x -> unwritten x)));
    intuition idtac.

    hammer.
    eauto 10.

    hammer.
    eapply prove_NoUninitializedRunsTo' in H3; eauto.
    destruct H3; intuition idtac.
    repeat esplit; eauto.
    intros.
    apply (H5 _ (not_eq_sym H2)).
    eauto.

    hammer.
    left; repeat irrel; eauto 10.
    right; repeat irrel; eauto 10.

    intros.
    hammer.
    irrel.
    left; intuition idtac.
    eauto 10.
    eapply prove_NoUninitializedRunsTo' in H2; eauto.
    destruct H2; intuition idtac.
    apply H10 in H4.
    do 2 esplit.
    Focus 2.
    do 2 esplit.
    eauto.
    intros; apply H6.
    eauto.
    intuition idtac.
    eapply H3; left.
    use expReads_weaken.
    eapply H3; right.
    use reads_weaken.
    eauto.

    irrel; tauto.

    hammer.
    repeat irrel.
    left.
    do 2 esplit.
    eauto.
    esplit; eauto.
    intros.
    do 2 esplit.
    Focus 2.
    do 2 esplit.
    erewrite <- map_eval_irrel in H2.
    eauto.
    eauto.
    eauto.
    tauto.
    instantiate (1 := fun _ => False).
    intro; apply reads_trivial.

    repeat irrel.
    right.
    do 2 esplit.
    split.
    eauto.
    split.
    erewrite <- map_eval_irrel; eauto.
    eauto.

    hammer.

    eauto 10.
  Qed.

  Theorem prove_NoUninitializedSafe : forall arg_vars s,
    (forall x, ~reads (fun s => ~In s arg_vars) s x)
    -> forall fs vs a, Safe (ADTValue := ADTValue) fs s (vs, a)
      -> forall vs', agree_on vs vs' arg_vars
        -> Safe fs s (vs', a).
    intros.
    eapply prove_NoUninitializedSafe' in H0; eauto.
    simpl; intros.
    intro.
    eapply Forall_forall in H1; eauto.
  Qed.

End ADTValue.

Section TopSection.

  Require Import Bedrock.Platform.Cito.Syntax.
  Require Import Bedrock.sep.Locals.
  Require Import Coq.Strings.String.

  Definition NoUninitialized (arg_vars : list string) (rvar : string) (s : Stmt) :=
    (forall x, ~reads (fun s => ~In s arg_vars) s x) /\ writes s rvar.

  Definition agree_in vs vs' vars := List.Forall (fun x => sel vs x = sel vs' x) vars.

  Lemma agree_in_merge : forall vs vs' vars, agree_in vs (merge vs vs' vars) vars.
    intros.
    generalize (merge_agree vs vs' vars).
    unfold agree_on, agree_in.
    apply Forall_weaken; auto.
  Qed.

  Lemma agree_in_comm : forall vs vs' vars, agree_in vs vs' vars -> agree_in vs' vs vars.
    do 3 intro; apply Forall_weaken; auto.
  Qed.

End TopSection.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Section TopSection.

    Lemma NoUninitialized_Safe : forall arg_vars rvar s, NoUninitialized arg_vars rvar s -> forall fs vs h, Safe fs s (vs, h) -> forall vs', agree_in vs vs' arg_vars -> Safe fs s (vs', h).
      intros.
      eapply prove_NoUninitializedSafe in H0; eauto.
      destruct H; auto.
    Qed.

    Lemma NoUninitialized_RunsTo : forall arg_vars rvar s, NoUninitialized arg_vars rvar s -> forall fs vs h v', RunsTo fs s (vs, h) v' -> forall vs', agree_in vs vs' arg_vars ->
      exists vs'', RunsTo fs s (vs', h) (vs'', snd v') /\ sel vs'' rvar = sel (fst v') rvar.
      intros.
      destruct v'; simpl.
      destruct H.
      eapply prove_NoUninitializedRunsTo in H0; eauto.
    Qed.

  End TopSection.

End Make.
