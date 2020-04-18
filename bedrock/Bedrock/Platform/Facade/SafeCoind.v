Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.Facade.

Require Import Bedrock.Platform.Cito.StringMapFacts.
Require Import Coq.Lists.List.
Require Import Bedrock.Platform.Cito.ListFacts4.

Section ADTValue.

  Variable ADTValue : Type.

  Notation RunsTo := (@RunsTo ADTValue).
  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation Sca := (@SCA ADTValue).

  Section Safe_coind.

    Variable env : Env.

    Variable R : Stmt -> State -> Prop.

    Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', RunsTo env a st st' -> R b st'.

    Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true st cond /\ R t st) \/ (is_false st cond /\ R f st).

    Hypothesis WhileCase :
      forall cond body st,
        let loop := While cond body in
        R loop st ->
        (is_true st cond /\ R body st /\ (forall st', RunsTo env body st st' -> R loop st')) \/
        (is_false st cond).

    Hypothesis AssignCase :
      forall x e st,
        R (Facade.Assign x e) st ->
        not_mapsto_adt x st = true /\
        exists w, eval st e = Some (Sca w).

    Hypothesis LabelCase :
      forall x lbl st,
        R (Label x lbl) st ->
        not_mapsto_adt x st = true /\
        exists w, Label2Word env lbl = Some w.

    Hypothesis CallCase :
      forall x f args st,
        R (Call x f args) st ->
        NoDup args /\
        not_mapsto_adt x st = true /\
        exists f_w input,
          eval st f = Some (Sca f_w) /\
          mapM (sel st) args = Some input /\
          ((exists spec,
              Word2Spec env f_w = Some (Axiomatic spec) /\
              PreCond spec input) \/
           (exists spec,
              Word2Spec env f_w = Some (Operational _ spec) /\
              length args = length (ArgVars spec) /\
              let callee_st := make_map (ArgVars spec) input in
              R (Body spec) callee_st /\
              (forall callee_st',
                 RunsTo env (Body spec) callee_st callee_st' ->
                 sel callee_st' (RetVar spec) <> None /\
                 no_adt_leak input (ArgVars spec) (RetVar spec) callee_st'))).

    Hint Constructors Safe.

    Require Import Bedrock.Platform.Cito.GeneralTactics.

    Theorem Safe_coind : forall c st, R c st -> Safe env c st.
      cofix; intros; destruct c.
      - eauto.
      - eapply SeqCase in H; openhyp; eapply SafeSeq; eauto.
      - eapply IfCase in H; openhyp; eauto.
      - eapply WhileCase in H; openhyp; eauto.
      - eapply CallCase in H; openhyp; simpl in *; intuition eauto.
      - eapply LabelCase in H; openhyp; eauto.
      - eapply AssignCase in H; openhyp; eauto.
    Qed.

  End Safe_coind.

End ADTValue.
