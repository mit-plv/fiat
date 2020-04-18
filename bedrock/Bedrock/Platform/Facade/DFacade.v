(* DFacade : Direct Facade *)

Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.Facade.
Export Facade.

Require Import Coq.Strings.String.
Require Import Bedrock.Platform.Cito.StringMap.

Require Import Coq.Lists.List.
Require Import Bedrock.Platform.Cito.ListFacts3 Bedrock.Platform.Cito.ListFacts4.
Import ListNotations.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.
Import FSetNotations.
Local Open Scope fset_scope.

Require Import Bedrock.Platform.Cito.GLabel.
Require Import Bedrock.Memory.
Require Import Bedrock.Platform.Cito.SyntaxExpr.

(* Syntax *)

Inductive Stmt :=
| Skip
| Seq : Stmt -> Stmt -> Stmt
| If : Expr -> Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt
| Call : string -> glabel -> list string -> Stmt
| Assign : string -> Expr -> Stmt.

(* syntactical checks *)

(* List of variables that are assigned to, i.e. appear as LHS *)
Fixpoint assigned s :=
  match s with
    | Skip => empty
    | Seq a b => assigned a + assigned b
    | If _ t f => assigned t + assigned f
    | While _ c => assigned c
    | Assign x _ => singleton x
    | Call x _ _ => singleton x
  end.

Local Open Scope bool_scope.

Fixpoint is_actual_args_no_dup s :=
  match s with
    | Call _ _ args => is_no_dup args
    | Skip => true
    | Seq a b => is_actual_args_no_dup a && is_actual_args_no_dup b
    | If _ a b => is_actual_args_no_dup a && is_actual_args_no_dup b
    | While _ body => is_actual_args_no_dup body
    | Assign _ _ => true
  end.

Require Import Bedrock.Platform.Cito.FreeVarsExpr.

Local Notation e_free_vars := FreeVarsExpr.free_vars.

Fixpoint free_vars (s : Stmt) :=
  match s with
    | Skip => empty
    | Seq a b => free_vars a + free_vars b
    | If e t f => e_free_vars e + free_vars t + free_vars f
    | While e body => e_free_vars e + free_vars body
    | Assign x e => singleton x + e_free_vars e
    | Call x _ args => singleton x + StringSetFacts.of_list args
  end.

Require Import Bedrock.Platform.Facade.NameDecoration.

Definition is_good_varnames s := for_all is_good_varname (free_vars s).

Definition is_syntax_ok s := is_actual_args_no_dup s && is_good_varnames s.

(* Argument variables are not allowed to be assigned to, which needed for compilation into Cito.
   The return variable must not be an argument, to prevent aliasing.
   Boolean predicates are used here so that OperationalSpec is proof-irrelavant, and proofs can simply be eq_refl. *)
Record OperationalSpec :=
  {
    ArgVars : list string;
    RetVar : string;
    Body : Stmt;
    args_no_dup : is_no_dup ArgVars = true;
    ret_not_in_args : negb (is_in RetVar ArgVars) = true;
    no_assign_to_args : is_disjoint (assigned Body) (of_list ArgVars) = true;
    args_name_ok : forallb is_good_varname ArgVars = true;
    ret_name_ok : is_good_varname RetVar = true;
    syntax_ok : is_syntax_ok Body = true
  }.

Import StringMap.
Require Import Bedrock.Platform.Cito.StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.

Require Import Bedrock.Platform.Cito.GLabelMap.

Section ADTSection.

  (* Semantics *)

  Variable ADTValue : Type.

  Notation Value := (@Value ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Notation State := (@State ADTValue).

  Inductive FuncSpec :=
    | Axiomatic : AxiomaticSpec -> FuncSpec
    | Operational : OperationalSpec -> FuncSpec.

  Definition Env := GLabelMap.t FuncSpec.

  Section EnvSection.

    Variable env : Env.

    Inductive RunsTo : Stmt -> State -> State -> Prop :=
    | RunsToSkip :
        forall st st',
          st' == st ->
          RunsTo Skip st st'
    | RunsToSeq :
        forall a b st st' st'',
          RunsTo a st st' ->
          RunsTo b st' st'' ->
          RunsTo (Seq a b) st st''
    | RunsToIfTrue :
        forall cond t f st st',
          is_true st cond ->
          RunsTo t st st' ->
          RunsTo (If cond t f) st st'
    | RunsToIfFalse :
        forall cond t f st st',
          is_false st cond ->
           RunsTo f st st' ->
          RunsTo (If cond t f) st st'
    | RunsToWhileTrue :
        forall cond body st st' st'',
          let loop := While cond body in
          is_true st cond ->
          RunsTo body st st' ->
          RunsTo loop st' st'' ->
          RunsTo loop st st''
    | RunsToWhileFalse :
        forall cond body st st',
          let loop := While cond body in
          is_false st cond ->
          st' == st ->
          RunsTo loop st st'
    | RunsToAssign :
        forall x e st st' w,
          (* rhs can't be an ADT object, to prevent aliasing *)
          eval st e = Some (SCA w) ->
          (* lhs can't be already referring to an ADT object, to prevent memory leak *)
          not_mapsto_adt x st = true ->
          st' == add x (SCA w) st ->
          RunsTo (Assign x e) st st'
    | RunsToCallAx :
        forall x f args st spec input output ret,
          GLabelMap.find f env = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          not_mapsto_adt x st = true ->
          PreCond spec input ->
          length input = length output ->
          PostCond spec (combine input output) ret ->
          let st' := add_remove_many args input (wrap_output output) st in
          let st' := add x ret st' in
          forall st'',
            st'' == st' ->
            RunsTo (Call x f args) st st''
    | RunsToCallOp :
        forall x f args st spec input callee_st' ret,
          GLabelMap.find f env = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          mapM (sel st) args = Some input ->
          not_mapsto_adt x st = true ->
          let callee_st := make_map (ArgVars spec) input in
          RunsTo (Body spec) callee_st callee_st' ->
          sel callee_st' (RetVar spec) = Some ret ->
          (* prevent memory leak *)
          no_adt_leak input (ArgVars spec) (RetVar spec) callee_st' ->
          let output := List.map (sel callee_st') (ArgVars spec) in
          let st' := add_remove_many args input output st in
          let st' := add x ret st' in
          forall st'',
            st'' == st' ->
            RunsTo (Call x f args) st st''.

    CoInductive Safe : Stmt -> State -> Prop :=
    | SafeSkip : forall st, Safe Skip st
    | SafeSeq :
        forall a b st,
          Safe a st /\
          (forall st',
             RunsTo a st st' -> Safe b st') ->
          Safe (Seq a b) st
    | SafeIfTrue :
        forall cond t f st,
          is_true st cond ->
          Safe t st ->
          Safe (If cond t f) st
    | SafeIfFalse :
        forall cond t f st,
          is_false st cond ->
          Safe f st ->
          Safe (If cond t f) st
    | SafeWhileTrue :
        forall cond body st,
          let loop := While cond body in
          is_true st cond ->
          Safe body st ->
          (forall st',
             RunsTo body st st' -> Safe loop st') ->
          Safe loop st
    | SafeWhileFalse :
        forall cond body st,
          let loop := While cond body in
          is_false st cond ->
          Safe loop st
    | SafeAssign :
        forall x e st w,
          eval st e = Some (SCA w) ->
          not_mapsto_adt x st = true ->
          Safe (Assign x e) st
    | SafeCallAx :
        forall x f args st spec input,
          GLabelMap.find f env = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          not_mapsto_adt x st = true ->
          PreCond spec input ->
          Safe (Call x f args) st
    | SafeCallOp :
        forall x f args st spec input,
          GLabelMap.find f env = Some (Operational spec) ->
          length args = length (ArgVars spec) ->
          mapM (sel st) args = Some input ->
          not_mapsto_adt x st = true ->
          let callee_st := make_map (ArgVars spec) input in
          Safe (Body spec) callee_st ->
          (* all paths of callee must be memory-leak free and produce a return value *)
          (forall callee_st',
             RunsTo (Body spec) callee_st callee_st' ->
             sel callee_st' (RetVar spec) <> None /\
             no_adt_leak input (ArgVars spec) (RetVar spec) callee_st') ->
          Safe (Call x f args) st.

    Section Safe_coind.

      Variable R : Stmt -> State -> Prop.

      Hypothesis SeqCase : forall a b st, R (Seq a b) st -> R a st /\ forall st', RunsTo a st st' -> R b st'.

      Hypothesis IfCase : forall cond t f st, R (If cond t f) st -> (is_true st cond /\ R t st) \/ (is_false st cond /\ R f st).

      Hypothesis WhileCase :
        forall cond body st,
          let loop := While cond body in
          R loop st ->
          (is_true st cond /\ R body st /\ (forall st', RunsTo body st st' -> R loop st')) \/
          (is_false st cond).

      Hypothesis AssignCase :
        forall x e st,
          R (Assign x e) st ->
          not_mapsto_adt x st = true /\
          exists w, eval st e = Some (SCA w).

      Hypothesis CallCase :
        forall x f args st,
          R (Call x f args) st ->
          not_mapsto_adt x st = true /\
          exists input,
            mapM (sel st) args = Some input /\
            ((exists spec,
                GLabelMap.find f env = Some (Axiomatic spec) /\
                PreCond spec input) \/
             (exists spec,
                GLabelMap.find f env = Some (Operational spec) /\
                length args = length (ArgVars spec) /\
                let callee_st := make_map (ArgVars spec) input in
                R (Body spec) callee_st /\
                (forall callee_st',
                   RunsTo (Body spec) callee_st callee_st' ->
                   sel callee_st' (RetVar spec) <> None /\
                   no_adt_leak input (ArgVars spec) (RetVar spec) callee_st'))).

      Hint Constructors Safe.

      Require Import Bedrock.Platform.Cito.GeneralTactics.

      Theorem Safe_coind : forall c st, R c st -> Safe c st.
        cofix; intros; destruct c.
        - eauto.
        - eapply SeqCase in H; openhyp; eapply SafeSeq; eauto.
        - eapply IfCase in H; openhyp; eauto.
        - eapply WhileCase in H; openhyp; eauto.
        - eapply CallCase in H; openhyp; simpl in *; intuition eauto.
        - eapply AssignCase in H; openhyp; eauto.
      Qed.

    End Safe_coind.

  End EnvSection.

End ADTSection.
