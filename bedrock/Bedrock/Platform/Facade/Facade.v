(* Facade : a heap-free, aliasing-free and memory-leak-free imperative language *)

Set Implicit Arguments.

Require Import Coq.Strings.String.

Require Import Bedrock.Platform.Cito.StringMap.
Import StringMap.
Require Import Bedrock.Platform.Cito.AxSpec.
Export AxSpec.

Section ADTSection.

  (* Syntax *)

  Require Import Bedrock.Memory Bedrock.IL.
  Require Import Bedrock.Platform.Cito.SyntaxExpr.
  Require Import Bedrock.Platform.Cito.GLabel.

  Inductive Stmt :=
  | Skip
  | Seq : Stmt -> Stmt -> Stmt
  | If : Expr -> Stmt -> Stmt -> Stmt
  | While : Expr -> Stmt -> Stmt
  | Call : string -> Expr -> list string -> Stmt
  | Label : string -> glabel -> Stmt
  | Assign : string -> Expr -> Stmt.

  (* Semantics *)

  Variable ADTValue : Type.

  Notation Value := (@Value ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Arguments SCA {ADTValue} _.
  Arguments ADT {ADTValue} _.

  Definition State := StringMap.t Value.

  Definition eval_binop (op : binop + test) a b :=
    match op with
      | inl op' => evalBinop op' a b
      | inr op' => if evalTest op' a b then $1 else $0
    end.

  Definition eval_binop_m (op : binop + test) (oa ob : option Value) : option Value :=
    match oa, ob with
      | Some (SCA a), Some (SCA b) => Some (SCA (eval_binop op a b))
      | _, _ => None
    end.

  Fixpoint eval (st : State) (e : Expr) : option Value :=
    match e with
      | Var x => find x st
      | Const w => Some (SCA w)
      | Binop op a b => eval_binop_m (inl op) (eval st a) (eval st b)
      | TestE op a b => eval_binop_m (inr op) (eval st a) (eval st b)
    end.

  Definition eval_bool st e : option bool :=
    match eval st e with
      | Some (SCA w) => Some (wneb w $0)
      | _ => None
    end.

  Definition is_true st e := eval_bool st e = Some true.
  Definition is_false st e := eval_bool st e = Some false.

  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Import FMapNotations.
  Open Scope fmap_scope.

  Require Import Coq.Lists.List.

  Fixpoint add_remove_many keys (input : list Value) (output : list (option Value)) st :=
    match keys, input, output with
      | k :: keys', i :: input', o :: output' =>
        let st' :=
            match i, o with
              | ADT _, Some v => add k v st
              | ADT _, None => StringMap.remove k st
              | _, _ => st
            end in
        add_remove_many keys' input' output' st'
      | _, _, _ => st
    end.

  Require Import Bedrock.Platform.Cito.ListFacts3 Bedrock.Platform.Cito.ListFacts4.

  Definition is_in (a : string) ls := if in_dec string_dec a ls then true else false.

  Require Import Bedrock.StringSet Bedrock.Platform.Cito.StringSetFacts.
  Import StringSet FSetNotations.
  Open Scope fset_scope.

  (* List of variables that are assigned to, i.e. appear as LHS *)
  Fixpoint assigned s :=
    match s with
      | Skip => empty
      | Seq a b => assigned a + assigned b
      | If _ t f => assigned t + assigned f
      | While _ c => assigned c
      | Assign x e => singleton x
      | Label x l => singleton x
      | Call x f es => singleton x
    end.

  Definition is_disjoint a b := StringSet.is_empty (StringSet.inter a b).

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
      no_assign_to_args : is_disjoint (assigned Body) (of_list ArgVars) = true
    }.

  Inductive FuncSpec :=
    | Axiomatic : AxiomaticSpec -> FuncSpec
    | Operational : OperationalSpec -> FuncSpec.

  Definition sel st x := @StringMap.find Value x st.

  Record Env :=
    {
      Label2Word : glabel -> option W ;
      Word2Spec : W ->option FuncSpec
    }.

  Definition no_adt_leak input argvars retvar st :=
    forall var (a : ADTValue),
      sel st var = Some (ADT a) ->
      var = retvar \/
      exists i (ai : ADTValue), nth_error argvars i = Some var /\
                   nth_error input i = Some (ADT ai).

  Definition wrap_output := List.map (option_map (@ADT ADTValue)).

  Definition is_some_p A (p : A -> bool) o :=
    match o with
      | Some a => p a
      | None => false
    end.

  Definition is_mapsto_adt x st := is_some_p (@is_adt ADTValue) (StringMap.find x st).
  Definition not_mapsto_adt x st := negb (is_mapsto_adt x st).

  Import StringMap.
  Open Scope fmap_scope.

  Section EnvSection.

    Variable env : Env.

    Inductive RunsTo : Stmt -> State -> State -> Prop :=
    | RunsToSkip : forall st, RunsTo Skip st st
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
        forall cond body st,
          let loop := While cond body in
          is_false st cond ->
          RunsTo loop st st
    | RunsToAssign :
        forall x e st st' w,
          (* rhs can't be an ADT object, to prevent aliasing *)
          eval st e = Some (SCA w) ->
          (* lhs can't be already referring to an ADT object, to prevent memory leak *)
          not_mapsto_adt x st = true ->
          st' == add x (SCA w) st ->
          RunsTo (Assign x e) st st'
    | RunsToLabel :
        forall x lbl st st' w,
          Label2Word env lbl = Some w ->
          not_mapsto_adt x st = true ->
          st' == add x (SCA w) st ->
          RunsTo (Label x lbl) st st'
    | RunsToCallAx :
        forall x f args st spec input output ret f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Axiomatic spec) ->
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
        forall x f args st spec input callee_st' ret f_w,
          (* the same actual parameter cannot be supplied twice, to prevent aliasing in the callee *)
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Operational spec) ->
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
    | SafeLabel :
        forall x lbl st w,
          Label2Word env lbl = Some w ->
          not_mapsto_adt x st = true ->
          Safe (Label x lbl) st
    | SafeCallAx :
        forall x f args st spec input f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Axiomatic spec) ->
          mapM (sel st) args = Some input ->
          not_mapsto_adt x st = true ->
          PreCond spec input ->
          Safe (Call x f args) st
    | SafeCallOp :
        forall x f args st spec input f_w,
          NoDup args ->
          eval st f = Some (SCA f_w) ->
          Word2Spec env f_w = Some (Operational spec) ->
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

  End EnvSection.

End ADTSection.
