Require Import Bedrock.Platform.Cito.FreeVarsExpr.
Require Import Bedrock.Platform.Cito.Syntax.
Require Import Bedrock.StringSet.
Require Import Bedrock.Platform.Cito.Option.
Require Import Bedrock.Platform.Cito.Union.
Import StringSet.

Set Implicit Arguments.

Local Notation e_free_vars := FreeVarsExpr.free_vars.

Fixpoint free_vars (s : Syntax.Stmt) :=
  match s with
    | Syntax.Skip => empty
    | Syntax.Seq a b => union (free_vars a) (free_vars b)
    | Syntax.If cond t f => union (union (e_free_vars cond) (free_vars t)) (free_vars f)
    | Syntax.While cond body => union (e_free_vars cond) (free_vars body)
    | Syntax.Call var f args =>
      union
        (union
           (default empty (option_map singleton var))
           (e_free_vars f))
        (union_list (List.map e_free_vars args))
    | Syntax.Label x lbl => singleton x
    | Syntax.Assign x e => union (singleton x) (e_free_vars e)
  end.
