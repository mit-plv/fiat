Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Syntax.

Require Import Bedrock.Platform.Cito.FreeVarsExpr.

Require Import Bedrock.Platform.Cito.Option.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.
Import FSetNotations.
Import FSetNotationsTrial.
Local Open Scope fset_scope.

Coercion string2elt (x : string) : elt := x.
Coercion singleton : elt >-> t.

Fixpoint inits stmt : StringSet.t :=
  match stmt with
    | Assign x _ => x
    | Label x _ => x
    | Seq a b => inits a + inits b
    | Skip => []
    | Syntax.If _ t f => inits t * inits f
    | While _ _ => []
    | Syntax.Call x _ _ => default empty (option_map singleton x)
  end.

Fixpoint uninited_reads inited stmt :=
  match stmt with
    | Assign _ e => free_vars e - inited
    | Label _ _ => []
    | Seq a b => uninited_reads inited a + uninited_reads (inited + inits a) b
    | Skip => []
    | Syntax.If e t f => (free_vars e - inited) + uninited_reads inited t + uninited_reads inited f
    | While e s => (free_vars e - inited) + uninited_reads inited s
    | Syntax.Call _ f args => List.fold_left (fun acc e => free_vars e - inited + acc) args (free_vars f - inited)
  end.

Require Import Bedrock.Platform.Cito.FuncCore.

Local Open Scope bool_scope.

Definition is_no_uninited_reads (f : FuncCore) := is_empty (uninited_reads (of_list (ArgVars f)) (Body f)).

Definition is_no_uninited (f : FuncCore) := is_no_uninited_reads f && mem (RetVar f) (inits (Body f)).
