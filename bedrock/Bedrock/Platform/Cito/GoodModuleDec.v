Set Implicit Arguments.

Local Open Scope bool_scope.
Local Notation "! b" := (negb b) (at level 35).

Require Import Bedrock.Word.
Import NArith.BinNat.
Local Open Scope N_scope.

Definition is_good_size (n : nat) :=
  match N.of_nat n ?= Npow2 32 with
    | Datatypes.Lt => true
    | _ => false
  end.

Require Import Bedrock.Platform.Cito.SyntaxModule.

Fixpoint is_arg_len_ok s :=
  match s with
    | Syntax.Call _ _ args => is_good_size (2 + length args)
    | Syntax.Skip => true
    | Syntax.Seq a b => is_arg_len_ok a && is_arg_len_ok b
    | Syntax.If _ a b => is_arg_len_ok a && is_arg_len_ok b
    | Syntax.While _ body => is_arg_len_ok body
    | Syntax.Assign _ _ => true
    | Syntax.Label _ _ => true
  end.

Require Import Bedrock.Platform.Cito.GetLocalVars.
Require Import Coq.Lists.List.
Require Import Bedrock.Platform.Cito.ListFacts3.
Require Import Bedrock.Platform.Cito.NoUninitDec.
Require Import Bedrock.Platform.Cito.Depth.

Definition is_good_func f :=
  let body := Body f in
  let local_vars := get_local_vars body (ArgVars f) (RetVar f) in
  let all_vars := ArgVars f ++ local_vars in
  is_no_dup (ArgVars f) &&
            is_no_uninited f &&
            is_arg_len_ok body &&
            is_good_size (length local_vars + depth body).

Definition is_good_funcs fs := forallb is_good_func fs.

Require Import Bedrock.Platform.Cito.NameDecoration.

Definition is_good_module (m : Module) :=
  is_good_module_name (SyntaxModule.Name m) &&
                      is_good_funcs (map Core (SyntaxModule.Functions m)) &&
                      is_no_dup (map SyntaxFunc.Name (SyntaxModule.Functions m)).
