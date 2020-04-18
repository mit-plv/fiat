Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.Facade.
Require Bedrock.Platform.Cito.Semantics.

Require Import Coq.Strings.String.
Require Import Bedrock.Platform.Cito.SyntaxExpr.

Fixpoint compile (s : Stmt) : Syntax.Stmt :=
  match s with
    | Skip => Syntax.Skip
    | Seq a b => Syntax.Seq (compile a) (compile b)
    | If e t f => Syntax.If e (compile t) (compile f)
    | While e c => Syntax.While e (compile c)
    | Facade.Assign x e => Syntax.Assign x e
    | Label x lbl => Syntax.Label x lbl
    | Call x f args => Syntax.Call (Some x) f (List.map Var args)
  end.

Require Import Bedrock.Platform.Cito.ListFacts3.

Definition compile_op (spec : OperationalSpec) :=
  {|
    Semantics.Fun :=
      {|
        FuncCore.ArgVars := ArgVars spec;
        FuncCore.RetVar := RetVar spec;
        FuncCore.Body := compile (Body spec)
      |};
    Semantics.NoDupArgVars := args_no_dup spec
  |}.
