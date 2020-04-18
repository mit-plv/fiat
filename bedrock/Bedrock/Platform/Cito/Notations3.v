Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Cito.Syntax.
Require Import Bedrock.Platform.Cito.SyntaxExpr Bedrock.Memory Bedrock.IL Coq.Strings.String.

Set Implicit Arguments.

Coercion Const : W >-> Expr.
Coercion Var : string >-> Expr.

Infix "+" := (SyntaxExpr.Binop Plus) : expr_scope.
Infix "-" := (SyntaxExpr.Binop Minus) : expr_scope.
Infix "*" := (SyntaxExpr.Binop Times) : expr_scope.
Infix "=" := (SyntaxExpr.TestE IL.Eq) : expr_scope.
Infix "<>" := (SyntaxExpr.TestE IL.Ne) : expr_scope.
Infix "<" := (SyntaxExpr.TestE IL.Lt) : expr_scope.
Infix "<=" := (SyntaxExpr.TestE IL.Le) : expr_scope.

Delimit Scope expr_scope with expr.
Local Open Scope expr.

Infix ";;" := Syntax.Seq : stmt_scope.

Notation "'skip'" := Syntax.Skip : stmt_scope.

Notation "'If' cond { trueStmt } 'else' { falseStmt }" := (Syntax.If cond%expr trueStmt falseStmt) : stmt_scope.

Notation "x <- e" := (Syntax.Assign x e%expr) : stmt_scope.

Delimit Scope stmt_scope with stmt.
Local Open Scope stmt.

Definition DirectCall x f args := (Syntax.Label "_f" f ;; Syntax.Call x "_f" args)%stmt.

Notation "'DCall' f ()" := (DirectCall None f nil)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "'DCall' f ( x1 , .. , xN )" := (DirectCall None f (cons x1 (.. (cons xN nil) ..))%expr)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "x <-- 'DCall' f ()" := (DirectCall (Some x) f nil)
  (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "x <-- 'DCall' f ( x1 , .. , xN )" := (DirectCall (Some x) f (cons x1 (.. (cons xN nil) ..))%expr) (no associativity, at level 95, f at level 0) : stmt_scope.

Notation "a ! b" := (a, b) (only parsing) : stmt_scope.

Local Close Scope stmt.
Local Close Scope expr.
