Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Syntax.
Require Import Coq.Strings.String.

Record FuncCore :=
  {
    ArgVars : list string;
    RetVar : string;
    Body : Stmt
  }.
