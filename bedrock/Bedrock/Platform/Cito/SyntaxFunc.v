Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Syntax.
Require Import Coq.Strings.String.
Require Import Bedrock.Platform.Cito.FuncCore.
Export Syntax FuncCore.

Record Func :=
  {
    Name : string;
    Core : FuncCore
  }.

Coercion Core : Func >-> FuncCore.
