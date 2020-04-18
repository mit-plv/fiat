Require Import Bedrock.Platform.Cito.SyntaxFunc.
Require Import Coq.Strings.String.
Export SyntaxFunc.

Set Implicit Arguments.

Record Module :=
  {
    Name : string;
    Functions : list Func
  }.
