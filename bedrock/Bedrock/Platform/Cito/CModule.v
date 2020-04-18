Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.GoodModuleDec.
Require Import Bedrock.Platform.Cito.FuncCore.

Record CFun :=
  {
    Core : FuncCore;
    good_func : is_good_func Core = true
  }.

Coercion Core : CFun >-> FuncCore.

Require Import Bedrock.Platform.Cito.StringMap.

Record CModule :=
  {
    Funs : StringMap.t CFun
  }.
