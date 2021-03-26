Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Ltac get_goal :=
  match goal with |- ?G => G end.
