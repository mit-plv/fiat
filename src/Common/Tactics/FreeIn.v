Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Ltac free_in x y :=
  idtac;
  match y with
  | context[x] => fail 1 x "appears in" y
  | _ => idtac
  end.
