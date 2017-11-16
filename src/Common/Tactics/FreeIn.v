Ltac free_in x y :=
  idtac;
  match y with
  | context[x] => fail 1 x "appears in" y
  | _ => idtac
  end.
