Ltac free_in x y :=
  idtac;
  match y with
  | appcontext[x] => fail 1 x "appears in" y
  | _ => idtac
  end.
