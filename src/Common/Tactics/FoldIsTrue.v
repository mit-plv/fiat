(* These tactics do [change (?x = true) with (is_true x) in *], but get around anomalies in older versions of 8.4 *)
Ltac fold_is_true' x :=
  change (x = true) with (is_true x) in *.
Ltac fold_is_true :=
  repeat match goal with
         | [ H : context[?x = true] |- _ ] => fold_is_true' x
         | [ |- context[?x = true] ] => fold_is_true' x
         end.
