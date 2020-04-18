Require Import Bedrock.Examples.AutoSep.

(** Read from pointers in variables *)

Definition indirS : spec := SPEC("x") reserving 1
  Al v,
  PRE[V] V "x" =*> v
  POST[R] [| R = v |] * V "x" =*> v.

Definition indir := bmodule "indir" {{
  bfunction "indir"("x", "y") [indirS]
    "y" <-* "x";;
    Return "y"
  end
}}.

Theorem indirOk : moduleOk indir.
  vcgen; abstract sep_auto.
Qed.

Definition doubleIndirS : spec := SPEC("x") reserving 1
  Al p, Al v,
  PRE[V] V "x" =*> p * p =*> v
  POST[R] [| R = v |] * V "x" =*> p * p =*> v.

Definition doubleIndir := bmodule "doubleIndir" {{
  bfunction "doubleIndir"("x", "y") [doubleIndirS]
    "y" <-* "x";;
    "y" <-* "y";;
    Return "y"
  end
}}.

Theorem doubleIndirOk : moduleOk doubleIndir.
(*TIME Clear Timing Profile. *)
  vcgen; abstract sep_auto.
(*TIME Print Timing Profile. *)
Qed.
