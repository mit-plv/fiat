Require Import Bedrock.Examples.AutoSep.

(** Swapping two pointers *)

Definition swapS : spec := SPEC("x", "y") reserving 2
  Al v, Al w,
  PRE[V] V "x" =*> v * V "y" =*> w
  POST[_] V "x" =*> w * V "y" =*> v.

Definition swap := bmodule "swap" {{
  bfunction "swap"("x", "y", "v", "w") [swapS]
    "v" <-* "x";;
    "w" <-* "y";;
    "x" *<- "w";;
    "y" *<- "v";;
    Return 0
  end
}}.

Theorem swapOk : moduleOk swap.
(*TIME Clear Timing Profile. *)
  vcgen; abstract sep_auto.
(*TIME Print Timing Profile. *)
Qed.
