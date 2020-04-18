Require Import Bedrock.Examples.AutoSep.

(** * A trivial example to make sure the separation logic proof automation isn't completely borked *)

Definition readS : spec := SPEC("x") reserving 1
  Al v,
  PRE[V] V "x" =*> v
  POST[R] [| R = v |] * V "x" =*> v.

Definition read := bmodule "read" {{
  bfunction "read"("x", "y") [readS]
    "y" <-* "x";;
    If ("y" = 0) {
      "x" *<- 0
    } else {
      "x" *<- "y"
    } ;;
    "y" <-* "x";;
    Return "y"
  end
}}.

Theorem readOk : moduleOk read.
(*TIME  Clear Timing Profile. *)
  vcgen; abstract sep_auto.
(*TIME  Print Timing Profile. *)
Qed.
