Require Import Bedrock.Examples.AutoSep.


(** * Always-0 *)

Definition always0S res : spec := SPEC reserving res
  PRE[_] Emp
  POST[R] [| R = 0 |].

Definition always0 := bmodule "always0" {{
  bfunction "main"("f") [always0S 2]
    "f" <-- Lambda() [always0S 0]
      Return 0
    end;;

    "f" <-- ICall "f"()
    [PRE[_, R] [| R = 0 |]
     POST[R'] [| R' = 0 |] ];;
    Return "f"
  end
}}.

Hint Extern 1 (@eq W _ _) => words.

Theorem always0Ok : moduleOk always0.
  vcgen; abstract (post; try icall (@nil string); (sep_auto; auto)).
Qed.


(** * Add three numbers *)

Definition add3S : spec := SPEC("x", "y", "z") reserving 5
  PRE[V] Emp
  POST[R] [| R = V "x" ^+ V "y" ^+ V "z" |].

Definition addS : spec := SPEC("x", "y") reserving 0
  PRE[V] Emp
  POST[R] [| R = V "x" ^+ V "y" |].

Definition add3 := bmodule "add3" {{
  bfunction "add3"("x", "y", "z", "f", "tmp") [add3S]
    "f" <-- Lambda("x", "y") [addS]
      Return "x" + "y"
    end;;

    "tmp" <-- ICall "f"("x", "y")
    [PRE[V, R] Emp
     POST[R'] [| R' = R ^+ V "z" |]];;

    Return "tmp" + "z"
  end
}}.

Theorem add3Ok : moduleOk add3.
  vcgen; abstract (post; try icall ("x" :: "y" :: nil); (sep_auto; auto)).
Qed.
