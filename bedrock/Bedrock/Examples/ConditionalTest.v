Require Import Bedrock.Examples.AutoSep.


Definition alwaysZeroS : spec := SPEC("x", "y") reserving 0
  PRE[_] Emp
  POST[R] [| R = $0 |].

Definition alwaysZero := bmodule "alwaysZero" {{
  bfunction "main"("x", "y") [alwaysZeroS]
    If* (("x" = 0) || (("x" = "y") && ("y" = 0))) {
      Return "x"
    } else {
      If* (!("x" = 0)) {
        Return 0
      } else {
        Fail
      }
    }
  end
}}.

Theorem alwaysZeroOk : moduleOk alwaysZero.
  vcgen; abstract (post; evaluate auto_ext; try congruence; sep_auto).
Qed.
