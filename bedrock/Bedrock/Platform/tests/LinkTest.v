Require Import Bedrock.Platform.AutoSep.


Definition spec1 := SPEC reserving 0
  PRE[_] Emp
  POST[_] Emp.

Definition spec2 := SPEC reserving 1
  PRE[_] Emp
  POST[_] Emp.

Definition m1 := bmodule "1" {{
  bfunction "f"() [spec1]
    Return 0
  end
}}.

Definition m2 := bimport [[ "1"!"f" @ [spec1] ]]
  bmodule "2" {{
    bfunction "g"() [spec2]
      Call "1"!"f"()
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end
  }}.

Theorem ok1 : moduleOk m1.
  vcgen; sep_auto.
Qed.

Theorem ok2 : moduleOk m2.
  vcgen; sep_auto; words.
Qed.

Definition m := link m1 m2.

Theorem ok : moduleOk m.
  link ok1 ok2.
Qed.
