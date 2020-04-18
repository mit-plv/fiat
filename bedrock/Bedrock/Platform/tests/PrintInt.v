Require Import Bedrock.Platform.AutoSep.


Definition mainS := SPEC reserving 3
  PREonly[_] Emp.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS] ]]
  bmodule "test" {{
    bfunctionNoRet "main"("i") [mainS]
      "i" <- 0;;

      [PREonly[_] Emp]
      While ("i" < 10) {
        Call "sys"!"printInt"("i")
        [PREonly[_] Emp];;

        "i" <- "i" + 1
      };;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
