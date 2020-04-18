Require Import Bedrock.Platform.AutoSep.


Definition mainS := SPEC reserving 0
  PREonly[_] Emp.

Definition m := bimport [[ "sys"!"abort" @ [abortS] ]]
  bmodule "test" {{
    bfunctionNoRet "main"() [mainS]
      Abort
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract sep_auto.
Qed.
