Require Import Bedrock.Platform.tests.Thread0.


Module Make(M : S).
Import M.

Module T := Thread0.Make(M).
Import T.

Definition handlerS := SPEC reserving 49
  Al fs, PREmain[_] sched fs * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * mallocHeap 0.

Definition m := bimport [[ "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("x", "y") [handlerS]
      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;
      Exit 50
    end with bfunctionNoRet "main"("x", "y") [mainS]
      Init
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Exit 50
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract (sep_auto; auto).
Qed.

End Make.
