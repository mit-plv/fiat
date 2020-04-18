Require Import Bedrock.Platform.Thread Bedrock.Platform.SinglyLinkedList.


Module Type S.
  Parameters globalList globalSched : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (_ : files) : HProp := Ex p, globalList =*> p * Ex ls, sll ls p.
End M'''.

Ltac unf := unfold M'''.globalSched, M'''.globalInv in *.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Ltac sep := T.sep unf SinglyLinkedList.hints.

Definition handlerS := SPEC reserving 49
  Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * globalList =?> 1 * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"yield" @ [yieldS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("i", "p", "r") [handlerS]
      "i" <- 0;; (* Loop counter *)

      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0]
      While ("i" < 10) {
        "r" <-- Call "malloc"!"malloc"(0, 2)
        [Al fs, PREmain[V, R] [| R <> 0 |] * [| freeable R 2 |] * R =?> 2 * sched fs * globalInv fs * mallocHeap 0];;

        "r" *<- "i";;
        "p" <-* globalList;;
        "r" + 4 *<- "p";;
        globalList *<- "r";;
        "i" <- "i" + 1;;

        Yield
        [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0]
      };;

      "p" <-* globalList;;
      [Al fs, PREmain[V] sched fs * globalList =*> V "p" * Ex ls, sll ls (V "p") * mallocHeap 0]
      While ("p" <> 0) {
        "r" <- "p";;
        "p" <-* "p" + 4;;
        globalList *<- "p";;
        Call "malloc"!"free"(0, "r", 2)
        [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

        Yield
        [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

        "p" <-* globalList
      };;

      Exit 50
    end with bfunctionNoRet "main"("x", "y") [mainS]
      globalList *<- 0;;

      Init
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Exit 50
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract (sep; auto).
Qed.

End Make.
