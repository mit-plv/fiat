Require Import Bedrock.Platform.tests.Thread0 Bedrock.Platform.SinglyLinkedList.


Module Make(M : S).
Import M.

Module T := Thread0.Make(M).
Import T.

Definition handlerS := SPEC reserving 49
  Al fs, PREmain[_] sched fs * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"yield" @ [yieldS] ]]
  bmodule "test" {{
    bfunctionNoRet "handler"("i", "p", "r") [handlerS]
      "i" <- 0;; (* Loop counter *)
      "p" <- 0;; (* Pointer to head of list we will build *)

      [Al fs, PREmain[V] Ex ls, sll ls (V "p") * sched fs * mallocHeap 0]
      While ("i" < 10) {
        "r" <-- Call "malloc"!"malloc"(0, 2)
        [Al fs, PREmain[V, R] [| R <> 0 |] * [| freeable R 2 |] * R =?> 2 * Ex ls, sll ls (V "p") * sched fs * mallocHeap 0];;

        "r" *<- "i";;
        "r" + 4 *<- "p";;
        "p" <- "r";;
        "i" <- "i" + 1;;

        Yield
        [Al fs, PREmain[V] Ex ls, sll ls (V "p") * sched fs * mallocHeap 0]
      };;

      [Al fs, PREmain[V] Ex ls, sll ls (V "p") * sched fs * mallocHeap 0]
      While ("p" <> 0) {
        "r" <- "p";;
        "p" <-* "p" + 4;;
        Call "malloc"!"free"(0, "r", 2)
        [Al fs, PREmain[V] Ex ls, sll ls (V "p") * sched fs * mallocHeap 0];;

        Yield
        [Al fs, PREmain[V] Ex ls, sll ls (V "p") * sched fs * mallocHeap 0]
      };;

      Exit 50
    end with bfunctionNoRet "main"("x", "y") [mainS]
      Init
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Exit 50
    end
  }}.

Theorem ok : moduleOk m.
  vcgen; abstract (sep SinglyLinkedList.hints; auto).
Qed.

End Make.
