Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.Thread Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays.

Local Hint Extern 1 (@eq W _ _) => words.


Module Type S.
  Parameters globalSched globalSock : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (fs : files) : HProp := Ex fr, globalSock =*> fr * [| fr %in fs |].
End M'''.

Ltac unf := unfold M'''.globalSched, M'''.globalInv in *.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Definition hints : TacPackage.
  prepare (materialize_buffer, buffer_split_tagged) buffer_join_tagged.
Defined.

Ltac sep := T.sep unf hints.

Definition handlerS := SPEC reserving 49
  Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * globalSock =?> 1 * mallocHeap 0.

Definition writeSomeS := SPEC("fr", "buf", "len") reserving 36
  Al fs, Al len,
  PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len * [| (wordToNat (V "len") <= len)%nat |]
    * sched fs * globalInv fs * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS],
                           "scheduler"!"init" @ [initS], "scheduler"!"exit" @ [exitS],
                           "scheduler"!"spawn" @ [spawnS], "scheduler"!"listen" @ [listenS],
                           "scheduler"!"accept" @ [acceptS], "scheduler"!"read" @ [readS],
                           "scheduler"!"write" @ [writeS], "scheduler"!"close" @ [closeS] ]]
  bmodule "test" {{
    bfunction "writeSome"("fr", "buf", "len") [writeSomeS]
      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "len")) (V "buf") len
          * [| (wordToNat (V "len") <= len)%nat |] * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "len")) (V "buf") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Call "scheduler"!"write"("fr", "buf", "len")
      [PRE[_] Emp POST[_] Emp];;
      Return 0
    end with bfunctionNoRet "handler"("buf", "fr", "n") [handlerS]
      "buf" <-- Call "malloc"!"malloc"(0, 10)
      [Al fs, PREmain[_, R] R =?> 10 * sched fs * globalInv fs * mallocHeap 0];;

      Note [please_materialize_buffer 10];;

      [Al fs, PREmain[V] V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
      While (0 = 0) {
        "fr" <-- Call "scheduler"!"accept"($[globalSock])
        [Al fs, PREmain[V, R] [| R %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0];;

        "n" <-- Call "scheduler"!"read"("fr", "buf", 40)
        [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0];;

        [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
        While ("n" <> 0) {
          If ("n" <= 40) {
            Call "test"!"writeSome"("fr", "buf", "n")
            [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
          } else {
            Skip
          };;

          "n" <-- Call "scheduler"!"read"("fr", "buf", 40)
          [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
        };;

        Call "scheduler"!"close"("fr")
        [Al fs, PREmain[V] V "buf" =?>8 40 * sched fs * globalInv fs * mallocHeap 0]
      }
    end with bfunctionNoRet "main"("fr", "x") [mainS]
      Init
      [Al fs, Al v, PREmain[_] sched fs * globalSock =*> v * mallocHeap 0];;

      "fr" <-- Call "scheduler"!"listen"(8080%N)
      [Al fs, Al v, PREmain[_, R] [| R %in fs |] * sched fs * globalSock =*> v * mallocHeap 0];;

      globalSock *<- "fr";;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Spawn("test"!"handler", 50)
      [Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0];;

      Exit 50
    end
  }}.

Opaque allocated.

Lemma single_cell : forall p,
  (p =?> 1 = (Ex v, p =*> v) * Emp)%Sep.
  auto.
Qed.

Lemma le_40 : forall w : W,
  w <= natToW 40
  -> (wordToNat w <= 40)%nat.
  intros; pre_nomega.
  rewrite wordToNat_natToWord_idempotent in * by reflexivity; omega.
Qed.

Hint Immediate le_40.

Ltac t' := try rewrite (single_cell globalSock); sep; auto.
Ltac t := solve [ t'
  | post; evaluate hints; descend; try match_locals; t' ].

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
