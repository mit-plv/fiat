Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Scheduler Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers.


Section specs.
  Variables sched globalInv : bag -> HProp.

  Definition readSomeGS := SPEC("fr", "buf", "start", "len") reserving 36
    Al fs, Al len,
    PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len
      * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
      * sched fs * globalInv fs * mallocHeap 0
    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0.

  Definition writeSomeGS := SPEC("fr", "buf", "start", "len") reserving 36
    Al fs, Al len,
    PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len
      * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
      * sched fs * globalInv fs * mallocHeap 0
    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0.

  Definition readUntilGS := SPEC("fr", "buf", "len", "ch") reserving 39
    Al fs,
    PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
      * sched fs * globalInv fs * mallocHeap 0
    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len") * sched fs' * globalInv fs' * mallocHeap 0.

  Definition writeAllGS := SPEC("fr", "buf", "start", "len") reserving 42
    Al fs, Al len,
    PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len
      * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
      * [| goodSize len |]
      * sched fs * globalInv fs * mallocHeap 0
    POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0.
End specs.

Module Type S.
  Parameters sched globalInv : bag -> HProp.
End S.

Module Make(M : S).
Import M.

Definition hints : TacPackage.
  prepare buffer_split_tagged buffer_join_tagged.
Defined.

Definition readSomeS := readSomeGS sched globalInv.
Definition writeSomeS := writeSomeGS sched globalInv.
Definition readUntilS := readUntilGS sched globalInv.
Definition writeAllS := writeAllGS sched globalInv.

Definition m := bimport [[ "scheduler"!"read" @ [readGS sched globalInv],
                           "scheduler"!"write" @ [writeGS sched globalInv],
                           "sys"!"abort" @ [abortS], "buffers"!"contains" @ [containsS] ]]
  bmodule "io" {{
    bfunction "readSome"("fr", "buf", "start", "len") [writeSomeS]
      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "start")) (V "buf") len
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "start")) (V "buf") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "start")) (V "buf") len
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
          * [| (wordToNat (V "start") <= len)%nat |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "start")) (V "buf") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * (V "buf" ^+ V "start") =?>8 (len - wordToNat (V "start"))
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
            * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * (V "buf" ^+ V "start") =?>8 (len - wordToNat (V "start"))
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "len")) (V "buf" ^+ V "start") len
          * [| (wordToNat (V "len") <= len)%nat |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "len")) (V "buf" ^+ V "start") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      "buf" <- "buf" + "start";;
      "len" <-- Call "scheduler"!"read"("fr", "buf", "len")
      [PRE[_] Emp POST[_] Emp];;
      Return "len"
    end with bfunction "writeSome"("fr", "buf", "start", "len") [writeSomeS]
      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "start")) (V "buf") len
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "start")) (V "buf") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "start")) (V "buf") len
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
          * [| (wordToNat (V "start") <= len)%nat |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "start")) (V "buf") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * (V "buf" ^+ V "start") =?>8 (len - wordToNat (V "start"))
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
            * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * (V "buf" ^+ V "start") =?>8 (len - wordToNat (V "start"))
          * sched fs' * globalInv fs' * mallocHeap 0];;

      Assert [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "len")) (V "buf" ^+ V "start") len
          * [| (wordToNat (V "len") <= len)%nat |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "len")) (V "buf" ^+ V "start") len
          * sched fs' * globalInv fs' * mallocHeap 0];;

      "buf" <- "buf" + "start";;
      "len" <-- Call "scheduler"!"write"("fr", "buf", "len")
      [PRE[_] Emp POST[_] Emp];;
      Return "len"
    end with bfunction "readUntil"("fr", "buf", "len", "ch", "readSoFar", "n", "b") [readUntilS]
      "n" <-- Call "scheduler"!"read"("fr", "buf", "len")
      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len") * sched fs' * globalInv fs'
          * mallocHeap 0];;

      "readSoFar" <- 0;;

      [Al fs,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len") * sched fs' * globalInv fs'
          * mallocHeap 0]
      While ("n" <> 0) {
        If ("len" < "n") {
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ];;
          Fail
        } else {
          Assert [Al fs,
            PRE[V] [| V "fr" %in fs |] * buffer_splitAt (wordToNat (V "n")) (V "buf") (wordToNat (V "len"))
              * [| (wordToNat (V "n") <= wordToNat (V "len"))%nat |]
              * sched fs * globalInv fs * mallocHeap 0
            POST[_] Ex fs', [| fs %<= fs' |] * buffer_joinAt (wordToNat (V "n")) (V "buf") (wordToNat (V "len"))
              * sched fs' * globalInv fs' * mallocHeap 0];;

          "b" <-- Call "buffers"!"contains"("buf", "n", "ch")
          [Al fs,
            PRE[V] [| V "fr" %in fs |] * (V "buf" ^+ V "n") =?>8 wordToNat (V "len" ^- V "n")
              * sched fs * globalInv fs * mallocHeap 0
            POST[_] Ex fs', [| fs %<= fs' |] * (V "buf" ^+ V "n") =?>8 wordToNat (V "len" ^- V "n") * sched fs'
              * globalInv fs' * mallocHeap 0];;

          "readSoFar" <- "readSoFar" + "n";;

          If ("b" <> neg1) {
            Return "readSoFar"
          } else {
            "len" <- "len" - "n";;
            "buf" <- "buf" + "n";;

            "n" <-- Call "scheduler"!"read"("fr", "buf", "len")
            [Al fs,
              PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 wordToNat (V "len")
                * sched fs * globalInv fs * mallocHeap 0
              POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 wordToNat (V "len") * sched fs' * globalInv fs'
                * mallocHeap 0]
          }
        }
      };;

      Return 0
    end with bfunction "writeAll"("fr", "buf", "start", "len", "n") [writeAllS]
      [Al fs, Al len,
        PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len
          * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
          * [| goodSize (wordToNat (V "start") + wordToNat (V "len")) |]
          * sched fs * globalInv fs * mallocHeap 0
        POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0 ]
      While ("len" <> 0) {
        "n" <-- Call "io"!"writeSome"("fr", "buf", "start", "len")
        [Al fs, Al len,
          PRE[V] [| V "fr" %in fs |] * V "buf" =?>8 len
            * [| (wordToNat (V "start") + wordToNat (V "len") <= len)%nat |]
            * [| goodSize (wordToNat (V "start") + wordToNat (V "len")) |]
            * sched fs * globalInv fs * mallocHeap 0
          POST[_] Ex fs', [| fs %<= fs' |] * V "buf" =?>8 len * sched fs' * globalInv fs' * mallocHeap 0 ];;

        If ("n" > "len") {
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ];;
          Fail
        } else {
          "len" <- "len" - "n";;
          "start" <- "start" + "n"
        }
      };;

      Return 0
    end
  }}.

Hint Rewrite natToW_wordToNat : sepFormula.

Ltac match_locals :=
  match goal with
    | [ _ : context[locals ?NS ?X _ _] |- context[locals ?NS ?Y _ _] ] => equate X Y
  end; descend.

Hint Extern 1 (@eq W _ _) => words.

Ltac t := solve [ sep hints; eauto
  | post; evaluate hints; repeat rewrite natToW_wordToNat in *; descend;
    try match_locals; sep hints; eauto ].

Local Hint Immediate incl_mem.

Local Hint Extern 2 (goodSize _) => eapply goodSize_weaken; [ eassumption | ].

Lemma wordToNat_wplus' : forall u v w : W,
  v <= w
  -> goodSize (wordToNat u + wordToNat w)
  -> wordToNat (u ^+ v) = wordToNat u + wordToNat v.
  intros; rewrite wordToNat_wplus; try nomega; eapply goodSize_weaken; eauto; nomega.
Qed.

Local Hint Extern 2 (_ <= _)%nat => try erewrite wordToNat_wplus' by eassumption; nomega.

Hint Rewrite wordToNat_wminus using nomega : sepFormula.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
