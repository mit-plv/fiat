Require Import Bedrock.Platform.Thread Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers.

Local Hint Extern 1 (@eq W _ _) => words.


Module Type S.
  Parameters globalSched : W.

  Parameters port : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (fs : files) : HProp := Emp.
End M'''.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * mallocHeap 0.

Definition handlerS := SPEC reserving 99
  Al fs, PREmain[_] sched fs * mallocHeap 0.

Definition inbuf_size := 2.
Definition bsize := (inbuf_size * 4)%nat.

Ltac unf := unfold M'''.globalSched, M'''.globalInv, bsize in *.

Definition m := bimport [[ "buffers"!"bmalloc" @ [bmallocS], "buffers"!"bfree" @ [bfreeS],
                           "scheduler"!"init"@ [T.Q''.initS], "scheduler"!"exit" @ [T.Q''.exitS],
                           "scheduler"!"spawn" @ [T.Q''.spawnS], "scheduler"!"listen" @ [T.Q''.listenS],
                           "scheduler"!"accept" @ [T.Q''.acceptS], "scheduler"!"close" @ [T.Q''.closeS],
                           "scheduler"!"read" @ [T.Q''.readS], "sys"!"printInt" @ [printIntS] ]]
  bmodule "increment" {{
    bfunctionNoRet "handler"("buf", "listener", "accepted", "n", "Sn") [handlerS]
      "listener" <-- Call "scheduler"!"listen"(port)
      [Al fs, PREmain[_, R] [| R %in fs |] * sched fs * mallocHeap 0];;

      "buf" <-- Call "buffers"!"bmalloc"(inbuf_size)
      [Al fs, PREmain[V, R] R =?>8 bsize * [| R <> 0 |] * [| freeable R inbuf_size |] * [| V "listener" %in fs|] * sched fs * mallocHeap 0];;

      "accepted" <-- Call "scheduler"!"accept"("listener")
      [Al fs, PREmain[V, R] [| R %in fs |] * V "buf" =?>8 bsize * [| V "buf" <> 0 |] * [| freeable (V "buf") inbuf_size |] * [| V "listener" %in fs|] * sched fs * mallocHeap 0];;

      "n" <-- Call "scheduler"!"read"("accepted", "buf", bsize)
      [Al fs, PREmain[V] [| V "accepted" %in fs |] * V "buf" =?>8 bsize * [| V "buf" <> 0 |] * [| freeable (V "buf") inbuf_size |] * [| V "listener" %in fs|] * sched fs * mallocHeap 0];;

      "Sn" <- "n" + 1;;
      Call "scheduler"!"close"("accepted")
      [Al fs, PREmain[V] V "buf" =?>8 bsize * [| V "buf" <> 0 |] * [| freeable (V "buf") inbuf_size |] * [| V "listener" %in fs|] * sched fs * mallocHeap 0 * [| V "Sn" = V "n" ^+ $1 |] ];;

      Call "scheduler"!"close"("listener")
      [Al fs, PREmain[V] V "buf" =?>8 bsize * [| V "buf" <> 0 |] * [| freeable (V "buf") inbuf_size |] * sched fs * mallocHeap 0 * [| V "Sn" = V "n" ^+ $1 |] ];;

      Call "buffers"!"bfree"("buf", inbuf_size)
      [Al fs, PREmain[V] sched fs * mallocHeap 0 * [| V "Sn" = V "n" ^+ $1 |] ];;

      Call "sys"!"printInt"("Sn")
      [Al fs, PREmain[V] sched fs * mallocHeap 0 * [| V "Sn" = V "n" ^+ $1 |] ];;

      Exit 100
    end with bfunctionNoRet "main"("fr", "x") [mainS]
      Init
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Spawn("increment"!"handler", 100)
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      Exit 50
    end
  }}.

Hint Extern 1 (_ %in _) =>
  eapply incl_mem; [ eassumption |
                     repeat (eapply incl_trans; [ eassumption | ]); apply incl_refl ].

Ltac t := try solve [ sep unf hints; auto ];
  unf; unfold localsInvariantMain; post; evaluate hints; descend;
    try match_locals; sep unf hints; auto.

Ltac u := solve [ t ].

Opaque inbuf_size.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
