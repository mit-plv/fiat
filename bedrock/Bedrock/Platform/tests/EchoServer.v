Require Import Bedrock.Platform.Thread Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers Bedrock.Platform.Io.

Local Hint Extern 1 (@eq W _ _) => words.


Module Type S.
  Parameters globalSched globalSock : W.

  Parameter inbuf_size : nat.
  Axiom inbuf_size_lower : (inbuf_size >= 2)%nat.
  Axiom inbuf_size_upper : (N_of_nat (inbuf_size * 4) < Npow2 32)%N.

  Parameters port numWorkers : W.
End S.

Module Make(M : S).
Import M.

Module M'''.
  Definition globalSched := M.globalSched.

  Open Scope Sep_scope.

  Definition globalInv (fs : files) : HProp := Ex fr, globalSock =*> fr * [| fr %in fs |].
End M'''.

Module T := Thread.Make(M''').

Import T M'''.
Export T M'''.

Module MyM.
  Definition sched := sched.
  Definition globalInv := globalInv.
End MyM.

Ltac unf := unfold MyM.sched, MyM.globalInv, M'''.globalSched, M'''.globalInv in *.

Module MyIo := Io.Make(MyM).


Definition hints : TacPackage.
  prepare (materialize_buffer, buffer_split_tagged) buffer_join_tagged.
Defined.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * globalSock =?> 1 * mallocHeap 0.

Definition handlerS := SPEC reserving 99
  Al fs, PREmain[_] sched fs * globalInv fs * mallocHeap 0.

Definition bsize := (inbuf_size * 4)%nat.

Definition m := bimport [[ "buffers"!"bmalloc" @ [bmallocS],
                           "scheduler"!"init"@ [T.Q''.initS], "scheduler"!"exit" @ [T.Q''.exitS],
                           "scheduler"!"spawn" @ [T.Q''.spawnS], "scheduler"!"listen" @ [T.Q''.listenS],
                           "scheduler"!"accept" @ [T.Q''.acceptS], "scheduler"!"close" @ [T.Q''.closeS],
                           "scheduler"!"read" @ [T.Q''.readS], "io"!"writeAll" @ [MyIo.writeAllS] ]]
  bmodule "echo" {{
    bfunctionNoRet "handler"("buf", "fr", "n") [handlerS]
      "buf" <-- Call "buffers"!"bmalloc"(inbuf_size)
      [Al fs, PREmain[V, R] R =?>8 bsize * sched fs * globalInv fs * mallocHeap 0];;

      [Al fs, PREmain[V] V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0]
      While (0 = 0) {
        "fr" <-- Call "scheduler"!"accept"($[globalSock])
        [Al fs, PREmain[V, R] [| R %in fs |] * V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0];;

        "n" <-- Call "scheduler"!"read"("fr", "buf", bsize)
        [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0];;

        [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0]
        While ("n" <> 0) {
          If ("n" <= bsize) {
            Call "io"!"writeAll"("fr", "buf", 0, "n")
            [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0]
          } else {
            Skip
          };;

          "n" <-- Call "scheduler"!"read"("fr", "buf", bsize)
          [Al fs, PREmain[V] [| V "fr" %in fs |] * V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0]
        };;

        Call "scheduler"!"close"("fr")
        [Al fs, PREmain[V] V "buf" =?>8 bsize * sched fs * globalInv fs * mallocHeap 0]
      }
    end with bfunctionNoRet "main"("fr", "x") [mainS]
      Init
      [Al fs, Al v, PREmain[_] sched fs * globalSock =*> v * mallocHeap 0];;

      "fr" <- 0;;
      [Al fs, PREmain[_] sched fs * globalSock =?> 1 * mallocHeap 0]
      While ("fr" < numWorkers) {
        Spawn("echo"!"handler", 100)
        [Al fs, PREmain[_] sched fs * globalSock =?> 1 * mallocHeap 0];;
        "fr" <- "fr" + 1
      };;

      "fr" <-- Call "scheduler"!"listen"(port)
      [Al fs, Al v, PREmain[_, R] [| R %in fs |] * sched fs * globalSock =*> v * mallocHeap 0];;

      globalSock *<- "fr";;

      Exit 50
    end
  }}.

Lemma le_bsize : forall w : W,
  w <= natToW bsize
  -> (wordToNat w <= bsize)%nat.
  intros; pre_nomega;
    rewrite wordToNat_natToWord_idempotent in * by apply inbuf_size_upper; assumption.
Qed.

Local Hint Immediate le_bsize.

Lemma inbuf_size_small : (N.of_nat inbuf_size < Npow2 32)%N.
  specialize inbuf_size_upper;  generalize (Npow2 32); intros; nomega.
Qed.

Hint Rewrite Nat2N.inj_mul N2Nat.inj_mul : N.
Lemma le_inbuf_size : natToW 2 <= natToW inbuf_size.
  pre_nomega; rewrite wordToNat_natToWord_idempotent by apply inbuf_size_small;
    rewrite wordToNat_natToWord_idempotent by reflexivity; apply inbuf_size_lower.
Qed.

Local Hint Immediate le_inbuf_size.

Lemma roundTrip_inbuf_size : wordToNat (natToW inbuf_size) = inbuf_size.
  rewrite wordToNat_natToWord_idempotent by apply inbuf_size_small; auto.
Qed.

Lemma roundTrip_bsize : wordToNat (natToW bsize) = bsize.
  rewrite wordToNat_natToWord_idempotent by apply inbuf_size_upper; auto.
Qed.

Hint Rewrite roundTrip_inbuf_size roundTrip_bsize : sepFormula.

Theorem goodSize_bsize : goodSize bsize.
  apply inbuf_size_upper.
Qed.

Local Hint Immediate goodSize_bsize.

Ltac t := try solve [ sep unf hints; auto ];
  unf; unfold localsInvariantMain; post; evaluate hints; descend;
    try match_locals; sep unf hints; auto.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
