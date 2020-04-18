Require Import Bedrock.Platform.tests.Thread0 Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays Bedrock.Platform.Buffers.

Local Hint Extern 1 (@eq W _ _) => words.


Module Type S.
  Parameter globalSched : W.

  Parameter inbuf_size : nat.
  Axiom inbuf_size_lower : (inbuf_size >= 2)%nat.
  Axiom inbuf_size_upper : (N_of_nat (inbuf_size * 4) < Npow2 32)%N.
End S.

Module Make(M : S).
Import M.

Module T := Thread0.Make(M).
Import T.

Definition hints : TacPackage.
  prepare (materialize_buffer, buffer_split_tagged) buffer_join_tagged.
Defined.

Definition mainS := SPEC reserving 49
  PREmain[_] globalSched =?> 1 * mallocHeap 0.

Definition bsize := (inbuf_size * 4)%nat.

Inductive reveal_split : Prop := RevealSplit.
Hint Constructors reveal_split.

Definition m := bimport [[ "buffers"!"bmalloc" @ [bmallocS],
                           "scheduler"!"init"@ [T.Q''.initS], "scheduler"!"exit" @ [T.Q''.exitS],
                           "scheduler"!"connect" @ [T.Q''.connectS],
                           "scheduler"!"connected" @ [T.Q''.connectedS],
                           "sys"!"abort" @ [Sys.abortS],
                           "sys"!"read" @ [Sys.readS], "scheduler"!"write" @ [T.Q''.writeS] ]]
  bmodule "connect" {{
    bfunctionNoRet "main"("fr", "buf", "n") [mainS]
      Init
      [Al fs, PREmain[_] sched fs * mallocHeap 0];;

      "buf" <-- Call "buffers"!"bmalloc"(inbuf_size)
      [Al fs, PREmain[V, R] R =?>8 bsize * sched fs * mallocHeap 0];;

      "n" <-- Call "sys"!"read"(0, "buf", bsize)
      [Al fs, PREmain[V] V "buf" =?>8 bsize * sched fs * mallocHeap 0];;

      If ("n" > bsize) {
        Call "sys"!"abort"()
        [PREmain[_] [| False |] ];;
        Fail
      } else {
        Note [reveal_split];;

        Assert [Al fs, PREmain[V] [| wordToNat (V "n") <= bsize |]%nat
          * buffer_splitAt (wordToNat (V "n")) (V "buf") bsize * sched fs * mallocHeap 0];;

        "fr" <-- Call "scheduler"!"connect"("buf", "n")
        [Al fs, PREmain[V, R] [| R %in fs |] * sched fs * mallocHeap 0
          * V "buf" =?>8 wordToNat (V "n") * (V "buf" ^+ V "n") =?>8 (bsize - wordToNat (V "n"))];;

        Call "scheduler"!"connected"("fr")
        [Al fs, PREmain[V] [| V "fr" %in fs |] * sched fs * mallocHeap 0
          * V "buf" =?>8 wordToNat (V "n") * (V "buf" ^+ V "n") =?>8 (bsize - wordToNat (V "n"))];;

        Call "scheduler"!"write"("fr", "buf", "n")
        [Al fs, PREmain[V, R] sched fs * mallocHeap 0
          * V "buf" =?>8 wordToNat (V "n") * (V "buf" ^+ V "n") =?>8 (bsize - wordToNat (V "n"))];;

        Diverge
      }
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

Ltac t :=
  try match goal with
        | [ |- context[reveal_split] ] => unfold buffer_splitAt
      end;
  sep hints; auto.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.

End Make.
