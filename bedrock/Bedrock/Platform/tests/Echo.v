Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.


Definition mainS := SPEC reserving 12
  PREonly[_] mallocHeap 0.

Definition writeS := SPEC("fd", "buf", "len") reserving 4
  Al len,
  PRE[V] V "buf" =?>8 len * [| (wordToNat (V "len") <= len)%nat |]
  POST[_] V "buf" =?>8 len.

Opaque allocated.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS],
                           "sys"!"listen" @ [listenS], "sys"!"accept" @ [acceptS],
                           "sys"!"read" @ [readS], "sys"!"write" @ [Sys.writeS],
                           "malloc"!"malloc" @ [mallocS] ]]
  bmodule "test" {{
    bfunction "write"("fd", "buf", "len") [writeS]
      Assert [Al len,
        PRE[V] buffer_splitAt (wordToNat (V "len")) (V "buf") len
          * [| (wordToNat (V "len") <= len)%nat |]
        POST[_] buffer_joinAt (wordToNat (V "len")) (V "buf") len];;

      Call "sys"!"write"("fd", "buf", "len")
      [PRE[_] Emp POST[_] Emp];;
      Return 0
    end with bfunctionNoRet "main"("fdl", "fd", "buf", "n") [mainS]
      "fdl" <-- Call "sys"!"listen"(8080%N)
      [PREonly[_] mallocHeap 0];;

      "fd" <-- Call "sys"!"accept"("fdl")
      [PREonly[_] mallocHeap 0];;

      "buf" <-- Call "malloc"!"malloc"(0, 10)
      [PREonly[_, R] R =?> 10];;

      Note [please_materialize_buffer 10];;

      "n" <-- Call "sys"!"read"("fd", "buf", 40)
      [PREonly[V] V "buf" =?>8 40];;

      [PREonly[V] V "buf" =?>8 40]
      While ("n" <> 0) {
        If ("n" <= 40) {
          Call "test"!"write"("fd", "buf", "n")
          [PREonly[V] V "buf" =?>8 40]
        } else {
          Skip
        };;

        "n" <-- Call "sys"!"read"("fd", "buf", 40)
        [PREonly[V] V "buf" =?>8 40]
      };;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition hints : TacPackage.
  prepare (materialize_buffer, buffer_split_tagged) buffer_join_tagged.
Defined.

Hint Extern 1 (@eq W _ _) => words.

Lemma le_40 : forall w : W,
  w <= natToW 40
  -> (wordToNat w <= 40)%nat.
  intros; pre_nomega.
  rewrite wordToNat_natToWord_idempotent in * by reflexivity; omega.
Qed.

Hint Immediate le_40.

Ltac t :=
  try match goal with
        | [ |- context[evalCond _ Le (RvImm (natToW 40)) _ _] ] =>
          post; evaluate hints; exists 40
      end;
  sep hints; auto.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
