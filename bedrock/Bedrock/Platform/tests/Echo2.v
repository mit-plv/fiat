Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.


Definition mainS := SPEC reserving 16
  PREonly[_] mallocHeap 0.

Definition writeS := SPEC("fd", "buf", "len") reserving 4
  Al len,
  PRE[V] V "buf" =?>8 len * [| (wordToNat (V "len") <= len)%nat |]
  POST[_] V "buf" =?>8 len.

Opaque allocated.

Definition neg1 : W := wones _.

Definition m := bimport [[ "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS],
                           "sys"!"listen" @ [listenS], "sys"!"accept" @ [acceptS],
                           "sys"!"read" @ [readS], "sys"!"write" @ [Sys.writeS],
                           "sys"!"declare" @ [declareS], "sys"!"wait" @ [Sys.waitS],
                           "sys"!"close" @ [closeS], "malloc"!"malloc" @ [mallocS] ]]
  bmodule "test" {{
    bfunction "write"("fd", "buf", "len") [writeS]
      Assert [Al len,
        PRE[V] buffer_splitAt (wordToNat (V "len")) (V "buf") len
          * [| (wordToNat (V "len") <= len)%nat |]
        POST[_] buffer_joinAt (wordToNat (V "len")) (V "buf") len];;

      Call "sys"!"write"("fd", "buf", "len")
      [PRE[_] Emp POST[_] Emp];;
      Return 0
    end with bfunctionNoRet "main"("fdl", "fd1", "fd2", "ind1", "ind2", "fd", "buf", "n") [mainS]
      "fdl" <-- Call "sys"!"listen"(8080%N)
      [PREonly[_] mallocHeap 0];;

      "fd1" <-- Call "sys"!"accept"("fdl")
      [PREonly[_] mallocHeap 0];;

      "fd2" <-- Call "sys"!"accept"("fdl")
      [PREonly[_] mallocHeap 0];;

      "buf" <-- Call "malloc"!"malloc"(0, 10)
      [PREonly[_, R] R =?> 10];;

      Note [please_materialize_buffer 10];;

      "ind1" <-- Call "sys"!"declare"("fd1", 0)
      [PREonly[V] V "buf" =?>8 40];;

      "ind2" <-- Call "sys"!"declare"("fd2", 0)
      [PREonly[V] V "buf" =?>8 40];;

      "n" <-- Call "sys"!"wait"(1)
      [PREonly[V] V "buf" =?>8 40];;

      [PREonly[V] V "buf" =?>8 40]
      While ("n" <> neg1) {
        If ("n" = "ind1") {
          "fd" <- "fd1"
        } else {
          "fd" <- "fd2"
        };;

        "n" <-- Call "sys"!"read"("fd", "buf", 40)
        [PREonly[V] V "buf" =?>8 40];;

        If ("n" = 0) {
          Call "sys"!"close"("fd")
          [PREonly[V] V "buf" =?>8 40]
        } else {
          If ("fd" = "fd1") {
            "ind1" <-- Call "sys"!"declare"("fd1", 0)
            [PREonly[V] V "buf" =?>8 40]
          } else {
            "ind2" <-- Call "sys"!"declare"("fd2", 0)
            [PREonly[V] V "buf" =?>8 40]
          };;

          If ("n" <= 40) {
            Call "test"!"write"("fd", "buf", "n")
            [PREonly[V] V "buf" =?>8 40]
          } else {
            Skip
          }
        };;

        "n" <-- Call "sys"!"wait"(1)
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
