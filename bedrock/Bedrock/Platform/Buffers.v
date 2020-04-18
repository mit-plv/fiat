Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Arrays8 Bedrock.Platform.MoreArrays.


Definition bmallocS : spec := SPEC("n") reserving 8
  PRE[V] [| V "n" >= $2 |] * mallocHeap 0
  POST[R] [| R <> 0 |] * [| freeable R (wordToNat (V "n")) |]
    * R =?>8 (wordToNat (V "n") * 4) * mallocHeap 0.

Definition bfreeS : spec := SPEC("p", "n") reserving 6
  PRE[V] [| V "p" <> 0 |] * [| freeable (V "p") (wordToNat (V "n")) |]
    * V "p" =?>8 (wordToNat (V "n") * 4) * mallocHeap 0
  POST[_] mallocHeap 0.

Definition containsS : spec := SPEC("haystack", "len", "needle") reserving 2
  PRE[V] V "haystack" =?>8 wordToNat (V "len")
  POST[_] V "haystack" =?>8 wordToNat (V "len").

Definition copyS : spec := SPEC("dst", "src", "srcLen") reserving 2
  Al dstLen,
  PRE[V] V "dst" =?>8 wordToNat dstLen * V "src" =?>8 wordToNat (V "srcLen") * [| V "srcLen" <= dstLen |]
  POST[_] V "dst" =?>8 wordToNat dstLen * V "src" =?>8 wordToNat (V "srcLen").

Inductive debufferize : Prop := Debufferize.
Hint Constructors debufferize.

Definition neg1 : W := wones _.

Definition m := bimport [[ "sys"!"abort" @ [abortS],
                           "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "buffers" {{
    bfunction "bmalloc"("n", "r") [bmallocS]
      "r" <-- Call "malloc"!"malloc"(0, "n")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "r"
    end with bfunction "bfree"("p", "n") [bfreeS]
      Assert [PRE[V] [| V "p" <> 0 |] * [| freeable (V "p") (wordToNat (V "n")) |]
        * V "p" =?> wordToNat (V "n") * mallocHeap 0
        POST[_] mallocHeap 0];;

      Call "malloc"!"free"(0, "p", "n")
      [PRE[_] Emp
       POST[_] Emp ];;
      Return 0
    end with bfunction "contains"("haystack", "len", "needle", "i", "tmp") [containsS]
      Note [debufferize];;

      Assert [Al bs, PRE[V] array8 bs (V "haystack") * [| length bs = wordToNat (V "len") |]
        POST[_] array8 bs (V "haystack")];;

      "i" <- 0;;

      [Al bs, PRE[V] array8 bs (V "haystack") * [| length bs = wordToNat (V "len") |]
        POST[_] array8 bs (V "haystack")]
      While ("i" < "len") {
        Assert [Al bs, PRE[V] array8 bs (V "haystack") * [| length bs = wordToNat (V "len") |]
          * [| (V "i" < natToW (length bs))%word |]
          POST[_] array8 bs (V "haystack")];;

        "tmp" <-*8 "haystack" + "i";;
        If ("tmp" = "needle") {
          Return "i"
        } else {
          "i" <- "i" + 1
        }
      };;

      Return neg1
    end with bfunction "copy"("dst", "src", "srcLen", "i", "tmp") [copyS]
      Note [debufferize];;

      Assert [Al src, Al dst,
        PRE[V] array8 dst (V "dst") * array8 src (V "src")
          * [| length src = wordToNat (V "srcLen") |] * [| (wordToNat (V "srcLen") <= length dst)%nat |]
          * [| goodSize (length dst) |]
        POST[_] Ex dst', array8 dst' (V "dst") * array8 src (V "src")
          * [| length dst' = length dst |] ];;

      "i" <- 0;;

      [Al src, Al dst,
        PRE[V] array8 dst (V "dst") * array8 src (V "src") * [| (wordToNat (V "srcLen") <= length dst)%nat |]
          * [| length src = wordToNat (V "srcLen") |]
          * [| goodSize (length dst) |]
        POST[_] Ex dst', array8 dst' (V "dst") * array8 src (V "src")
          * [| length dst' = length dst |] ]
      While ("i" < "srcLen") {
        Assert [Al src, Al dst,
          PRE[V] array8 dst (V "dst") * array8 src (V "src") * [| (wordToNat (V "srcLen") <= length dst)%nat |]
            * [| length src = wordToNat (V "srcLen") |] * [| goodSize (length dst) |]
            * [| (V "i" < natToW (length dst))%word |] * [| (V "i" < natToW (length src))%word |]
          POST[_] Ex dst', array8 dst' (V "dst") * array8 src (V "src")
            * [| length dst' = length dst |] ];;

        "tmp" <-*8 "src" + "i";;
        "dst" + "i" *<-8 "tmp";;
        "i" <- "i" + 1
      };;

      Return 0
    end
  }}.

Theorem dematerialize_buffer : forall p n, p =?>8 (n * 4) ===> p =?> n.
  unfold buffer; sepLemma; apply decomission_array8; auto.
Qed.

Ltac finish :=
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
         end; try apply materialize_array8;
  try (etransitivity; [ apply himp_star_comm | apply himp_star_frame; reflexivity || apply dematerialize_buffer ]);
    try rewrite natToW_wordToNat; try rewrite length_upd; auto; try nomega.

Ltac t :=
  try match goal with
        | [ |- context[debufferize] ] => unfold buffer
      end; sep_auto; finish.

Local Hint Extern 1 (@eq W _ _) => words.

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
