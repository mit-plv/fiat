Require Import Bedrock.Platform.AutoSep Bedrock.Platform.Arrays8.


Definition copyS := SPEC("dst", "dstPos", "src", "srcPos", "len") reserving 1
  Al bsD, Al bsS, Al lenD : W, Al lenS : W,
  PRE[V] array8 bsD (V "dst") * array8 bsS (V "src")
    * [| wordToNat (V "dstPos") + wordToNat (V "len") <= length bsD |]%nat
    * [| wordToNat (V "srcPos") + wordToNat (V "len") <= length bsS |]%nat
    * [| length bsD = wordToNat lenD |] * [| length bsS = wordToNat lenS |]
  POST[_] Ex bsD', array8 bsD' (V "dst") * array8 bsS (V "src")
    * [| length bsD' = length bsD |].

Definition equalS := SPEC("arr1", "pos1", "arr2", "pos2", "len") reserving 2
  Al bs1, Al bs2, Al len1 : W, Al len2 : W,
  PRE[V] array8 bs1 (V "arr1") * array8 bs2 (V "arr2")
    * [| wordToNat (V "pos1") + wordToNat (V "len") <= length bs1 |]%nat
    * [| wordToNat (V "pos2") + wordToNat (V "len") <= length bs2 |]%nat
    * [| length bs1 = wordToNat len1 |] * [| length bs2 = wordToNat len2 |]
  POST[_] array8 bs1 (V "arr1") * array8 bs2 (V "arr2").

Definition m := bmodule "array8" {{
  bfunction "copy"("dst", "dstPos", "src", "srcPos", "len", "tmp") [copyS]
    [Al bsD, Al bsS, Al lenD : W, Al lenS : W,
      PRE[V] array8 bsD (V "dst") * array8 bsS (V "src")
        * [| wordToNat (V "dstPos") + wordToNat (V "len") <= length bsD |]%nat
        * [| wordToNat (V "srcPos") + wordToNat (V "len") <= length bsS |]%nat
        * [| length bsD = wordToNat lenD |] * [| length bsS = wordToNat lenS |]
      POST[_] Ex bsD', array8 bsD' (V "dst") * array8 bsS (V "src")
        * [| length bsD' = length bsD |] ]
    While ("len" > 0) {
      Assert [Al bsD, Al bsS, Al lenD : W, Al lenS : W,
        PRE[V] [| V "len" > natToW 0 |]%word * [| V "srcPos" < natToW (length bsS) |]%word
          * [| V "dstPos" < natToW (length bsD) |]%word
          * array8 bsD (V "dst") * array8 bsS (V "src")
          * [| wordToNat (V "dstPos") + wordToNat (V "len") <= length bsD |]%nat
          * [| wordToNat (V "srcPos") + wordToNat (V "len") <= length bsS |]%nat
          * [| length bsD = wordToNat lenD |] * [| length bsS = wordToNat lenS |]
        POST[_] Ex bsD', array8 bsD' (V "dst") * array8 bsS (V "src")
          * [| length bsD' = length bsD |] ];;

      "tmp" <-*8 "src" + "srcPos";;
      "dst" + "dstPos" *<-8 "tmp";;
      "dstPos" <- "dstPos" + 1;;
      "srcPos" <- "srcPos" + 1;;
      "len" <- "len" - 1
    };;

    Return 0
  end with bfunction "equal"("arr1", "pos1", "arr2", "pos2", "len", "tmp1", "tmp2") [equalS]
    [Al bs1, Al bs2, Al len1 : W, Al len2 : W,
      PRE[V] array8 bs1 (V "arr1") * array8 bs2 (V "arr2")
        * [| wordToNat (V "pos1") + wordToNat (V "len") <= length bs1 |]%nat
        * [| wordToNat (V "pos2") + wordToNat (V "len") <= length bs2 |]%nat
        * [| length bs1 = wordToNat len1 |] * [| length bs2 = wordToNat len2 |]
      POST[_] array8 bs1 (V "arr1") * array8 bs2 (V "arr2") ]
    While ("len" > 0) {
      Assert [Al bs1, Al bs2, Al len1 : W, Al len2 : W,
        PRE[V] [| V "len" > natToW 0 |]%word * [| V "pos1" < natToW (length bs1) |]%word
          * [| V "pos2" < natToW (length bs2) |]%word
          * array8 bs1 (V "arr1") * array8 bs2 (V "arr2")
          * [| wordToNat (V "pos1") + wordToNat (V "len") <= length bs1 |]%nat
          * [| wordToNat (V "pos2") + wordToNat (V "len") <= length bs2 |]%nat
          * [| length bs1 = wordToNat len1 |] * [| length bs2 = wordToNat len2 |]
        POST[_] array8 bs1 (V "arr1") * array8 bs2 (V "arr2") ];;

      "tmp1" <-*8 "arr1" + "pos1";;
      "tmp2" <-*8 "arr2" + "pos2";;
      If ("tmp1" = "tmp2") {
        "pos1" <- "pos1" + 1;;
        "pos2" <- "pos2" + 1;;
        "len" <- "len" - 1
      } else {
        Return 0
      }
    };;

    Return 1
  end
}}.

Lemma rt1 : wordToNat (natToW 1) = 1.
  reflexivity.
Qed.

Hint Rewrite rt1 : N.

Lemma updown : forall (x : W) y,
  natToW 0 < x
  -> y + 1 + wordToNat (x ^- natToW 1) = y + wordToNat x.
  intros; rewrite wordToNat_wminus; nomega.
Qed.

Hint Rewrite updown using assumption : sepFormula.

Lemma natToW_wordToNat : forall w : W, natToW (wordToNat w) = w.
  apply natToWord_wordToNat.
Qed.

Hint Rewrite natToW_wordToNat : N.

Lemma goodBound : forall (x y u : W) n,
  (wordToNat x + wordToNat y <= n)%nat
  -> natToW 0 < y
  -> n = wordToNat u
  -> x < natToW n.
  intros; subst; nomega.
Qed.

Local Hint Immediate goodBound.

Theorem ok : moduleOk m.
  vcgen; abstract (sep_auto; (descend; eauto)).
Qed.
