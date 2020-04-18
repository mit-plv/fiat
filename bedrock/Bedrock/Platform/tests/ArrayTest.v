Require Import Coq.omega.Omega.
Require Import Coq.Arith.Arith Bedrock.Platform.AutoSep Bedrock.Platform.Malloc Bedrock.Platform.Arrays8.


Definition readS := SPEC("arr", "pos") reserving 0
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "pos" < $ (length arr) |]
  POST[R] array8 arr (V "arr") * [| R = BtoW (Array8.sel arr (V "pos")) |].

Definition writeS := SPEC("arr", "pos", "val") reserving 0
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "pos" < $ (length arr) |]
  POST[_] array8 (Array8.upd arr (V "pos") (WtoB (V "val"))) (V "arr").

Definition inc1 (b : B) : B := WtoB (BtoW b ^+ $1).
Definition inc := map inc1.

Definition incS := SPEC("arr", "len") reserving 2
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "len" = length arr |] * [| goodSize (length arr) |]
  POST[_] array8 (inc arr) (V "arr").

Definition sum ls := fold_left (fun n b => n ^+ BtoW b) ls $0.

Definition sumS := SPEC("arr", "len") reserving 3
  Al arr,
  PRE[V] array8 arr (V "arr") * [| V "len" = length arr |] * [| goodSize (length arr) |]
  POST[R] array8 arr (V "arr") * [| R = sum arr |].

Definition testS := SPEC reserving 9
  PREonly[_] mallocHeap 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "sys"!"abort" @ [abortS], "sys"!"printInt" @ [printIntS] ]]
  bmodule "array" {{
  bfunction "read"("arr", "pos") [readS]
    "arr" <-*8 "arr" + "pos";;
    Return "arr"
  end with bfunction "write"("arr", "pos", "val") [writeS]
    "arr" + "pos" *<-8 "val";;
    Return 0
  end with bfunction "inc"("arr", "len", "i", "tmp") [incS]
    "i" <- 0;;

    [Al arr,
      PRE[V] array8 arr (V "arr") * [| V "len" = length arr |] * [| goodSize (length arr) |]
        * [| (V "i" <= $ (length arr))%word |]
      POST[_] Ex arr', array8 arr' (V "arr") * [| length arr' = length arr |]
        * [| forall j, (j < wordToNat (V "i"))%nat -> Array8.selN arr' j = Array8.selN arr j |]
        * [| forall j, (j >= wordToNat (V "i"))%nat -> Array8.selN arr' j = inc1 (Array8.selN arr j) |] ]
    While ("i" < "len") {
      "tmp" <-*8 "arr" + "i";;
      "tmp" <- "tmp" + 1;;
      "arr" + "i" *<-8 "tmp";;
      "i" <- "i" + 1
    };;

    Return 0
  end with bfunction "sum"("arr", "len", "i", "acc", "tmp") [sumS]
    "i" <- 0;;
    "acc" <- 0;;

    [Al done, Al rem,
      PRE[V] array8 (done ++ rem) (V "arr") * [| V "len" = length (done ++ rem) |]
        * [| goodSize (length (done ++ rem)) |] * [| V "i" = length done |]
      POST[R] array8 (done ++ rem) (V "arr") * [| R = V "acc" ^+ sum rem |] ]
    While ("i" < "len") {
      "tmp" <-*8 "arr" + "i";;
      "acc" <- "acc" + "tmp";;
      "i" <- "i" + 1
    };;

    Return "acc"
  end with bfunctionNoRet "test"("arr", "tmp") [testS]
    "arr" <-- Call "malloc"!"malloc"(0, 2)
    [PREonly[_, R] mallocHeap 0 * R =?> 2 * [| R <> 0 |] * [| freeable R 2 |] ];;

    Note [please_materialize 2];;

    Assert [Al arr,
      PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
        * array8 arr (V "arr") * [| length arr = 8|] ];;

    "tmp" <- 0;;
    [Al arr,
      PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
        * array8 arr (V "arr") * [| length arr = 8 |] ]
    While ("tmp" < 8) {
      Assert [Al arr,
        PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
        * array8 arr (V "arr") * [| length arr = 8 |] * [| (V "tmp" < natToW (length arr))%word |] ];;

      "arr" + "tmp" *<-8 "tmp";;
      "tmp" <- "tmp" + 1
    };;

    Call "array"!"inc"("arr", 8)
    [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8 arr (V "arr") * [| length arr = 8 |] ];;

    "tmp" <-- Call "array"!"sum"("arr", 8)
    [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8 arr (V "arr") * [| length arr = 8 |] ];;

    Call "sys"!"printInt"("tmp")
    [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8 arr (V "arr") * [| length arr = 8 |] ];;

    Assert [Al arr, PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * array8_decomission 2 arr (V "arr") * [| decomission_ok 2 arr |] ];;

    Assert [PREonly[V] mallocHeap 0 * [| V "arr" <> 0 |] * [| freeable (V "arr") 2 |]
      * V "arr" =?> 2];;

    Call "malloc"!"free"(0, "arr", 2)
    [PREonly[_] Emp];;

    Call "sys"!"abort"()
    [PREonly[_] [| False |] ]
  end
}}.


Lemma inc_nil : inc nil = nil.
  auto.
Qed.

Hint Rewrite inc_nil app_nil_r : sepFormula.

Lemma determine_inc : forall arr arr',
  length arr' = length arr
  -> (forall j, Array8.selN arr' j = inc1 (Array8.selN arr j))
  -> arr' = inc arr.
  induction arr; destruct arr'; simpl; intuition; f_equal.
  apply (H0 O).
  apply IHarr; auto.
  intro j; apply (H0 (S j)).
Qed.

Hint Extern 1 (not (@eq nat _ _)) => omega.
Hint Extern 1 (_ < _) => congruence.

Lemma final_bound : forall (len i : W) len' j,
  goodSize len'
  -> len <= i
  -> len = natToW len'
  -> i <= natToW len'
  -> (j >= wordToNat i)%nat
  -> (j >= len')%nat.
  intros.
  assert (natToW len' = i) by eauto using squeeze.
  subst.
  rewrite wordToNat_natToWord_idempotent in H3; auto.
Qed.

Hint Resolve final_bound.

Lemma reveal_middle' : forall (ls1 ls2 : list B),
  (length ls1 < length (ls1 ++ ls2))%nat
  -> exists x, exists ls2', ls2 = x :: ls2'.
  intros; rewrite app_length in *.
  assert (length ls2 <> 0) by omega.
  destruct ls2; simpl in *; intuition eauto.
Qed.

Lemma reveal_middle : forall (ls1 ls2 : list B) i len,
  i < len
  -> i = natToW (length ls1)
  -> len = natToW (length (ls1 ++ ls2))
  -> goodSize (length (ls1 ++ ls2))
  -> exists x, exists ls2', ls2 = x :: ls2'.
  intros; subst.
  eapply reveal_middle'.
  instantiate (1 := ls1).
  rewrite app_length in *.
  pre_nomega.
  rewrite wordToNat_natToWord_idempotent in H.
  rewrite wordToNat_natToWord_idempotent in H; assumption.
  Transparent goodSize.
  red in H2.
  generalize dependent (Npow2 32); intros.
  nomega.
  Opaque goodSize.
Qed.

Hint Rewrite DepList.pf_list_simpl : sepFormula.

Lemma length_addendum : forall A (x : A) ls,
  length (ls ++ x :: nil) = length ls + 1.
  intros; rewrite app_length; auto.
Qed.

Hint Rewrite length_addendum : sepFormula.

Lemma sum_cons' : forall acc1 bs acc2,
  fold_left (fun n b => n ^+ BtoW b) bs (acc1 ^+ acc2) = acc1 ^+ fold_left (fun n b => n ^+ BtoW b) bs acc2.
  induction bs; simpl; intuition idtac.
  rewrite <- wplus_assoc.
  apply IHbs.
Qed.

Lemma sum_cons : forall b bs,
  sum (b :: bs) = BtoW b ^+ sum bs.
  unfold sum; simpl.
  intros.
  rewrite wplus_comm; apply sum_cons'.
Qed.

Hint Rewrite sum_cons : sepFormula.

Lemma selN_middle : forall post mid pre,
  Array8.selN (pre ++ mid :: post) (length pre) = mid.
  induction pre; simpl; intuition.
Qed.

Lemma sel_middle : forall i pre mid post,
  i = natToW (length pre)
  -> goodSize (length pre)
  -> Array8.sel (pre ++ mid :: post) i = mid.
  unfold Array8.sel; intros; subst.
  autorewrite with N.
  apply selN_middle.
Qed.

Hint Rewrite sel_middle using solve [ eauto 1 ] : sepFormula.

Lemma goodSize_split : forall A (ls1 ls2 : list A),
  goodSize (length (ls1 ++ ls2))
  -> goodSize (length ls1).
  intros; rewrite app_length in *; eapply goodSize_weaken; eauto.
Qed.

Hint Immediate goodSize_split.

Lemma all_done : forall len i A (done rem : list A),
  len <= i
  -> len = natToW (length (done ++ rem))
  -> i = natToW (length done)
  -> goodSize (length (done ++ rem))
  -> rem = nil.
  intros; subst.
  rewrite app_length in *.
  pre_nomega.
  assert (goodSize (length done)); eauto.
  rewrite wordToNat_natToWord_idempotent in *; eauto.
  rewrite wordToNat_natToWord_idempotent in *; eauto.
  destruct rem; simpl in *; auto; omega.
Qed.

Lemma sum_nil : sum nil = $0.
  auto.
Qed.

Hint Rewrite sum_nil : sepFormula.

Lemma length_inc : forall ls, length (inc ls) = length ls.
  intros; apply map_length.
Qed.

Hint Rewrite length_inc : sepFormula.

Lemma goodSize8 : forall n, n = 8
  -> goodSize n.
  intros; subst; auto.
Qed.

Hint Immediate goodSize8.

Opaque array8 allocated.

Definition hints : TacPackage.
  prepare (materialize_array8_tagged, decomission_array8_tagged) tt.
Defined.

Ltac useHyp := match goal with
                 | [ H : forall j : nat, _ |- _ ] => rewrite H by omega
               end.

Ltac finish :=
  match goal with
    | [ |- _ ^+ _ <= _ ] => eauto
    | [ |- sel _ "len" = natToW (length (?X ++ _))%nat ] => equate X (@nil B); simpl;
      eauto; reflexivity || words
    | [ |- himp _ (array8 ?A _) (array8 ?B _) ] =>
      replace B with A by eauto using determine_inc; reflexivity
    | [ H : sel _ "i" = _ |- _ ^+ natToW 1 = natToW (length _ + 1) ] => solve [ rewrite H; descend ]
    | [ _ : goodSize (length (_ ++ ?X)) |- _ ] => assert (X = nil) by eauto using all_done; subst;
      autorewrite with sepFormula; words
    | _ => solve [ useHyp; auto ]
    | _ => solve [ rewrite selN_oob; eauto ]
    | [ H : (?N >= ?M)%nat |- _ ] => destruct (eq_nat_dec N M); subst;
      useHyp; auto; rewrite selN_upd_ne; auto
    | _ => eauto; reflexivity || words
  end.

Ltac t := solve [
  try match goal with
        | [ |- forall stn_st specs, interp _ _ -> interp _ _ ] =>
          match goal with
            | [ |- context[LvMem8] ] => post; evaluate auto_ext;
              match goal with
                | [ H : goodSize (length (?done ++ _)) |- _ ] =>
                  let Ho := fresh in
                    generalize H; intro Ho; eapply reveal_middle in Ho; eauto; destruct Ho as [ mid [ rem ] ]; subst;
                      exists (done ++ mid :: nil); exists rem
              end
          end
      end; sep hints; finish ].

Theorem ok : moduleOk m.
  vcgen; abstract t.
Qed.
