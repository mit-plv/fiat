Require Import Coq.omega.Omega.
Require Import Bedrock.Examples.AutoSep.
Require Import Coq.Arith.Arith Coq.Lists.List.

Set Implicit Arguments.

Local Hint Extern 1 (himp _ (allocated _ _ _) (allocated _ _ _)) => apply allocated_shift_base.

Lemma wplus_lt_lift : forall n m o : nat,
  goodSize (n + m)
  -> goodSize o
  -> natToW n ^+ natToW m < natToW o
  -> (n + m < o)%nat.
  unfold wlt; intros.
  rewrite <- natToWord_plus in H1.
  unfold wplusN, wordBinN in *.
  repeat rewrite wordToN_nat in *.
  repeat rewrite wordToNat_natToW_goodSize in * by auto.
  nomega.
Qed.

Local Hint Extern 1 (_ <= _)%nat => match goal with
                                      | [ H : _ < _ |- _ ] =>
                                        apply wplus_lt_lift in H;
                                          [ omega | solve [ eauto ] | solve [ eauto ] ]
                                    end.

Lemma goodSize_plus2 : forall n,
  goodSize (n + 2)
  -> goodSize n.
  intros; eapply goodSize_plus_l; eauto.
Qed.

Lemma goodSize_diff : forall x y,
  goodSize (x + 2)
  -> goodSize (x - y - 2 + 2).
  intros; eapply goodSize_weaken; eauto.
Qed.

Local Hint Resolve goodSize_plus2 goodSize_diff.


(** * A free-list heap managed by the malloc library *)

Module Type FREE_LIST.
  Parameter freeable : W -> nat -> Prop.

  Axiom goodSize_freeable : forall p sz,
    freeable p sz
    -> goodSize sz.

  Axiom freeable_narrow : forall a sz sz',
    freeable a sz
    -> (sz' <= sz)%nat
    -> freeable a sz'.

  Axiom freeable_split : forall a b x y,
    freeable a (x + 2)
    -> natToW (y + 2) < natToW x
    -> goodSize (y + 2)
    -> b = a ^+ $4 ^* (natToW x ^- natToW y)
    -> freeable b (y + 2).

  Axiom it's_not_zero : forall x y a b,
    x = y ^+ $4 ^* ($ (a) ^- natToW b)
    -> freeable y (a + 2)
    -> natToW (b + 2) < natToW a
    -> goodSize (b + 2)
    -> x <> $0.

  Parameter freeList : nat (* number of elements in list *) -> W -> HProp.
  Parameter mallocHeap : HProp.

  Axiom freeList_extensional : forall n p, HProp_extensional (freeList n p).
  Axiom mallocHeap_extensional : HProp_extensional mallocHeap.

  Axiom mallocHeap_fwd : mallocHeap ===> Ex n, Ex p, 0 =*> p * freeList n p.
  Axiom mallocHeap_bwd : (Ex n, Ex p, 0 =*> p * freeList n p) ===> mallocHeap.

  Axiom nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
  Axiom cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $ (sz), p')
      * (p ^+ $8) =?> sz * freeList n' p')
    ===> freeList n p.

  Axiom cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $ (sz), p')
    * (p ^+ $8) =?> sz * freeList n' p'.
End FREE_LIST.

Module FreeList : FREE_LIST.
  Transparent goodSize.

  Definition noWrapAround (p : W) (sz : nat) :=
    forall n, (n < sz * 4)%nat -> p ^+ $ (n) <> $0.

  Definition freeable (p : W) (sz : nat) := goodSize sz /\ noWrapAround p sz.

  Lemma goodSize_narrow : forall sz sz' q,
    (N.of_nat sz < q)%N
    -> (sz' <= sz)%nat
    -> (N.of_nat sz' < q)%N.
    intros; nomega.
  Qed.

  Lemma freeable_narrow : forall a sz sz',
    freeable a sz
    -> (sz' <= sz)%nat
    -> freeable a sz'.
    unfold freeable; intuition eauto.
    eapply goodSize_narrow; eauto.

    do 2 intro.
    apply H2.
    omega.
  Qed.

  Lemma goodSize_freeable : forall p sz,
    freeable p sz
    -> goodSize sz.
    unfold freeable; tauto.
  Qed.

  Lemma it's_not_zero : forall x y a b,
    x = y ^+ $4 ^* ($ (a) ^- natToW b)
    -> freeable y (a + 2)
    -> natToW (b + 2) < natToW a
    -> goodSize (b + 2)
    -> x <> $0.
    intros.
    destruct H0.
    intro.
    apply (H3 (4 * (a - b))).
    auto.
    rewrite mult_comm.
    rewrite natToW_times4.
    rewrite natToW_minus.
    rewrite wmult_comm.
    subst; assumption.
    apply lt_goodSize' in H1; auto.
  Qed.

  Hint Extern 1 (_ < _)%N => apply goodSize_plus2.

  Lemma freeable_split : forall a b x y,
    freeable a (x + 2)
    -> natToW (y + 2) < natToW x
    -> goodSize (y + 2)
    -> b = a ^+ $4 ^* (natToW x ^- natToW y)
    -> freeable b (y + 2).
    intros; rewrite natToW_plus in *.
    destruct H; split; auto; subst.
    do 2 intro.
    specialize (H3 (4 * (x - y) + n)).
    intro.
    apply H3.
    auto.
    rewrite natToW_plus.
    rewrite mult_comm.
    rewrite natToW_times4.
    rewrite natToW_minus.
    rewrite wmult_comm.
    rewrite wplus_assoc.
    assumption.
    auto.
  Qed.

  Open Scope Sep_scope.

  Fixpoint freeList (n : nat) (p : W) : HProp :=
    match n with
      | O => [| p = 0 |]
      | S n' => [| p <> 0 |] * Ex sz, Ex p', [| freeable p (sz+2) |] * (p ==*> $ (sz), p')
        * (p ^+ $8) =?> sz * freeList n' p'
    end.

  Definition mallocHeap := Ex n, Ex p, 0 =*> p * freeList n p.

  Theorem freeList_extensional : forall n p, HProp_extensional (freeList n p).
    destruct n; reflexivity.
  Qed.

  Theorem mallocHeap_extensional : HProp_extensional mallocHeap.
    reflexivity.
  Qed.

  Theorem mallocHeap_fwd : mallocHeap ===> Ex n, Ex p, 0 =*> p * freeList n p.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem mallocHeap_bwd : (Ex n, Ex p, 0 =*> p * freeList n p) ===> mallocHeap.
    unfold mallocHeap; sepLemma.
  Qed.

  Theorem nil_bwd : forall n p, p = 0 -> [| n = 0 |] ===> freeList n p.
    destruct n; sepLemma.
  Qed.

  Theorem cons_bwd : forall n (p : W), p <> 0
    -> (Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $ (sz), p')
      * (p ^+ $8) =?> sz * freeList n' p')
    ===> freeList n p.
    destruct n; sepLemma; match goal with
                            | [ H : S _ = S _ |- _ ] => injection H
                          end; sepLemma.
  Qed.

  Theorem cons_fwd : forall n (p : W), p <> 0
    -> freeList n p
    ===> Ex n', Ex sz, Ex p', [| n = S n' /\ freeable p (sz+2) |] * (p ==*> $ (sz), p')
    * (p ^+ $8) =?> sz * freeList n' p'.
    destruct n; sepLemma.
  Qed.
End FreeList.

Import FreeList.
Export FreeList.
Hint Immediate freeList_extensional mallocHeap_extensional.

Definition splitMe cur full (_ : nat) := (cur =?> full)%Sep.

Local Hint Resolve goodSize_freeable.

Lemma malloc_split : forall cur full init,
  (init <= full)%nat
  -> splitMe cur full init ===> cur =?> init
  * (cur ^+ $ (init * 4)) =?> (full - init).
  intros; eapply Himp_trans; [
    eapply allocated_split; eauto
    | sepLemma; apply allocated_shift_base; [
      rewrite mult_comm; simpl; unfold natToW; W_eq
      | reflexivity ] ].
Qed.

(*TIME Clear Timing Profile. *)

Definition hints : TacPackage.
(*TIME idtac "malloc:prepare". Time *)
  prepare (mallocHeap_fwd, cons_fwd, malloc_split) (mallocHeap_bwd, nil_bwd, cons_bwd).
(*TIME Time *)Defined.

Definition initS : spec := SPEC("size") reserving 0
  Al n,
  PRE[V] [| V("size") = $ (n) |] * [| freeable 4 (n+2) |] * 0 =?> (3 + n)
  POST[_] mallocHeap.

Definition freeS : spec := SPEC("p", "n") reserving 1
  Al n,
  PRE[V] [| V "n" = $ (n) |] * [| V "p" <> 0 |] * [| freeable (V "p") (n+2) |] * V "p" =?> (2 + n) * mallocHeap
  POST[_] mallocHeap.

Definition mallocS : spec := SPEC("n") reserving 4
  Al sz,
  PRE[V] [| V "n" = $ (sz) |] * [| goodSize (sz+2) |] * mallocHeap
  POST[R] [| R <> 0 |] * [| freeable R (sz+2) |] * R =?> (sz + 2) * mallocHeap.

Definition mallocM := bmodule "malloc" {{
  bfunction "init"("size") [initS]
    0 *<- 4;;
    4 *<- "size";;
    8 *<- 0;;
    Return 0
  end with bfunction "free"("p", "n", "tmp") [freeS]
    "p" *<- "n";;
    "tmp" <-* 0;;
    0 *<- "p";;
    "p" <- "p" + 4;;
    "p" *<- "tmp";;
    Return 0
  end with bfunction "malloc"("n", "cur", "prev", "tmp", "tmp2") [mallocS]
    "cur" <-* 0;;
    "prev" <- 0;;

    [Al sz, Al len,
      PRE[V] [| V "n" = $ (sz) |] * [| goodSize (sz+2) |] * V "prev" =*> V "cur" * freeList len (V "cur")
      POST[R] Ex p, Ex len', [| R <> 0 |] * [| freeable R (sz+2) |] * R =?> (sz + 2)
        * V "prev" =*> p * freeList len' p]
    While ("cur" <> 0) {
      "tmp" <-* "cur";;
      If ("tmp" = "n") {
        (* Exact size match on the current free list block *)
        "tmp" <- "cur" + 4;;
        "tmp" <-* "tmp";;
        "prev" *<- "tmp";;
        Return "cur"
      } else {
        "tmp" <- "n" + 2;;
        "tmp2" <-* "cur";;
        If ("tmp" < "tmp2") {
          (* This free list block is large enough to split in two. *)

          (* Calculate starting address of a suffix of this free block to return to caller. *)
          "tmp" <- "tmp2" - "n";;
          "tmp" <- 4 * "tmp";;
          "tmp" <- "cur" + "tmp";;

          (* Decrement size of free list block to reflect deleted suffix. *)
          "tmp2" <- "tmp2" - "n";;
          "tmp2" <- "tmp2" - 2;;
          "cur" *<- "tmp2";;

          (* Return suffix starting address. *)
          Return "tmp"
        } else {
          (* Current block too small; continue to next. *)
          "prev" <- "cur" + 4;;
          "cur" <-* "prev"
        }
      }
    };;

    Diverge (* out of memory! *)
  end
}}.

Lemma four_neq_zero : natToW 4 <> natToW 0.
  discriminate.
Qed.

Lemma cancel8 : forall x y z,
  (z + 2 <= y)%nat
  -> x ^+ $8 ^+ ($ (y) ^- $ (z + 2)) ^* $4 = x ^+ $4 ^* ($ (y) ^- natToW z).
  intros.
  autorewrite with sepFormula.
  rewrite natToW_plus.
  unfold natToW.
  W_eq.
Qed.

Local Hint Extern 1 False => eapply it's_not_zero; eassumption.
Local Hint Extern 1 (freeable _ _) => eapply freeable_narrow; [ eassumption | omega ].
Local Hint Extern 1 (freeable _ _) => eapply freeable_split; eassumption.

Local Hint Extern 1 (@eq (word _) _ _) => words.
Local Hint Extern 5 (@eq nat _ _) => omega.
Local Hint Extern 5 (_ <= _)%nat => omega.

Section mallocOk.
  Hint Rewrite natToW_times4 cancel8 natToW_minus using solve [ auto ] : sepFormula.

  Ltac main := generalize four_neq_zero; sep hints;
    try match goal with
          | [ H1 : _ = ?X, H2 : ?X = _ |- _ ] =>
            rewrite H2 in H1;
              apply natToW_inj in H1; [ | solve [ eauto ] | solve [ eauto ] ];
                subst
        end; congruence || eauto; try rewrite <- (plus_comm 2);
    simpl; cancel hints.

  Ltac split_case := post; evaluate hints;
    match goal with
      | [ H : sel _ _ = natToW _ |- _ ] => rewrite H in *
    end;
    match goal with
      | [ _ : natToW ?init ^+ natToW 2 < natToW ?full,
        H : context[((?base ^+ natToW 8) =?> ?full)%Sep],
        H' : freeable _ (?full + 2) |- _ ] =>
      change ((base ^+ natToW 8) =?> full)%Sep
      with (splitMe (base ^+ natToW 8) full (full - init - 2)) in H;
        assert (full - init - 2 <= full)%nat by omega
    end; sep hints;
    try match goal with
          | [ H : natToW (?a + ?b) < natToW ?c |- _ ] =>
            rewrite natToW_plus in H;
              apply wplus_lt_lift in H; [ | solve [ eauto ] | solve [ eauto ] ]
        end; sep hints; auto.

  Ltac combined :=
    match goal with
      | [ |- context[Times] ] =>
        match goal with
          | [ |- context[Logic.ex _] ] => split_case
        end
      | _ => main
    end.

  Theorem mallocMOk : moduleOk mallocM.
(*TIME idtac "malloc:verify". Time *)
    vcgen; abstract combined.
(*TIME Time *)Qed.

(*TIME Print Timing Profile. *)
End mallocOk.
