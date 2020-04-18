Require Import Coq.Sets.Ensembles Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Facade.examples.TupleF Bedrock.Platform.MoreArrays.


Module Type ADT.
  Parameter tuple : list W -> W -> HProp.

  Axiom tuple_fwd : forall ls c, tuple ls c ===> [| c <> 0 |] * [| freeable c (length ls) |] * array ls c.
  Axiom tuple_bwd : forall ls (c : W), [| c <> 0 |] * [| freeable c (length ls) |] * array ls c ===> tuple ls c.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Definition tuple (ls : list W) (c : W) : HProp := [| c <> 0 |] * [| freeable c (length ls) |] * array ls c.

  Theorem tuple_fwd : forall ls c, tuple ls c ===> [| c <> 0 |] * [| freeable c (length ls) |] * array ls c.
  Proof.
    unfold tuple; sepLemma.
  Qed.

  Theorem tuple_bwd : forall ls (c : W), [| c <> 0 |] * [| freeable c (length ls) |] * array ls c ===> tuple ls c.
  Proof.
    unfold tuple; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Definition hints : TacPackage.
  prepare (tuple_fwd, allocate_array) (tuple_bwd, free_array).
Defined.

Definition newS := newS tuple 7.
Definition deleteS := deleteS tuple 6.
Definition copyS := copyS tuple 11.
Definition getS := getS tuple 0.
Definition setS := setS tuple 0.

Definition agreeUpto (ls1 ls2 : list W) (pos : nat) :=
  forall i, (i < pos)%nat -> Array.selN ls1 i = Array.selN ls2 i.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ArrayTuple" {{
    bfunction "new"("extra_stack", "len") [newS]
      "len" <-- Call "malloc"!"malloc"(0, "len")
      [PRE[V, R] R =?> wordToNat (V "len") * [| R <> 0 |] * [| freeable R (wordToNat (V "len")) |]
       POST[R'] Ex ls, tuple ls R' * [| length ls = wordToNat (V "len") |]];;

      Note [make_array];;
      Return "len"
    end

    with bfunction "delete"("extra_stack", "self", "len") [deleteS]
      Note [dissolve_array];;

      Call "malloc"!"free"(0, "self", "len")
      [PRE[_] Emp
       POST[R] [| R = $0 |] ];;

      Return 0
    end

    with bfunction "copy"("extra_stack", "self", "len", "copy", "i", "tmp", "tmp2") [copyS]
      "copy" <-- Call "malloc"!"malloc"(0, "len")
      [Al ls,
       PRE[V, R] tuple ls (V "self") * [| length ls = wordToNat (V "len") |]
         * R =?> wordToNat (V "len") * [| R <> 0 |] * [| freeable R (wordToNat (V "len")) |]
       POST[R'] tuple ls (V "self") * tuple ls R'];;

      Note [make_array];;
      "i" <- 0;;
      [Al ls1, Al ls2,
       PRE[V] tuple ls1 (V "self") * tuple ls2 (V "copy") * [| agreeUpto ls1 ls2 (wordToNat (V "i")) |]
         * [| length ls1 = wordToNat (V "len") |] * [| length ls2 = wordToNat (V "len") |]
       POST[R] [| R = V "copy" |] * tuple ls1 (V "self") * tuple ls1 (V "copy")]
      While ("i" < "len") {
        Assert [Al ls1, Al ls2,
                PRE[V] tuple ls1 (V "self") * tuple ls2 (V "copy") * [| agreeUpto ls1 ls2 (wordToNat (V "i")) |]
                  * [| length ls1 = wordToNat (V "len") |] * [| length ls2 = wordToNat (V "len") |]
                  * [| (V "i" < natToW (length ls1))%word |] * [| (V "i" < natToW (length ls2))%word |]
                POST[R] [| R = V "copy" |] * tuple ls1 (V "copy") * tuple ls1 (V "self")];;

        "tmp" <- 4 * "i";;
        "tmp2" <-* "self" + "tmp";;
        "copy" + "tmp" *<- "tmp2";;
        "i" <- "i" + 1
      };;

      Return "copy"
    end

    with bfunction "get"("extra_stack", "self", "pos") [getS]
      "pos" <- 4 * "pos";;
      "pos" <-* "self" + "pos";;
      Return "pos"
    end

    with bfunction "set"("extra_stack", "self", "pos", "val") [setS]
      "pos" <- 4 * "pos";;
      "self" + "pos" *<- "val";;
      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma agreeUpto_O : forall ls1 ls2, agreeUpto ls1 ls2 0.
Proof.
  unfold agreeUpto; intros; omega.
Qed.

Hint Resolve agreeUpto_O.

Lemma freeable_cong : forall p n n',
  freeable p n'
  -> n = n'
  -> freeable p n.
Proof.
  congruence.
Qed.

Hint Immediate freeable_cong.

Lemma selN_updN_ne : forall v a n n',
  n <> n'
  -> Array.selN (Array.updN a n v) n' = Array.selN a n'.
Proof.
  induction a; destruct n, n'; simpl; intuition.
Qed.

Lemma agreeUpto_S : forall ls1 ls2 n,
  agreeUpto ls1 ls2 (wordToNat n)
  -> n < natToW (length ls2)
  -> goodSize (length ls2)
  -> agreeUpto ls1 (Array.upd ls2 n (Array.sel ls1 n)) (wordToNat (n ^+ $1)).
Proof.
  unfold agreeUpto; intros.
  rewrite wordToNat_wplus in H2.
  change (wordToNat $1) with 1 in H2.
  assert (i < wordToNat n \/ i = wordToNat n)%nat by omega; intuition subst.
  rewrite H by assumption.

  unfold Array.upd.
  rewrite selN_updN_ne by omega; auto.

  unfold Array.upd.
  rewrite selN_updN_eq; auto.
  apply lt_goodSize'; auto.
  unfold natToW; rewrite natToWord_wordToNat; auto.
  change (wordToNat $1) with 1.
  eapply goodSize_weaken; eauto.

  assert (wordToNat n < length ls2)%nat; try omega.
  apply lt_goodSize'; auto.
  unfold natToW; rewrite natToWord_wordToNat; auto.
Qed.

Hint Extern 1 (agreeUpto _ (Array.upd _ _ _) _) =>
  eapply agreeUpto_S; [ eassumption | eassumption | solve [ eauto 7 ] ].

Lemma bound_nat : forall i len n,
  i < len
  -> n = wordToNat len
  -> i < natToW n.
Proof.
  intros; subst.
  unfold natToW; rewrite natToWord_wordToNat; auto.
Qed.

Hint Immediate bound_nat.

Lemma agreeUpto_total : forall ls1 ls2 (i : W) len,
  agreeUpto ls1 ls2 (wordToNat i)
  -> len <= i
  -> length ls1 = wordToNat len
  -> length ls2 = wordToNat len
  -> ls1 = ls2.
Proof.
  induction ls1; destruct ls2; simpl; intuition.

  assert (Hgt : (wordToNat i > 0)%nat).
  unfold wlt in H0.
  destruct (wordToNat i) eqn:Heq.
  rewrite wordToN_nat in H0.
  rewrite Heq in H0; simpl in H0.
  exfalso; apply H0.
  rewrite wordToN_nat.
  destruct (wordToNat len); nomega.
  omega.

  assert (Hle : $1 <= i).
  unfold wlt.
  change (wordToN $1) with 1%N.
  nomega.

  assert (Hlen : $1 <= len).
  unfold wlt.
  change (wordToN $1) with 1%N.
  pre_nomega.
  change (Pos.to_nat 1) with 1.
  destruct (wordToNat len); omega.

  f_equal.

  specialize (H 0); intuition idtac.

  apply IHls1 with (i ^- $1) (len ^- $1).
  do 2 intro.
  specialize (H (S i0)).
  apply H.
  rewrite wordToNat_wminus in H3 by assumption.
  change (wordToNat $1) with 1 in *.
  omega.

  unfold wlt; intro.
  apply Nlt_out in H3.
  autorewrite with N in *.
  repeat rewrite wordToNat_wminus in H3 by assumption.
  nomega.

  rewrite wordToNat_wminus by assumption.
  change (wordToNat $1) with 1; omega.
  rewrite wordToNat_wminus by assumption.
  change (wordToNat $1) with 1; omega.
Qed.

Lemma agreeUpto_total_himp : forall ls1 ls2 (i : W) len specs p,
  agreeUpto ls1 ls2 (wordToNat i)
  -> len <= i
  -> length ls1 = wordToNat len
  -> length ls2 = wordToNat len
  -> himp specs (array ls2 p) (array ls1 p).
Proof.
  intros.
  replace ls2 with ls1.
  reflexivity.
  eauto using agreeUpto_total.
Qed.

Hint Immediate agreeUpto_total_himp.

Theorem ok : moduleOk m.
Proof.
  vcgen; abstract (sep hints; eauto).
Qed.
