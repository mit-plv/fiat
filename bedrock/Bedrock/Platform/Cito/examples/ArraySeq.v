Require Import Coq.omega.Omega.
Require Import Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Malloc Bedrock.Platform.Cito.examples.Seq.

Module Type ADT.
  Parameter arr : list W -> W -> HProp.

  Axiom arr_fwd : forall ws self, arr ws self ===> [| self <> 0 |] * [| freeable self (2 + length ws) |]
    * [| goodSize (2 + length ws) |]
    * (Ex junk, self ==*> $ (length ws), junk)
    * array ws (self ^+ $8).
  Axiom arr_bwd : forall ws (self : W), [| self <> 0 |] * [| freeable self (2 + length ws) |]
    * [| goodSize (2 + length ws) |]
    * (Ex junk, self ==*> $ (length ws), junk)
    * array ws (self ^+ $8) ===> arr ws self.
End ADT.

Module Adt : ADT.
  Open Scope Sep_scope.

  Definition arr (ws : list W) (self : W) : HProp :=
    [| self <> 0 |] * [| freeable self (2 + length ws) |] * [| goodSize (2 + length ws) |]
    * (Ex junk, self ==*> $ (length ws), junk)
    * array ws (self ^+ $8).

  Theorem arr_fwd : forall ws self, arr ws self ===> [| self <> 0 |] * [| freeable self (2 + length ws) |]
    * [| goodSize (2 + length ws) |]
    * (Ex junk, self ==*> $ (length ws), junk)
    * array ws (self ^+ $8).
    unfold arr; sepLemma.
  Qed.

  Theorem arr_bwd : forall ws (self : W), [| self <> 0 |] * [| freeable self (2 + length ws) |]
    * [| goodSize (2 + length ws) |]
    * (Ex junk, self ==*> $ (length ws), junk)
    * array ws (self ^+ $8) ===> arr ws self.
    unfold arr; sepLemma.
  Qed.
End Adt.

Import Adt.
Export Adt.

Lemma allocated_out'' : forall p len offset,
  allocated p offset len ===> Ex ws, ptsto32m' nil p offset ws * [| length ws = len |].
  induction len; sepLemmaLhsOnly.
  apply himp_ex_c; exists nil; sepLemma.
  etransitivity; [ apply himp_star_frame; [ apply IHlen | reflexivity ] | ].
  sepLemmaLhsOnly.
  apply himp_ex_c; exists (x :: x0); sepLemma.
  destruct offset; sepLemma.
Qed.

Lemma allocated_out' : forall p len offset,
  allocated p offset len ===> Ex ws, ptsto32m nil p offset ws * [| length ws = len |].
  intros; eapply Himp_trans; [ apply allocated_out'' | ].
  apply Himp_ex; intro.
  apply Himp_star_frame; try apply Himp_refl.
  apply ptsto32m'_out.
Qed.

Inductive view_shift (n : nat) := ViewShift.
Local Hint Constructors view_shift.

Lemma allocated_out : forall p offset len,
  view_shift offset
  -> allocated p offset len ===> Ex ws, array ws (p ^+ $ (offset)) * [| length ws = len |].
  intros; eapply Himp_trans; [ apply allocated_out' | ].
  apply Himp_ex; intro.
  apply Himp_star_frame; try apply Himp_refl.
  eapply Himp_trans; [ apply ptsto32m_shift_base' | ].
  instantiate (1 := offset); auto.
  rewrite Minus.minus_diag; apply Himp_refl.
Qed.

Lemma allocated_in'' : forall p len offset,
  (Ex ws, ptsto32m' nil p offset ws * [| length ws = len |]) ===> allocated p offset len.
  induction len; sepLemmaLhsOnly.
  destruct x; sepLemma.
  destruct x; sepLemma.
  apply himp_star_frame.
  etransitivity; [ | apply IHlen ].
  sepLemma.
  destruct offset; sepLemma.
Qed.

Lemma allocated_in' : forall p len offset,
  (Ex ws, ptsto32m nil p offset ws * [| length ws = len |]) ===> allocated p offset len.
  intros; eapply Himp_trans; [ | apply allocated_in'' ].
  apply Himp_ex; intro.
  apply Himp_star_frame; try apply Himp_refl.
  apply Arrays.ptsto32m'_in.
Qed.

Lemma allocated_in : forall p ws,
  goodSize (S (S (length ws)))
  -> p =?> 2 * array ws (p ^+ $8) ===> p =?> wordToNat (natToW (S (S (length ws)))).
  intros.

  replace (wordToNat (natToW (S (S (length ws))))) with (S (S (length ws))).
  eapply Himp_trans; [ | apply allocated_join ].
  apply Himp_star_frame; try apply Himp_refl.
  2: auto.
  simpl.
  eapply Himp_trans; [ | apply allocated_in' ].
  sepLemma.
  instantiate (1 := ws); omega.
  etransitivity; [ | apply ptsto32m_shift_base ].
  instantiate (1 := 8); reflexivity.
  auto.
  rewrite wordToNat_natToWord_idempotent; auto.
Qed.

Definition hints : TacPackage.
  prepare (arr_fwd, allocated_out) (arr_bwd, allocated_in).
Defined.

Definition newS := newS arr 8.
Definition deleteS := deleteS arr 7.
Definition readS := readS arr 0.
Definition writeS := writeS arr 0.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS] ]]
  bmodule "ArraySeq" {{
    bfunction "new"("extra_stack", "len", "x") [newS]
      "x" <- 2 + "len";;
      "x" <-- Call "malloc"!"malloc"(0, "x")
      [PRE[V, R] R =?> (2 + wordToNat (V "len"))
        * [| R <> 0 |] * [| freeable R (2 + wordToNat (V "len")) |]
        * [| goodSize (2 + wordToNat (V "len")) |] * mallocHeap 0
       POST[R'] Ex ws, arr ws R' * [| length ws = wordToNat (V "len") |] * mallocHeap 0];;

      "x" *<- "len";;
      Note [view_shift 8];;
      Return "x"
    end

    with bfunction "delete"("extra_stack", "self", "x") [deleteS]
      "x" <-* "self";;
      "x" <- 2 + "x";;
      Call "malloc"!"free"(0, "self", "x")
      [PRE[_] Emp
       POST[_] Emp];;

      Return 0
    end

    with bfunction "read"("extra_stack", "self", "n") [readS]
      "n" <- 4 * "n";;
      "self" <- "self" + 8;;
      "self" <-* "self" + "n";;
      Return "self"
    end

    with bfunction "write"("extra_stack", "self", "n", "v") [writeS]
      "n" <- 4 * "n";;
      "self" <- "self" + 8;;
      "self" + "n" *<- "v";;
      Return 0
    end
  }}.

Local Hint Extern 1 (@eq W _ _) => words.

Lemma twoPlus_le : forall w,
  goodSize (2 + wordToNat w)
  -> natToW 2 <= natToW 2 ^+ w.
  intros.
  rewrite <- (natToWord_wordToNat w).
  rewrite <- natToWord_plus.
  apply le_goodSize; auto.
Qed.

Local Hint Immediate twoPlus_le.

Local Hint Extern 1 (himp _ _ _) =>
  match goal with
    | [ H : _ = wordToNat _ |- _ ] =>
      rewrite H; unfold natToW; rewrite natToWord_wordToNat; solve [ step auto_ext ]
  end.

Lemma twoPlus_freeable : forall w len,
  freeable w (S (S len))
  -> goodSize (S (S len))
  -> freeable w (wordToNat (natToW (S (S len)))).
  intros; rewrite wordToNat_natToWord_idempotent; auto.
Qed.

Local Hint Immediate twoPlus_freeable.

Section hints.
  Hint Rewrite wordToNat_wplus using assumption : sepFormula.

  Theorem ok : moduleOk m.
    vcgen; abstract (sep hints; auto).
  Qed.
End hints.
