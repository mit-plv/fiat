Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Section TopSection.

    Require Import Bedrock.Platform.Cito.SemanticsExpr.

    Local Infix ";;" := Syntax.Seq (right associativity, at level 95).
    Local Notation skip := Syntax.Skip.

    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe RunsTo.

    Require Import Bedrock.Platform.AutoSep.

    Ltac invert :=
      match goal with
        | [ H : Safe _ _ _ |- _ ] => inversion_clear H; []
        | [ H : RunsTo _ _ _ _ |- _ ] => inversion_clear H; []
        | [ H : Semantics.Safe _ _ _ |- _ ] => inversion_clear H; []
        | [ H : Semantics.RunsTo _ _ _ _ |- _ ] => inversion_clear H; []
      end; intuition (subst; unfold vals in *; try congruence).

    Ltac t := intros; repeat invert; repeat (eauto; econstructor).

    Lemma Safe_Seq_Skip : forall fs k v, Safe fs (skip ;; k) v -> Safe fs k v.
      t.
    Qed.

    Lemma RunsTo_Seq_Skip : forall fs k v v', RunsTo fs k v v' -> RunsTo fs (skip ;; k) v v'.
      t.
    Qed.

    Lemma Safe_Seq_assoc : forall fs a b c v, Safe fs ((a ;; b) ;; c) v -> Safe fs (a ;; b;; c) v.
      t.
    Qed.

    Lemma RunsTo_Seq_assoc : forall fs a b c v v', RunsTo fs (a ;; b ;; c) v v' -> RunsTo fs ((a ;; b) ;; c) v v'.
      t.
    Qed.

    Lemma Safe_Seq_If_true : forall fs e t f k v, Safe fs (Syntax.If e t f ;; k) v -> wneb (eval (fst v) e) $0 = true -> Safe fs (t ;; k) v.
      t.
    Qed.

    Lemma RunsTo_Seq_If_true : forall fs e t f k v v', RunsTo fs (t ;; k) v v' -> wneb (eval (fst v) e) $0 = true -> RunsTo fs (Syntax.If e t f ;; k) v v'.
      t.
    Qed.

    Lemma Safe_Seq_If_false : forall fs e t f k v, Safe fs (Syntax.If e t f ;; k) v -> wneb (eval (fst v) e) $0 = false -> Safe fs (f ;; k) v.
      t.
    Qed.

    Lemma RunsTo_Seq_If_false : forall fs e t f k v v', RunsTo fs (f ;; k) v v' -> wneb (eval (fst v) e) $0 = false -> RunsTo fs (Syntax.If e t f ;; k) v v'.
      t.
    Qed.

    Lemma Safe_Seq_While_false : forall fs e s k v, Safe fs (Syntax.While e s ;; k) v -> wneb (eval (fst v) e) $0 = false -> Safe fs k v.
      t.
    Qed.

    Lemma RunsTo_Seq_While_false : forall fs e s k v v', RunsTo fs k v v' -> wneb (eval (fst v) e) $0 = false -> RunsTo fs (Syntax.While e s ;; k) v v'.
      t.
    Qed.

    Lemma RunsTo_Seq_While_true : forall fs e s k v v', RunsTo fs (s ;; Syntax.While e s ;; k) v v' -> wneb (eval (fst v) e) $0 = true -> RunsTo fs (Syntax.While e s ;; k) v v'.
      t.
    Qed.

    Lemma Safe_Seq_While_true : forall fs e s k v, Safe fs (Syntax.While e s ;; k) v -> wneb (eval (fst v) e) $0 = true -> Safe fs (s ;; Syntax.While e s ;; k) v.
      intros.
      invert.
      inversion H1; clear H1; intros.
      subst loop0 loop1; subst.
      econstructor; eauto.
      intros.
      econstructor; eauto.
      rewrite H5 in H0; intuition.
    Qed.

  End TopSection.

End Make.
