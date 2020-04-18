Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Semantics.Make E.

  Section TopSection.

    Local Infix ";;" := Syntax.Seq (right associativity, at level 95).
    Local Notation skip := Syntax.Skip.

    Hint Constructors Semantics.Safe.
    Hint Unfold Safe.

    Lemma Safe_Seq_Skip_Safe : forall fs s v, Safe fs s v -> Safe fs (s ;; skip) v.
      auto.
    Qed.

    Lemma RunsTo_Seq_Skip_RunsTo : forall fs s v v', RunsTo fs (s ;; skip) v v' -> RunsTo fs s v v'.
      inversion 1; subst.
      inversion H5; subst.
      auto.
    Qed.

  End TopSection.

End Make.
