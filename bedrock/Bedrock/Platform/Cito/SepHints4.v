Require Import Bedrock.Platform.AutoSep.
Require Import Coq.Lists.List.

Require Import Bedrock.Platform.Cito.SepHintsUtil.

Set Implicit Arguments.

Section TopSection.

  Definition locals_to_elim (_ : list string) := True.

  Lemma elim_locals : forall vars vs p, locals_to_elim vars -> locals vars vs 0 p ===> p =?> length vars.
    unfold locals; intros.
    sepLemma.
    eapply Himp_trans; [ apply ptsto32m'_in | ].
    eapply Himp_trans; [ apply ptsto32m'_allocated | ].
    rewrite length_toArray; apply Himp_refl.
  Qed.

  Definition hints_elim_locals : TacPackage.
    prepare elim_locals tt.
  Defined.

End TopSection.
