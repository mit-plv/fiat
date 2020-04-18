Require Import Bedrock.Platform.Cito.CompileStmtSpec.
Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.FreeVars.

Lemma Subset_singleton : forall x s,
  Subset (singleton x) s
  -> StringSet.In x s.
  intros.
  apply H.
  apply StringFacts.singleton_iff; auto.
Qed.

Local Hint Resolve Subset_singleton.

Require Import Bedrock.Platform.Cito.SetoidListFacts.

Lemma In_to_set : forall x ls,
  List.In x ls
  -> StringSet.In x (SSP.of_list ls).
  intros.
  eapply SSP.of_list_1.
  eapply InA_eq_In_iff; eauto.
Qed.

Local Hint Resolve In_to_set.

Lemma to_set_In : forall x ls,
  StringSet.In x (SSP.of_list ls)
  -> List.In x ls.
  intros.
  eapply SSP.of_list_1 in H.
  eapply InA_eq_In_iff; eauto.
Qed.

Local Hint Resolve to_set_In.

Lemma Subset_union_left : forall a b c,
  Subset (StringSet.union a b) c
  -> Subset a c /\ Subset b c.
  unfold Subset; intuition;
    (apply H; apply StringFacts.union_iff; auto).
Qed.

Lemma Subset_union_right : forall a b c,
  Subset a c
  -> Subset b c
  -> Subset (StringSet.union a b) c.
  unfold Subset; intuition.
  apply StringFacts.union_iff in H1; intuition.
Qed.

Local Hint Resolve Subset_union_right Max.max_lub.
