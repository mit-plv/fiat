Set Implicit Arguments.

Require Import Coq.Strings.String.
Require Import Bedrock.Platform.Cito.NatFacts.

Lemma length_append : forall s1 s2, String.length (s1 ++ s2) = String.length s1 + String.length s2.
  induction s1; simpl; intuition.
Qed.

Local Open Scope string.

Lemma prefix_neq : forall (s1 s2 : string), s1 <> "" -> (s1 ++ s2)%string <> s2.
  intros.
  intuition.
  contradict H.
  eapply f_equal with (f := String.length) in H0.
  rewrite length_append in H0.
  eapply plus_eq_right_0 in H0.
  destruct s1; simpl in *; intuition.
  discriminate.
Qed.

Lemma append_inj_2 : forall a b c, (a ++ b = a ++ c -> b = c)%string.
  induction a; simpl; intuition.
  injection H; intros.
  eauto.
Qed.
