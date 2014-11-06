Require Import ADTSynthesis.Common Coq.Arith.Arith Coq.Sets.Ensembles.

Class DecideableEnsemble {A} (P : Ensemble A) :=
  { dec : A -> bool;
    dec_decides_P : forall a, dec a = true <-> P a}.

Lemma Decides_false {A} :
  forall (P : Ensemble A)
         (P_dec : DecideableEnsemble P) a,
    dec a = false <-> ~ (P a).
Proof.
  split; unfold not; intros.
  + apply dec_decides_P in H0; congruence.
  + case_eq (dec a); intros; eauto.
    apply dec_decides_P in H0; intuition.
Qed.

Instance DecideableEnsemble_gt {A} (f f' : A -> nat)
  : DecideableEnsemble (fun a => f a > f' a) :=
  {| dec a := if le_lt_dec (f a) (f' a) then false else true |}.
Proof.
  intros; find_if_inside; intuition.
  exfalso; eapply gt_not_le; eassumption.
Defined.
