(** * Miscellaneous definitions about ensembles *)
Require Import Coq.Lists.List.
Require Export Coq.Sets.Ensembles.
Require Import Fiat.Common Fiat.Common.List.PermutationFacts
        Fiat.Common.Ensembles.EnsembleListEquivalence.
(** Coq's [cardinal] is stupid, and not total.  For example, it
    requires [Extensionality_Ensembles] to prove [cardinal _ (fun _ =>
    False) 0].  So we define a better one. *)
Definition cardinal U (A : Ensemble U) (n : nat) : Prop :=
  exists ls, EnsembleListEquivalence A ls /\ Datatypes.length ls = n.
(** To mimic the arguments of the built-in [cardinal]. *)
Arguments cardinal : clear implicits.

Lemma cardinal_Same_set {U} (A B : Ensemble U) x
      (H : Same_set _ A B)
      (H' : cardinal _ A x)
: cardinal _ B x.
Proof.
  destruct H' as [ls H'].
  exists ls.
  destruct_head and; split; auto.
  eapply EnsembleListEquivalence_Same_set; eassumption.
Qed.

Global Add Parametric Morphism {U} : (cardinal U)
    with signature Same_set _ ==> eq ==> iff
      as Same_set_cardinal.
Proof.
  intros; split; intros; eapply cardinal_Same_set;
  try eassumption;
  split; destruct_head_hnf and; assumption.
Qed.

Lemma cardinal_unique {U} (A : Ensemble U) x y
      (H : cardinal _ A x) (H' : cardinal _ A y)
: x = y.
Proof.
  destruct_head_hnf ex.
  destruct_head and.
  subst.
  apply Permutation_length.
  eapply EnsembleListEquivalence_Permutation; eassumption.
Qed.
