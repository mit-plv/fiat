Require Import
        Fiat.BinEncoders.Env.Common.Specs.

Notation "[ n ]" := (exist _ n _) : binencoders.

Lemma sig_equivalence :
  forall (A : Type) (P : A -> Prop) (n m : A) (n_pf : P n) (m_pf : P m),
    n = m <-> exist P n n_pf = exist P m m_pf.
Proof.
  intros A P n m n_pf m_pf. split.
  intro nm_pf. subst.
  pose proof (proof_irrelevance _ n_pf m_pf).
  subst. reflexivity.
  inversion 1. eauto.
Qed.
