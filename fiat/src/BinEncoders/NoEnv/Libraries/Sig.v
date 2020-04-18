Require Import Coq.Logic.ProofIrrelevance.

Lemma sig_equivalence :
  forall (A : Type) (P : A -> Prop) (n m : A) (n_pf : P n) (m_pf : P m),
    n = m -> exist P n n_pf = exist P m m_pf.
Proof.
  intros A P n m n_pf m_pf nm_pf.
  subst.
  pose proof (proof_irrelevance _ n_pf m_pf).
  subst. reflexivity.
Qed.