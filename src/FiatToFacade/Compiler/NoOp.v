Require Import FiatToFacade.Compiler.Prerequisites.

Unset Implicit Arguments.

Lemma no_op :
  forall {av env},
  forall adts scas knowledge,
    refine (@Prog av env knowledge
                  scas scas
                  adts adts)
           (ret Skip).
Proof.
  unfold refine, Prog, ProgOk; constructor; intros.
  inversion_by computes_to_inv; subst.
  split; [ constructor | intros; inversion_facade; intuition ].
Qed.
