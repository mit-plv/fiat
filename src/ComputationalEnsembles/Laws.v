Require Import Coq.Classes.Morphisms.
Require Import ADTSynthesis.ComputationalEnsembles.Core ADTSynthesis.Computation.

Set Implicit Arguments.

Lemma Ensemble_fold_right_simpl {A B} (f : A -> B -> B) b S
: refineEquiv (@fold_right A B (fun a b' => ret (f a b')) (ret b) S)
              (ls <- to_list S;
               ret (List.fold_right f b ls)).
Proof.
  unfold fold_right.
  f_equiv; intro ls; simpl.
  induction ls; simpl; try reflexivity.
  rewrite IHls.
  autorewrite with refine_monad.
  reflexivity.
Qed.

Lemma Ensemble_fold_right_simpl' {A B} f b S
: refineEquiv (@Ensemble_fold_right A B f b S)
              (ls <- to_list S;
               ret (List.fold_right f b ls)).
Proof.
  exact (Ensemble_fold_right_simpl f b S).
Qed.
