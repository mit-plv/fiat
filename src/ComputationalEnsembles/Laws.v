Require Import Coq.Classes.Morphisms Coq.Lists.List.
Require Import Fiat.ComputationalEnsembles.Core Fiat.Computation.
Require Import Fiat.Common.Ensembles.Tactics Fiat.Common.Ensembles.

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

Lemma Same_set__elements__Union {A} xs
: Same_set A (elements xs) (List.fold_right (Union _) (Empty_set _) (map (Singleton _) xs)).
Proof.
  induction xs; [ | simpl; rewrite <- IHxs; clear IHxs ];
  Ensembles_t.
Qed.

Lemma Same_set__elements_cons__Union {A} x xs
: Same_set A (elements (x::xs)) (Union A (Singleton _ x) (elements xs)).
Proof.
  rewrite !Same_set__elements__Union; simpl; reflexivity.
Qed.
