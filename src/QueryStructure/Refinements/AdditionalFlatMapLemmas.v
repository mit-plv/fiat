Require Import List Permutation AdditionalLemmas AdditionalMorphisms Program Arith Morphisms.
(* TODO: Actually use this file *)

Lemma length_flat_map :
  forall {A B} seq (f: A -> list B),
    List.length (flat_map f seq) = 
    fold_left (fun count (x : A) => count + List.length (f x)) seq 0.
Proof.
  intros; 
  rewrite (Permutation_length (flat_map_rev_permutation seq f));
  rewrite flat_map_flatten, length_flatten, <- foldright_compose, fold_left_rev_right;
  unfold compose; simpl; setoid_rewrite plus_comm at 1.
Qed.
