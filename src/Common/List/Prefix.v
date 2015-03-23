(* Prefix of a list.*)
Require Import Coq.Lists.List ADTSynthesis.Common.
Section Prefix.

  Context {A : Type}.
  Context {A_eq_dec : forall (a a' : A), {a = a'} + {a <> a'}}.

  Definition prefix_prop (p s : list A) := exists ps, p ++ ps = s.

  Fixpoint prefix_bool (p s : list A) :=
    match p, s with
      | nil, _ => true
      | p' :: ps', s' :: ss' => if A_eq_dec p' s' then prefix_bool ps' ss' else false
      | _, _ => false
    end.

  Lemma prefix_bool_eq :
    forall (p s : list A), prefix_bool p s = true <-> prefix_prop p s.
  Proof.
    unfold prefix_prop, prefix_bool; split; revert s; induction p; intros s H; [
      eexists s; reflexivity |
      destruct s; simpl in H; [
        discriminate |
        find_if_inside; [subst | discriminate];
        apply_in_hyp IHp; destruct_ex; eexists; subst; reflexivity ] |
      reflexivity |
      destruct s; simpl in *; destruct H; [
        discriminate |
        injections; find_if_inside; intuition eauto ] ].
  Qed.

End Prefix.
