Require Import Coq.Classes.Morphisms.

Lemma option_map_None A B (f : A -> B) x
: option_map f x = None <-> x = None.
Proof.
  destruct x; simpl; split; intros; trivial; congruence.
Qed.

Global Instance option_rect_Proper_nondep {A B}
: Proper (pointwise_relation _ eq ==> eq ==> eq ==> eq)
         (@option_rect A (fun _ => B)).
Proof.
  repeat (intros [] || intro); simpl; eauto.
Qed.

Global Instance option_rect_Proper {A B}
: Proper (forall_relation (fun _ => eq) ==> eq ==> forall_relation (fun _ => eq))
         (@option_rect A B).
Proof.
  repeat (intros [] || intro); simpl; eauto.
Qed.

Lemma option_rect_Proper_nondep_eq {A B} {S S' : A -> B} {N N' v}
      (HS : forall vv, v = Some vv -> S vv = S' vv)
      (Hn : v = None -> N = N')
: option_rect (fun _ : option A => B) S N v
  = option_rect (fun _ : option A => B) S' N' v.
Proof.
  destruct v; simpl; auto using eq_refl with nocore.
Qed.
