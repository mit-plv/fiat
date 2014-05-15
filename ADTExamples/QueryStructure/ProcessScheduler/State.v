Inductive State := Sleeping | Running.

Definition beq_state s1 s2 :=
  match s1, s2 with
    | Sleeping, Sleeping => true
    | Running , Running  => true
    | _       , _        => false
  end.

Ltac beq_state_crush :=
  intros;
  repeat match goal with
           | [ s: State |- _ ] => destruct s
         end;
  unfold beq_state; intuition; try discriminate.

Lemma beq_state_true_iff :
  forall s1 s2, beq_state s1 s2 = true <-> s1 = s2.
Proof.
  beq_state_crush.
Qed.

Lemma beq_state_false_iff :
  forall s1 s2, beq_state s1 s2 = false <-> s1 <> s2.
Proof.
  beq_state_crush.
Qed.

Lemma beq_state_sym :
  forall s1 s2, beq_state s1 s2 = beq_state s2 s1.
Proof.
  beq_state_crush.
Qed.

Lemma state_eta_rule :
  forall (params: State),
  forall {B C: Type}
         (f: State -> B) (g: B -> C),
    g (f (params)) =
    g (State_rect (fun _ => B) (f Sleeping) (f Running) params).
Proof.
  intro params; intros; destruct params; simpl; trivial.
Qed.

Require Import QueryStructure.

Instance State_Query_eq : Query_eq State :=
  {| A_eq_dec := _ |}.
Proof.
  decide equality.
Qed.
