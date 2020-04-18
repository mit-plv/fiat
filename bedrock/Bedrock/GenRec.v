Set Implicit Arguments.
Set Strict Implicit.

Section PairWF.
  Variables T U : Type.
  Variable RT : T -> T -> Prop.
  Variable RU : U -> U -> Prop.

  Inductive R_pair : T * U -> T * U -> Prop :=
  | L : forall l l' r r',
    RT l l' -> R_pair (l,r) (l',r')
  | R : forall l r r',
    RU r r' -> R_pair (l,r) (l,r').

  Hypothesis wf_RT : well_founded RT.
  Hypothesis wf_RU : well_founded RU.

  Theorem wf_R_pair : well_founded R_pair.
  Proof.
    red. intro x.
    destruct x. generalize dependent u.
    apply (well_founded_ind wf_RT (fun t => forall u : U, Acc R_pair (t, u))) .
    do 2 intro.

    apply (well_founded_ind wf_RU (fun u => Acc R_pair (x,u))). intros.
    constructor. destruct y.
    remember (t0,u). remember (x,x0). inversion 1; subst;
    inversion H4; inversion H3; clear H4 H3; subst; eauto.
  Defined.
End PairWF.

Inductive R_nat : nat -> nat -> Prop :=
| R_S : forall n, R_nat n (S n).

Theorem wf_R_nat : well_founded R_nat.
Proof.
  red; induction a; constructor; intros.
    inversion H.
    inversion H; subst; auto.
Defined.

Fixpoint guard A (R : A -> A -> Prop) (n : nat) (wfR : well_founded R)
  {struct n}: well_founded R :=
  match n with
    | 0 => wfR
    | S n => fun x => Acc_intro x (fun y _ => guard n (guard n wfR) y)
  end.
