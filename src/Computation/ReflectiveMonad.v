(** * Simplification of computation via monad laws, reflectively *)
Require Import String Ensembles.
Require Import Common.
Require Import Computation.Core Computation.SetoidMorphisms Computation.Monad.

(** The main tactic is [simplify with monad laws] *)

Fixpoint general_simplify_computation_with_monad_laws
         (simpl_pick : forall A, Ensemble A -> Ensemble A)
         (fuel : nat)
         X (c : Comp X)
         {struct fuel}
: Comp X
  := match fuel with
       | 0 => c
       | S fuel' =>
         let simpl := general_simplify_computation_with_monad_laws simpl_pick fuel' in
         match c with
           | Return _ x => Return x
           | Pick A P => Pick (simpl_pick _ P)
           | Bind A B x f
             => match (*simpl _ *)x in Comp A' return (A' -> Comp B) -> Comp B with
                  | Return _ x'
                    => fun f => simpl _ (f x')
                  | Pick A' P'
                    => fun f => Bind (simpl _ (Pick P'))
                                     (fun x => simpl _ (f x))
                  | Bind A'' A' x' f'
                    => fun f => simpl _ (Bind x' (fun u => Bind (f' u) f))
                end f
         end
     end.

Lemma general_simplify_computation_with_monad_laws_correct
      (simpl_pick : forall A, Ensemble A -> Ensemble A)
      fuel X (c : Comp X)
      (H : forall A P x, In _ (simpl_pick A P) x -> In _ P x)
: refine c
         (general_simplify_computation_with_monad_laws simpl_pick fuel c).
Proof.
  change (forall A P, pointwise_relation _ (flip impl) P (simpl_pick A P)) in H.
  revert X c.
  induction fuel; simpl;
  [ reflexivity
  | ].
  repeat match goal with
           | _ => progress intros
           (** monad stuff *)
           | _ => reflexivity
           | _ => assumption
           | [ H : refine _ _ |- _ ] => progress setoid_rewrite H
           | _ => progress rewrite_strat topdown repeat (hints refine_monad)
           (** discrimination stuff *)
           | [ H : forall A P, pointwise_relation A (flip impl) P _ |- _ ]
             => solve [ eapply refine_flip_impl_Pick; apply H ]
           | [ |- appcontext[match ?c in (Comp T) return _ with _ => _ end] ] => destruct c; try reflexivity
           | [ |- appcontext[general_simplify_computation_with_monad_laws simpl_pick fuel ?c] ]
             => generalize (IHfuel _ c); generalize (general_simplify_computation_with_monad_laws simpl_pick fuel c);
                destruct 0; simpl
           (** trivial refinement with bind stuff *)
           | _ => solve [ eapply_hyp'; trivial ]
           | _ => eapply refine_bind; [ reflexivity | ]
           | _ => progress unfold pointwise_relation
         end.
Qed.

Lemma general_simplify_computation_with_monad_laws_helper
      (simpl_pick : forall A, Ensemble A -> Ensemble A)
      fuel X (c c' : Comp X)
      (H : forall A P x, In _ (simpl_pick A P) x -> In _ P x)
: refine (general_simplify_computation_with_monad_laws simpl_pick fuel c) c'
  -> refine c c'.
Proof.
  intro H'.
  etransitivity; try eassumption.
  apply general_simplify_computation_with_monad_laws_correct; assumption.
Defined.

Definition simplify_computation_with_monad_laws (fuel : nat) X (c : Comp X) : Comp X
  := general_simplify_computation_with_monad_laws (fun _ P => P) fuel c.

Lemma simplify_computation_with_monad_laws_helper
      fuel X (c c' : Comp X)
: refine (simplify_computation_with_monad_laws fuel c) c'
  -> refine c c'.
Proof.
  apply general_simplify_computation_with_monad_laws_helper.
  intros; assumption.
Qed.

Tactic Notation "simplify" "with" "monad" "laws" constr(fuel) :=
  refine (@simplify_computation_with_monad_laws_helper fuel _ _ _ _).

Tactic Notation "reflective" "simplify" "with" "monad" "laws" :=
  simplify with monad laws 1000.
