(** * A variant of the [Comp] monad laws using [apply] *)
Require Import Coq.Strings.String Coq.Sets.Ensembles.
Require Import Fiat.Common.
Require Import Fiat.Computation.Core Fiat.Computation.Monad Fiat.Computation.SetoidMorphisms.

(** ** Helper monad laws, on the left side of a [refine] *)

Section monad.
  Local Ltac t := let H := fresh in intro H; autorewrite with refine_monad; exact H.

  Lemma refine_bind_bind_helper X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x y
  : refine (Bind x (fun u => Bind (f u) g)) y
    -> refine (Bind (Bind x f) g) y.
  Proof. t. Qed.

  Lemma refine_bind_unit_helper X Y (f : X -> Comp Y) x y
  : refine (f x) y
    -> refine (Bind (Return x) f) y.
  Proof. t. Qed.

  Lemma refine_unit_bind_helper X (x : Comp X) y
  : refine x y
    -> refine (Bind x (@Return X)) y.
  Proof. t. Qed.

  (** XXX This is a terribly ugly tactic that should be improved *)
  Local Ltac t2 :=
    unfold refine; intros;
    specialize_all_ways;
    computes_to_inv; eauto;
    computes_to_econstructor; eauto.

  Lemma refine_under_bind_helper X Y (f f' : X -> Comp Y) x x' y
  : (forall y, refine x y -> refine x' y)
    -> (forall x0 y, refine (f x0) y -> refine (f' x0) y)
    -> refine (Bind x f) y
    -> refine (Bind x' f') y.
  Proof. t2. Qed.

  Lemma refine_under_bind_helper_1 X Y (f : X -> Comp Y) x x' y
  : (forall y, refine x y -> refine x' y)
    -> refine (Bind x f) y
    -> refine (Bind x' f) y.
  Proof. t2. Qed.

  Lemma refine_under_bind_helper_2 X Y (f f' : X -> Comp Y) x y
  : (forall x0 y, refine (f x0) y -> refine (f' x0) y)
    -> refine (Bind x f) y
    -> refine (Bind x f') y.
  Proof. t2. Qed.
End monad.

Ltac simplify_with_applied_monad_laws :=
  progress repeat first [ simple apply refine_bind_unit_helper
                        | simple apply refine_unit_bind_helper
                        | simple apply refine_bind_bind_helper
                        | simple eapply refine_under_bind_helper;
                          [ let H := fresh in
                            intros ? H;
                            simplify_with_applied_monad_laws;
                            exact H
                          | let H := fresh in
                            intros ? ? H;
                            simplify_with_applied_monad_laws;
                            exact H
                          | ]
                        | simple eapply refine_under_bind_helper_1;
                          [ let H := fresh in
                            intros ? H;
                            simplify_with_applied_monad_laws;
                            exact H
                          | ]
                        | simple eapply refine_under_bind_helper_2;
                          [ let H := fresh in
                            intros ? ? H;
                            simplify_with_applied_monad_laws;
                            exact H
                          | ] ].

Tactic Notation "simplify" "with" "monad" "laws" :=
  simplify_with_applied_monad_laws.

(* Ideally we would throw refineEquiv_under_bind in here as well, but it gets stuck *)

Tactic Notation "autorewrite" "with" "monad" "laws" :=
  repeat first [ setoid_rewrite refineEquiv_bind_bind
               | setoid_rewrite refineEquiv_bind_unit
               | setoid_rewrite refineEquiv_unit_bind].

Ltac interleave_autorewrite_refine_monad_with tac :=
  repeat first [ reflexivity
               | progress tac
               | progress autorewrite with refine_monad
               (*| rewrite refine_bind_bind'; progress tac
               | rewrite refine_bind_unit'; progress tac
               | rewrite refine_unit_bind'; progress tac
               | rewrite <- refine_bind_bind; progress tac
               | rewrite <- refine_bind_unit; progress tac
               | rewrite <- refine_unit_bind; progress tac ]*)
               | rewrite <- !refineEquiv_bind_bind; progress tac
               | rewrite <- !refineEquiv_bind_unit; progress tac
               | rewrite <- !refineEquiv_unit_bind; progress tac
               (*| rewrite <- !refineEquiv_under_bind; progress tac *)].
