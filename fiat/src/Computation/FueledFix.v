Require Import Coq.Classes.Morphisms
        Coq.Classes.SetoidTactics.
Require Import Fiat.Computation.

Section FueledFix.
  (* A bounded recursion operation for the Comp Monad. *)

  Variable A : Type. (* Argument Type *)
  Variable R : Type. (* Return Type *)

  Fixpoint FueledFix
           (fuel : nat)
           (base : Comp R)
           (body : (A -> Comp R) -> A -> Comp R)
           (arg : A)
  : Comp R :=
    match fuel with
      | O => base
      | S fuel' => body (FueledFix fuel' base body) arg
    end.
End FueledFix.

(* Can't rewrite under Fueled Fix at the moment,
as the condition on the body is not a proper relation. :p *)

(* Notation for our fueled fix function. *)
Notation "'Repeat' fuel 'initializing' a 'with' arg 'defaulting' rec 'with' base {{ bod }} " :=
  (FueledFix fuel base (fun rec a => bod) arg)
    (no associativity, at level 50,
     format "'Repeat' '[hv'  fuel  '/' 'initializing'  a  'with'  arg '/'  'defaulting'  rec  'with'  base  '/' {{ bod  }} ']' ").

Section FueledFixRefinements.
  (* TODO: Find a home for these refinements in the Computation folder. *)

  Variable A : Type. (* Argument Type *)
  Variable R : Type. (* Return Type *)

  (* Lemmas for refining FueledFix. *)

  (* Lemma refine_FueledFix_Bind (B : Type) :
    forall fuel body body' (base base' : Comp R) (arg : A) (k k' : R -> Comp B),
      refine base base'
      -> (forall a, refine (body a) (body' a))
      -> (forall r, refine (k r) (k' r))
      ->  refine (a <- FueledFix fuel base body arg; k a)
                 (a <- FueledFix fuel base body' arg; k' a).
  Proof.
    induction fuel; eauto.
  Qed. *)

Definition pointwise_refine
  (f g : (A -> Comp R) -> A -> Comp R) :=
  forall (rec rec' : A -> Comp R) (a : A),
    pointwise_relation A (@refine R) rec rec'
    -> refine (f rec a) (g rec' a).

Lemma transitive_pR :
  Transitive (pointwise_refine).
Proof.
  unfold Transitive, pointwise_refine, pointwise_relation; intros.
  etransitivity.
  apply H; eauto.
  apply H0. reflexivity.
Qed.

Add Parametric Morphism i
  : (@FueledFix A R i)
    with signature
    ((@refine R)
       ==> (pointwise_refine)
       ==> (@eq A)
       ==> (@refine R))
      as refineFix.
Proof.
  simpl; induction i; intros; simpl.
  - assumption.
  - unfold pointwise_refine, pointwise_relation, Proper, respectful in *.
    eapply H0.
    intros.
    generalize (IHi _ _ H _ _ H0 a); eauto.
Qed.

(* This is the main lemma for Fueled Fix, as we cannot use *)
(* setoid_rewriting because pointwise refine isn't a proper *)
(* relation (it's not reflexive). *)
Definition refineFueledFix
  : forall (fuel : nat)
           (base base' : Comp R)
           (body body' : (A -> Comp R) -> A -> Comp R)
           (arg : A),
    refine base base'
    -> (forall a bod bod',
           (forall a, refine (bod a) (bod' a))
           -> refine (body bod a) (body' bod' a))
    -> refine (FueledFix fuel base body arg)
           (FueledFix fuel base' body' arg).
Proof.
  intros; eapply refineFix; intros; eauto.
  intro; intros.
  eapply H0; apply H1.
Qed.

End FueledFixRefinements.
