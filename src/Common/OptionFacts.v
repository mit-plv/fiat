Require Import Coq.Classes.Morphisms Coq.Relations.Relation_Definitions.

Set Implicit Arguments.

Scheme Minimality for option Sort Type.
Scheme Minimality for option Sort Set.
Scheme Minimality for option Sort Prop.

Lemma fold_option_rect {A B} (S : forall a : A, B (Some a)) (N : B None) (v : option A)
  : match v return B v with
    | Some x => S x
    | None => N
    end = option_rect B S N v.
Proof.
  reflexivity.
Qed.
Lemma fold_option_rect_nd {A B} (S : A -> B) (N : B) (v : option A)
  : match v return B with
    | Some x => S x
    | None => N
    end = option_rect (fun _ => B) S N v.
Proof.
  reflexivity.
Qed.

Global Instance option_rect_Proper_nd_forall {A B}
  : Proper (pointwise_relation _ eq ==> eq ==> forall_relation (fun _ => eq))
           (@option_rect A (fun _ => B)).
Proof.
  intros ?????? [?|]; subst; simpl; eauto.
Qed.
Lemma fold_option_rect_nodep {A B} (S : A -> B) (N : B) (v : option A)
  : match v return B with
    | Some x => S x
    | None => N
    end = option_rect_nodep S N v.
Proof.
  reflexivity.
Qed.

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

Definition option_eq {A} eq (x y : option A) :=
  match x with
  | None    => y = None
  | Some ax => match y with
               | None => False
               | Some ay => eq ax ay
               end
  end.

Global Instance Equivalence_option_eq {T} {R} {Equivalence_R:@Equivalence T R}
  : Equivalence (option_eq R).
Proof.
  split; cbv; repeat (intros [|] || intro || intuition congruence ||
                      solve [ apply reflexivity | apply symmetry; eassumption | eapply transitivity; eassumption ] ).
Qed.

Global Instance Proper_option_rect_nd_changebody
      {A B:Type} {RB:relation B} {a:option A}
  : Proper (pointwise_relation _ RB ==> RB ==> RB) (fun S N => option_rect (fun _ => B) S N a).
Proof. destruct a; cbv; repeat (intros [|] || intro); intuition. Qed.

(* FIXME: there used to be a typeclass resolution hint here, something like
  Hint Extern 1 (Proper _ (@option_rect ?A (fun _ => ?B))) => exact (@Proper_option_rect_nd_changebody A B _ _) : typeclass_instances.
 but I could not get it working after generalizing [RB] from [Logic.eq] ~ andreser *)

Global Instance Proper_option_rect_nd_changevalue
      {A B RA RB} some {Proper_some: Proper (RA==>RB) some}
  : Proper (RB ==> option_eq RA ==> RB) (@option_rect A (fun _ => B) some).
Proof. cbv; repeat (intros [|] || intro || f_equiv || intuition congruence). Qed.

Lemma option_rect_false_returns_true_iff {T} (f:T->bool) (o:option T) :
  option_rect (fun _ => bool) f false o = true <-> exists s:T, o = Some s /\ f s = true.
Proof.
  unfold option_rect; split;
    [ destruct o; simpl; intro; try discriminate; eexists | intros [? [? ?]]; subst ];
    eauto.
Qed.

Lemma option_rect_option_map : forall {A B C} (f:A->B) some none v,
    option_rect (fun _ => C) (fun x => some (f x)) none v = option_rect (fun _ => C) some none (option_map f v).
Proof.
  destruct v; reflexivity.
Qed.

Lemma option_rect_function {A B C S' N' v} f
  : f (option_rect (fun _ : option A => option B) S' N' v)
    = option_rect (fun _ : option A => C) (fun x => f (S' x)) (f N') v.
Proof. destruct v; reflexivity. Qed.

(*
Ltac commute_option_rect_Let_In := (* pull let binders out side of option_rect pattern matching *)
  idtac;
  lazymatch goal with
  | [ |- ?LHS = option_rect ?P ?S ?N (Let_In ?x ?f) ]
    => (* we want to just do a [change] here, but unification is stupid, so we have to tell it what to unfold in what order *)
    cut (LHS = Let_In x (fun y => option_rect P S N (f y))); cbv beta;
    [ set_evars;
      let H := fresh in
      intro H;
      rewrite H;
      clear;
      abstract (cbv [Let_In]; reflexivity)
    | ]
  end.
*)

Ltac replace_option_match_with_option_rect :=
  idtac;
  lazymatch goal with
  | [ |- _ = ?RHS :> ?T ]
    => lazymatch RHS with
       | match ?a with None => ?N | Some x => @?S x end
         => replace RHS with (option_rect (fun _ => T) S N a) by (destruct a; reflexivity)
       end
  end.

Ltac simpl_option_rect := (* deal with [option_rect _ _ _ None] and [option_rect _ _ _ (Some _)] *)
  repeat match goal with
         | [ |- context[option_rect ?P ?S ?N None] ]
           => change (option_rect P S N None) with N
         | [ |- context[option_rect ?P ?S ?N (Some ?x) ] ]
           => change (option_rect P S N (Some x)) with (S x); cbv beta
         end.

Definition option_leq_to_eq {A} (x y : option A) : x = y -> option_eq eq x y.
Proof. destruct x; intro; subst; simpl; reflexivity. Qed.

Ltac inversion_option_step :=
  match goal with
  | [ H : Some _ = Some _ |- _ ] => apply option_leq_to_eq in H; unfold option_eq in H
  | [ H : None = Some _ |- _ ] => solve [ inversion H ]
  | [ H : Some _ = None |- _ ] => solve [ inversion H ]
  | [ H : None = None |- _ ] => clear H
  end.

Ltac inversion_option := repeat inversion_option_step.
