Require Import Fiat.Common.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.Enumerable.ReflectiveForall.
Require Import Fiat.Common.Equality.

Section reflective_forall.
  Context {A : Type} (P : A -> bool)
          {eq_A : BoolDecR A}
          {Abl : BoolDec_bl (@eq A)}
          {Alb : BoolDec_lb (@eq A)}
          {Henum : Enumerable { x : A | is_true (P x) }}
          {R_enum : Type}
          {eq_R_enum : BoolDecR R_enum}
          {R_enum_bl : BoolDec_bl (@eq R_enum)}
          {R_enum_lb : BoolDec_lb (@eq R_enum)}.

  Section inner.
    Context {R : Type}
            (x : A)
            (f : A -> R_enum)
            (g : R_enum -> R)
            (base : R).

    Definition forall_enumerable_by_beq_aggregate : R
      := let all := List.map (@proj1_sig _ _) (enumerate { x : A | is_true (P x) }) in
         let possibilities := uniquize eq_R_enum (List.map f all) in
         List.fold_right
           (fun y else_case
            => If beq (f x) y Then g y Else else_case)
           base
           possibilities.

    Lemma forall_enumerable_by_beq_aggregate_correct
          (H_f_good : forall x y, f x = f y -> P x = P y)
    : forall_enumerable_by_beq_aggregate = if P x then g (f x) else base.
    Proof.
      rewrite <- (forall_enumerable_by_beq_correct P x (fun y => g (f y)) base).
      unfold forall_enumerable_by_beq_aggregate, forall_enumerable_by_beq.
      change eq_R_enum with beq.
      progress change (@beq _ (@beq _ eq_R_enum)) with (@beq _ eq_R_enum).
      rewrite fold_right_uniquize.
      rewrite !fold_right_beq_in_correct'.
      repeat match goal with
             | [ |- ?x = ?x ] => reflexivity
             | _ => discriminate
             | [ |- context[list_bin ?beq ?x ?y] ]
               => destruct (list_bin beq x y) eqn:?
             | [ H : list_bin _ _ _ = true |- _ ]
               => apply (list_in_bl bl) in H
             | [ H : List.In _ (List.map _ _) |- _ ] => apply List.in_map_iff in H
             | [ |- List.In _ (List.map _ _) ] => apply List.in_map_iff
             | _ => progress subst
             | _ => progress destruct_head ex
             | _ => progress destruct_head sig
             | _ => progress destruct_head and
             | _ => progress simpl in *
             | [ H : list_bin ?beq ?x ?y = false |- _ ]
               => exfalso; rewrite (list_in_lb lb) in H; [ | clear H ]
             | [ |- _ /\ _ ] => split
             | [ |- @ex (sig _) _ ] => eexists (exist _ _ _)
             | [ |- ex _ ] => eexists
             | [ |- _ = ?x ] => is_var x; reflexivity
             | [ |- ?f _ = ?f ?x ] => is_var x; reflexivity
             | [ |- List.In _ (enumerate _) ] => apply enumerate_correct
             end.
      Grab Existential Variables.
      eassumption.
      simpl; erewrite <- H_f_good by eassumption; assumption.
    Qed.

    Lemma forall_enumerable_by_beq_aggregate_correct_reachable
          (H_f_good : forall x y, f x = f y -> P x = P y)
          (H : is_true (P x))
    : forall_enumerable_by_beq_aggregate = g (f x).
    Proof.
      rewrite forall_enumerable_by_beq_aggregate_correct, H by assumption; reflexivity.
    Qed.
  End inner.
End reflective_forall.
