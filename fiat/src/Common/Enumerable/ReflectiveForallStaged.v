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
          {R_enum : Type}.

  Section inner.
    Context {R : Type}
            (x : A)
            (f : A -> R_enum)
            (g : R_enum -> R)
            (base : R).

    Definition forall_enumerable_by_beq_staged : R
      := let all := List.map (@proj1_sig _ _) (enumerate { x : A | is_true (P x) }) in
         List.fold_right
           (fun y else_case
            => If
                 beq x (fst y)
               Then
                 g (snd y)
               Else
                 else_case)
           base
           (List.combine all (List.map f all)).

(*    Definition forall_enumerable_by_beq_staged' : R
      := let all := List.map (@proj1_sig _ _) (enumerate { x : A | is_true (P x) }) in
         let possibilities := uniquize eq_R_enum (List.map f all) in
         List.fold_right
           (fun y else_case
            => If beq (f x) y Then g y Else else_case)
           base
           possibilities.

    Lemma forall_enumerable_by_beq_staged'_eq
          (H_f_good : forall y, f x = f y -> P y -> P x)
      : forall_enumerable_by_beq_staged = forall_enumerable_by_beq_staged'.
    Proof.
      unfold forall_enumerable_by_beq_staged', forall_enumerable_by_beq_staged.
      destruct (P x) eqn:Hx.
      { match goal with
        | [ |- context[uniquize ?beq ?ls] ]
          => induction (uniquize beq ls) as [|y ys IHys]
        end.
        { reflexivity. }
        { simpl; rewrite IHys; clear IHys.
          repeat match goal with
                 | [ |- _ = _ ] => reflexivity
                 | _ => progress subst
                 | [ H : beq _ _ = true |- _ ] => apply bl in H
                 | [ H : context[beq ?x ?x] |- _ ] => rewrite lb in H by reflexivity
                 | _ => discriminate
                 | [ H : context[if ?b then _ else _] |- _ ]
                   => destruct b eqn:?; simpl in *
                 | [ |- context[If ?b Then _ Else _] ]
                   => destruct b eqn:?; simpl
                 | [ H : List.fold_right orb false (List.map _ _) = _ |- _ ]
                   => apply fold_right_orb_map_sig1 in H
                 | [ H : List.fold_right orb false (List.map _ _) = false |- _ ]
                   => rewrite fold_right_orb_map_sig2 in H; [ | clear H ]
                 | _ => progress destruct_head sig
                 | _ => progress destruct_head and
                 | [ |- { _ : _ | _ } ] => eexists
                 | [ |- _ /\ _ ] => split
                 | [ |- List.In ?x (List.map (@proj1_sig ?A ?B) ?ls) ]
                   => apply (fun x0 x1 => List.in_map (@proj1_sig A B) ls (exist _ x0 x1))
                 | [ |- context[beq ?x ?y] ] => unify x y; rewrite lb by reflexivity
                 | [ |- List.In _ (enumerate _) ] => apply enumerate_correct
                 end. } }
      { match goal with
        | [ |- context[uniquize _ (List.map _ ?ls)] ]
          => destruct (list_bin beq x ls) eqn:Heq; [ exfalso | ]
        end.
        { apply (list_in_bl bl), List.in_map_iff in Heq.
          destruct_head ex;
          destruct_head sig;
          destruct_head and;
          subst.
          congruence. }
        match goal with
        | [ |- List.fold_right (fun y else_case => If (@?T y) Then _ Else _) _ _ = _ ]
          => assert (forall y, P y -> T (f y) = false)
        end.
        { intros y' Hy'.
          match goal with
          | [ |- context[enumerate ?T] ]
            => induction (enumerate T) as [|y ys IHys]
          end.
          { reflexivity. }
          { simpl in *.
            repeat match goal with
                   | [ H : orb _ _ = false |- _ ] => apply Bool.orb_false_iff in H
                   | _ => progress destruct_head and
                   | _ => progress specialize_by assumption
                   | [ H : beq _ _ = true |- _ ] => apply bl in H
                   | [ H : context[beq ?x ?x] |- _ ] => rewrite lb in H by reflexivity
                   | _ => rewrite IHys'; []; clear IHys'
                   | [ |- context[beq ?x ?y] ]
                     => destruct (beq x y) eqn:?
                   | _ => progress subst
                   | _ => progress simpl
                   | _ => congruence
                   end. } }
        simpl in *.
        match goal with
        | [ |- context[uniquize ?beq (List.map _ (List.map _ ?ls))] ]
          => induction ls as [|y ys IHys]
        end.
        { reflexivity. }
        { simpl in *.
          repeat match goal with
                 | [ H : orb _ _ = false |- _ ] => apply Bool.orb_false_iff in H
                 | _ => progress destruct_head and
                 | _ => progress specialize_by assumption
                 | [ |- List.fold_right ?f ?k (if ?b then ?x else ?y)
                        = List.fold_right ?f' ?k (if ?b then ?x else ?y) ]
                   => transitivity (if b then List.fold_right f k x else List.fold_right f k y);
                     [ destruct b; reflexivity
                     | transitivity (if b then List.fold_right f' k x else List.fold_right f' k y);
                       [
                       | destruct b; reflexivity ] ]
                 | [ |- (if ?b then ?x else ?x) = _ ]
                   => transitivity x; [ destruct b; reflexivity | ]
                 | [ |- _ = (if ?b then ?x else ?x) ]
                   => transitivity x; [ | destruct b; reflexivity ]
                 | [ |- (if ?b then ?x else (If ?b' Then ?y Else ?x)) = _ ]
                   => transitivity (If (b || negb b')%bool Then x Else y); [ destruct b, b'; reflexivity | ]
                 | _ => progress simpl in *
                 | _ => progress subst
                 | _ => progress destruct_head sig
                 | [ H : beq _ _ = true |- _ ] => apply bl in H
                 | [ H : context[beq ?x ?x] |- _ ] => rewrite lb in H by reflexivity
                 | [ |- context[beq ?x ?y] ]
                   => destruct (beq x y) eqn:?
                 | [ H : forall y', ?k = ?f y' -> is_true (?P y') -> is_true false,
                       H' : is_true (?P ?y),
                       H'' : ?k = ?f ?y |- _ ]
                   => specialize (H _ H'' H')
                 | _ => congruence
                 | [ H : forall y, _ -> orb _ _ = false |- _ ]
                   => pose proof (fun y k => Bool.orb_false_elim _ _ (H y k)); clear H
                 | _ => progress split_and
                 | [ H : forall y, is_true (?P y) -> _ = false,
                       H' : is_true (?P ?x0)
                       |- context[List.fold_right orb false (List.map (fun z => if beq (?f z) (?f ?x0) then beq _ _ else _) _)] ]
                   => rewrite (H _ H')
                 | _ => rewrite Bool.orb_true_r
                 end.
          rewrite <- IHys; clear IHys.
          match goal with
          | [ |- List.fold_right (fun x y => If orb (if @?A x y then false else false) (@?B x y) Then @?C x y Else @?D x y) ?E ?ls
                 = List.fold_right (fun x y => If (@?B x y) Then @?C x y Else @?D x y) ?E ?ls ]
            => clear; induction ls as [|l0 ls0 IHls0];
               [ reflexivity
               | simpl; rewrite IHls0; clear IHls0 ]
          end.
          match goal with
          | [ |- context[if ?e then false else false] ]
            => destruct e eqn:?; reflexivity
          end. } }
      Grab Existential Variables.
      assumption.
    Qed.
*)
    Lemma forall_enumerable_by_beq_staged_correct
          (H_f_good : forall y, f x = f y -> P y -> P x)
    : forall_enumerable_by_beq_staged = if P x then g (f x) else base.
    Proof.
      rewrite <- (forall_enumerable_by_beq_correct P x (fun y => g (f y)) base).
      unfold forall_enumerable_by_beq_staged, forall_enumerable_by_beq.
      rewrite combine_map_r, map_combine_id; simpl.
      rewrite fold_right_map; unfold compose; simpl.
      reflexivity.
    Qed.

    Lemma forall_enumerable_by_beq_staged_correct_reachable
          (H : is_true (P x))
    : forall_enumerable_by_beq_staged = g (f x).
    Proof.
      rewrite forall_enumerable_by_beq_staged_correct, H by (rewrite H; reflexivity).
      reflexivity.
    Qed.
  End inner.
End reflective_forall.
