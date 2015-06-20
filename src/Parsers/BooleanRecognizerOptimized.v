(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarNotations.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common Fiat.Common.Wf.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.Match.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Equality.
Require Export Fiat.Common.SetoidInstances.
Require Import Fiat.Common.OptionFacts.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Global Arguments string_dec : simpl never.
Global Arguments string_beq : simpl never.
Global Arguments parse_production' _ _ _ _ _ _ _ _ !_.
Global Arguments parse_production _ _ _ _ _ !_.

Lemma parse_production'_respectful {Char HSL predata A B C}
      {f g : forall (a : _ * A) (b : B a) (c : C a b) (str : @String Char HSL) (len : nat), len <= (fst a) -> String.string -> bool}
      (H : forall a b c d e h i, f a b c d e h i = g a b c d e h i)
      str0 a b c str len pf
: pointwise_relation
    _ eq
    (@parse_production' Char HSL predata str0 (f (str0, a) b c) str len pf)
    (@parse_production' Char HSL predata str0 (g (str0, a) b c) str len pf).
Proof.
  intro ls.
  revert str0 a b c str len pf; induction ls; simpl; trivial; intros.
  setoid_rewrite IHls.
  f_equal.
  apply map_Proper_eq; trivial; repeat intro.
  f_equal.
  unfold parse_item'.
  destruct a; trivial.
  rewrite H; reflexivity.
Qed.

Local Ltac simpl_setoid_rewrite lem :=
  let H := fresh in
  pose proof lem as H;
    setoid_rewrite H;
    clear H.

Section recursive_descent_parser.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {ls : list (String.string * productions Char)}.
  Context {data : @boolean_parser_dataT Char _}.

  Class str_carrier_data (constT varT : Type)
    := { to_string : constT * varT -> String;
         of_string_const : String -> constT;
         of_string_var : String -> varT }.
  Class str_carrier_ok (constT varT : Type) {SD : str_carrier_data constT varT}
    := { to_of : forall x, to_string (of_string_const x, of_string_var x) = x;
         of_const_to : forall x, of_string_const (to_string x) = fst x;
         of_var_to : forall x, of_string_var (to_string x) = snd x;
         drop_const : forall x n, of_string_const (drop n x) = of_string_const x;
         take_const : forall x n, of_string_const (take n x) = of_string_const x }.

  (*Definition str_carrier' (constT varT : Type)
    := { to_string : constT * varT -> StringLike.String
       & { of_string : StringLike.String -> constT * varT
         | (forall x, to_string (of_string x) = x)
           /\ (forall x, of_string (to_string x) = x)
           /\ (forall x n, fst (of_string (drop n x)) = fst (of_string x))
           /\ (forall x n, fst (of_string (take n x)) = fst (of_string x)) } }.

  Definition str_carrier_default {constT varT} (strC : str_carrier' constT varT)
  : str_carrier constT varT.
  Proof.
    refine {| to_string := projT1 strC;
              of_string := proj1_sig (projT2 strC) |};
    apply (proj2_sig (projT2 strC)).
  Defined.*)

  Context constT varT {strC : str_carrier_data constT varT} {strCH : str_carrier_ok}.

  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).

  Local Ltac do_proper_solve_with tac
    := repeat match goal with
                | [ |- ?x = ?x ] => reflexivity
                | [ |- ?x = ?y ] => is_evar x; is_var y; reflexivity
                | [ |- ?x = false ] => is_evar x; reflexivity
                | [ |- ?x = true ] => is_evar x; reflexivity
                | [ |- pointwise_relation _ _ _ _ ] => intro
                | _ => solve [ tac ]
                | [ |- _ = fold_left _ _ _ ]
                  => apply fold_left_f_eq_mor_Proper
                | [ |- _ = fold_right _ _ _ ]
                  => apply fold_right_f_eq_mor_Proper
                | [ |- _ = map _ _ ]
                  => apply map_Proper_eq; [ intro | ]
                | [ |- _ = option_rect ?P _ _ _ ]
                  => apply option_rect_Proper
                | [ |- _ = option_map _ _ ]
                  => apply option_map_Proper; [ intro | ]
                | [ |- _ = nth_error _ _ ]
                  => apply f_equal2
                | [ |- _ = select_production_rules _ _ ]
                  => apply f_equal2
                | [ |- orb _ _ = orb _ _ ]
                  => apply f_equal2
                | [ |- andb _ _ = andb _ _ ]
                  => apply f_equal2
                | [ |- ?f ?x ?y = bool_rect (fun _ => ?P) ?a ?b ?c ]
                  => is_evar f;
                    refine (_ : bool_rect (fun _ => P) (_ x y) (_ x y) (_ x y) = bool_rect (fun _ => P) a b c); cbv beta;
                    apply f_equal3
                | [ |- ?f ?x = ?f' ?x ] => is_evar f; is_var f'; is_var x; reflexivity
                | [ |- ?f ?x ?y = ?f' ?x ?y ] => is_evar f; is_var f'; is_var x; is_var y; reflexivity
                | [ |- ?f ?x ?y = orb ?x ?y ] => is_evar f; is_var x; is_var y; reflexivity
              end.

  Definition parse_nonterminal_opt'
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    let G := match goal with |- context[_ = parse_nonterminal (G := ?G) _ _] => constr:G end in
    let G' := head G in
    try unfold G'.
    cbv beta iota zeta delta [parse_nonterminal parse_nonterminal_or_abort parse_nonterminal_step parse_productions parse_productions' parse_production parse_item parse_item' Lookup list_to_grammar list_to_productions].
    simpl.
    eexists.
    let L := match goal with |- ?L = _ => constr:L end in
    let e := fresh "e" in
    let e' := fresh "e" in
    let pp := fresh "pp" in
    set (e := L);
      etransitivity;
      [
      | match goal with
          | [ |- _ = @Fix ?A ?R ?Rwf (fun a : ?A => forall (b :@?B a) (c : @?C a b) (d : @?D a b c) (e : @?E a b c d) (h : @?H a b c d e), @?P a b c d e h) ?f ?a ?b ?c ?d ?e ?h ]
            => refine ((fun H0 => @Fix5_Proper_eq A B C D E H R Rwf P _ f H0 a b c d e h) _)
        end;
        unfold forall_relation, pointwise_relation, respectful;
        let H' := fresh in
        (intros ??? H' ?????);
          let L := match goal with |- ?L = ?R => constr:L end in
          let R := match goal with |- ?L = ?R => constr:R end in
          set (e' := L);
            let R' := match type of H' with
                        | forall a0 a1 a2 a3 a4 a5 a6, ?x a0 a1 a2 a3 a4 a5 a6 = ?y a0 a1 a2 a3 a4 a5 a6
                          => let Rp := (eval pattern y in R) in
                             match Rp with
                               | ?R' y => (eval cbv beta in (R' x))
                             end
                      end in
            transitivity R';
              [ clear H';
                unfold parse_production;
                try match goal with
                      | [ |- appcontext[@parse_production' ?a ?b ?c ?d ?e ?f ?g ?h] ]
                        => set (pp := @parse_production' a b c d e f g h)
                    end
              | clear -H'; unfold sumbool_rect;
                unfold parse_production;
                repeat match goal with
                         | _ => reflexivity
                         | [ |- appcontext[match ?e with left _ => _ | right _ => _ end] ]
                           => destruct e
                         | [ |- ?e = andb (is_valid_nonterminal _ _) _ ]
                           => subst e;
                             apply f_equal;
                             match goal with
                               | [ |- ?e' = _ ]
                                 => set (e := e')
                             end
                       end;
                rewrite !map_map;
                do_proper_solve_with idtac;
                rewrite (parse_production'_respectful H');
                reflexivity ] ];
      [
      | let e2 := fresh in
        evar (e2 : bool);
        refine (eq_trans _ (_ : andb _ e2 = _));
          [
          | apply f_equal;
            repeat match goal with
                     | _ => rewrite !map_map
                     | _ => setoid_rewrite option_rect_option_map
                     | _ => setoid_rewrite (fun ls => eq_sym (@fold_symmetric _ orb Bool.orb_assoc Bool.orb_comm false ls))
                     | _ => progress cbv beta
                     | [ |- appcontext[?f (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
                       => let h := head f in
                          not constr_eq h (@eq);
                            rewrite (fun init => @f_fold_right_bool_rect _ _ _ (fun k => f k) init ls)
                     | [ |- appcontext[?f _ (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
                       => let h := head f in
                          not constr_eq h (@eq);
                            rewrite (fun extra_arg init => @f_fold_right_bool_rect _ _ _ (fun k => f extra_arg k) init ls)
                     | [ |- appcontext[fold_right (fun str_t else_case => bool_rect (fun _ => ?A -> ?B) (@?a str_t) else_case (@?b str_t))] ]
                       => setoid_rewrite (@fold_right_fun_bool_rect _ _ _ a b)
                     | [ |- appcontext[?f (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
                       => let h := head f in
                          not constr_eq h (@eq);
                            simpl_setoid_rewrite (fun init => @f_fold_right_bool_rect _ _ _ (fun k => f k) init ls)
                     | [ |- appcontext[?f _ (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
                       => let h := head f in
                          not constr_eq h (@eq);
                            simpl_setoid_rewrite (fun extra_arg init => @f_fold_right_bool_rect _ _ _ (fun k => f extra_arg k) init ls)
                     | [ |- appcontext G[fold_right (fun str_t else_case s => bool_rect (fun _ => ?T) (@?a str_t) (else_case s) (@?b str_t s))] ]
                       => etransitivity;
                         [
                         | solve [
                               do_proper_solve_with
                                 ltac:(symmetry;
                                       match goal with
                                         | [ |- fold_right (fun str_t else_case s => bool_rect (fun _ => ?T') (@?a' str_t) (else_case s) (@?b' str_t s)) _ _ _ = _ ]
                                           => exact (@fold_right_fun
                                                       _ _ _
                                                       (fun str_t else_cases s => bool_rect (fun _ => T') (a' str_t) else_cases (b' str_t s))
                                                       _ _ _)
                                       end)
                         ] ]
                     | [ |- appcontext[fold_right (fun str_t else_case => bool_rect (fun _ => ?A -> ?B) (@?a str_t) else_case (@?b str_t))] ]
                       => etransitivity;
                         [
                         | solve [
                               do_proper_solve_with
                                 ltac:(symmetry;
                                       lazymatch goal with
                                       | [ |- fold_right (fun str_t else_case => bool_rect (fun _ => ?A -> ?B) (@?a str_t) else_case (@?b str_t)) _ _ _ = _ ]
                                         => exact (@fold_right_fun_bool_rect _ _ _ a b _ _ _)
                                       | [ |- appcontext[fold_right (fun str_t else_case => bool_rect (fun _ => ?A -> ?B) (@?a str_t) else_case (@?b str_t))] ]
                                         => fail 1
                                       | _ => reflexivity
                                       end) ] ]
                   end;
            subst e2; reflexivity ];
          subst e2;
          try subst pp; simpl;
          subst e'; instantiate; reflexivity ];
      cbv beta iota zeta delta [bool_rect sumbool_rect];
      simpl;
      subst e; instantiate.
    reflexivity.
  Defined.

  Lemma take_drop_helper n ms x
  : take n (fold_right drop (to_string x) ms)
    = to_string (fst x,
                 of_string_var (take n (fold_right drop (to_string x) ms))).
  Proof.
    rewrite <- (rev_involutive ms).
    rewrite fold_left_rev_right.
    generalize (rev ms); clear ms; intro ms.
    revert n x; induction ms; intros n [x y]; simpl.
    { match goal with
        | [ |- ?x = ?y ]
          => etransitivity;
            [ symmetry; exact (to_of x)
            | etransitivity; [ | exact (to_of y) ] ]
      end.
      apply f_equal.
      apply injective_projections.
      { rewrite take_const, !of_const_to; reflexivity. }
      { rewrite !of_var_to; simpl; reflexivity. } }
    { pose proof (IHms n (let x' := (drop a (to_string (x, y))) in (of_string_const x', of_string_var x'))) as IHms'.
      rewrite to_of in IHms'.
      rewrite IHms'; clear IHms'; simpl.
      rewrite drop_const, !of_var_to, !of_const_to; simpl.
      reflexivity. }
  Qed.

  Definition parse_nonterminal_opt''
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    eexists.
    transitivity (proj1_sig (parse_nonterminal_opt' str nt)); [ | exact (proj2_sig (parse_nonterminal_opt' str nt)) ].
    cbv beta iota zeta delta [parse_nonterminal_opt' proj1_sig].
    lazymatch goal with
      | [ |- ?e = Fix
                    ?wf
                    (fun (a : ?T0) => ?T1 -> String -> ?T2)
                    (fun (a' : ?T0)
                         (x : forall a'' : ?T0,
                                ?R a'' a'
                                -> ?T1 -> String -> @?T2' a'')
                         (y : ?T1)
                         (z : String)
                     => @?f a' x y z)
                    ?v1 ?v2 ?str ?v4 ?v5 ?v6 ]
        => idtac;
          let f' := constr:(fun const_str
                                 (a' : T0)
                                 (x : forall a'' : T0, R a'' a' -> T1 -> varT -> T2' a'')
                                 (y : T1)
                                 (z : varT)
                             => f a' (fun a'' rwf t1 str'
                                      => x a'' rwf t1 (of_string_var str'))
                                  y (to_string (const_str, z))) in
          let vstr' := constr:(of_string_var str) in
          let f'h := fresh "f0" in
          let fh := fresh "f1" in
          set (f'h := f');
            set (fh := f);
            let GT := constr:(Fix
                                wf
                                (fun (a : T0) => T1 -> varT -> T2)
                                (f'h (of_string_const str))
                                v1 v2 vstr' v4 v5 v6
                              = Fix
                                  wf
                                  (fun (a : T0) => T1 -> String -> T2)
                                  fh
                                  v1 v2 str v4 v5 v6) in
            refine (_ : GT); change GT;
            let H := fresh in
            assert (H : forall a b vstr' d e f0,
                          Fix wf (fun (a : T0) => T1 -> varT -> T2) (f'h (of_string_const str)) a b vstr' d e f0
                          = Fix wf (fun (a : T0) => T1 -> String -> T2) fh a b (to_string (of_string_const str, vstr')) d e f0);
              [ let a := fresh in intro a; induction (wf a) as [?? IH]
              | specialize (fun a b => H a b (of_string_var str));
                rewrite to_of in H;
                rewrite <- H;
                reflexivity ]
    end.
    intros.
    rewrite !Fix5_eq;
      [ unfold f0 at 1, f1 at 1
      | unfold f0, f1
      | unfold f0, f1 ];
      repeat match goal with
               | _ => progress intros
               | [ |- ?x = ?x ] => reflexivity
               | [ |- fold_right _ _ _ = fold_right _ _ _ ]
                 => apply fold_right_f_eq_mor_Proper; [ intros ?? | | ]
               | [ |- (match ?x with _ => _ end) = (match ?x with _ => _ end) ]
                 => destruct x eqn:?
               | [ |- (match ?x with _ => _ end) _ _ _ _ = (match ?x with _ => _ end) _ _ _ _ ]
                 => destruct x eqn:?
               | [ H : of_string_const _ = ?x |- context[?x] ] => rewrite <- H
               | [ |- fold_left _ _ _ = fold_left _ _ _ ]
                 => rewrite <- !fold_left_rev_right
               | _ => progress do_proper_solve_with idtac
               | [ |- rev _ = rev _ ]
                 => apply f_equal
               | [ |- map _ ?ls = map _ ?ls ]
                 => apply map_ext; intro
               | [ |- EqNat.beq_nat ?x ?y = EqNat.beq_nat ?x' ?y ]
                 => apply f_equal2
               | [ |- context[(fst ?x, snd ?x)] ]
                 => rewrite <- surjective_pairing
               | [ |- context[to_string (of_string_const _, of_string_var _)] ]
                 => rewrite to_of
               | [ |- context[of_string_const (to_string _)] ]
                 => rewrite of_const_to
               | [ |- context[of_string_var (to_string _)] ]
                 => rewrite of_var_to
               | [ H : context[(fst ?x, snd ?x)] |- _ ]
                 => rewrite <- surjective_pairing in H
               | [ H : context[to_string (of_string_const _, of_string_var _)] |- _ ]
                 => rewrite to_of in H
               | [ |- parse_production' _ _ _ _ = parse_production' _ _ _ _ ]
                 => apply parse_production_drop_ext with (ms := nil); intros
               | [ |- _ = Fix _ _ _ _ _ (take ?n (fold_right drop (?f ?x) ?ms)) _ _ _ ]
                 => rewrite (take_drop_helper n ms x : take n (fold_right drop (f x) ms) = _)
               | _ => progress simpl in *
               | _ => congruence
               | [ |- Fix _ _ _ ?a ?b ?c ?d ?e ?f = _ ]
                 => specialize (fun H' => IH a H' b c d e f);
                   try match goal with
                         | [ H : _ |- _ ] => specialize (IH (or_introl H))
                       end;
                   try apply IH
               | [ |- prod_relation _ _ _ _ ] => hnf
               | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
               | [ H : _ = in_left |- _ ] => clear H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : context[negb (EqNat.beq_nat ?x ?y)] |- _ ] => destruct (EqNat.beq_nat x y) eqn:?
               | [ H : EqNat.beq_nat _ _ = false |- _ ] => apply EqNat.beq_nat_false in H
               | [ |- _ \/ _ ] => right; split; [ reflexivity | omega ]
             end.
  Defined.

  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    let impl := (eval cbv beta iota zeta delta [parse_nonterminal_opt'' proj1_sig] in (proj1_sig (parse_nonterminal_opt'' str nt))) in
    (exists impl).
    abstract (exact (proj2_sig (parse_nonterminal_opt'' str nt))).
  Defined.
End recursive_descent_parser.

(** This tactic solves the simple case where the type of string is
    judgmentally [const_data * variable_data], and [take] and [drop]
    judgmentally preserve the constant data. *)

(*Ltac solve_default_str_carrier :=
  match goal with |- str_carrier _ _ => idtac end;
  eapply str_carrier_default; hnf; simpl;
  match goal with |- { to_string : _ * _ -> string * _ & _ } => idtac end;
  let T := match goal with |- { to_string : _ * _ -> string * ?T & _ } => constr:T end in
  exists (fun x : string * T => x);
    exists (fun x : string * T => x);
    simpl;
    solve [ repeat split ].

Hint Extern 1 (str_carrier _ _) => solve_default_str_carrier : typeclass_instances.
*)
