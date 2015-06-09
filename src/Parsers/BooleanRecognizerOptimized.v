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

  Class str_carrier (constT varT : Type)
    := { to_string : constT * varT -> String;
         of_string : String -> constT * varT;
         to_of : forall x, to_string (of_string x) = x;
         of_to : forall x, of_string (to_string x) = x;
         drop_const : forall x n, fst (of_string (drop n x)) = fst (of_string x);
         take_const : forall x n, fst (of_string (take n x)) = fst (of_string x)}.

  Definition str_carrier' (constT varT : Type)
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
  Defined.

  Context constT varT {strC : str_carrier constT varT}.

  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).

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
                       end;
                setoid_rewrite (parse_production'_respectful H');
                reflexivity ] ];
      [
      | repeat match goal with
                 | _ => progress simpl
                 | _ => setoid_rewrite (fun ls => eq_sym (@fold_symmetric _ orb Bool.orb_assoc Bool.orb_comm false ls))
                 | _ => setoid_rewrite Bool.orb_false_r
                 | [ |- appcontext[fold_right (fun str_t else_case s => bool_rect (fun _ => ?T) (@?a str_t) (else_case s) (@?b str_t s))] ]
                   => simpl_setoid_rewrite (@fold_right_fun _ _ _ (fun str_t else_cases s => bool_rect (fun _ => T) (a str_t) else_cases (b str_t s)))
                 | [ |- appcontext[?f (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls) ?x] ]
                   => simpl_setoid_rewrite (fun init => @f_fold_right_bool_rect _ _ _ (fun k => f k x) init ls)
                 | [ |- appcontext[?f (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
                   => simpl_setoid_rewrite (fun init => @f_fold_right_bool_rect _ _ _ f init ls)
                 | [ |- appcontext[?f _ (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
                   => simpl_setoid_rewrite (fun extra_arg init => @f_fold_right_bool_rect _ _ _ (fun k => f extra_arg k) init ls)
               end;
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
                 snd (of_string (take n (fold_right drop (to_string x) ms)))).
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
      { rewrite take_const, !of_to; reflexivity. }
      { rewrite !of_to; simpl; reflexivity. } }
    { pose proof (IHms n (of_string (drop a (to_string (x, y))))) as IHms'.
      rewrite to_of in IHms'.
      rewrite IHms'; clear IHms'.
      rewrite drop_const, !of_to; simpl.
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
        => let f' := constr:(fun const_str
                                 (a' : T0)
                                 (x : forall a'' : T0, R a'' a' -> T1 -> varT -> T2' a'')
                                 (y : T1)
                                 (z : varT)
                             => f a' (fun a'' rwf t1 str'
                                      => x a'' rwf t1 (snd (of_string str')))
                                  y (to_string (const_str, z))) in
           let vstr' := constr:(snd (of_string str)) in
           let f'h := fresh "f0" in
           let fh := fresh "f1" in
           set (f'h := f');
             set (fh := f);
             let GT := constr:(Fix
                                 wf
                                 (fun (a : T0) => T1 -> varT -> T2)
                                 (f'h (fst (of_string str)))
                                 v1 v2 vstr' v4 v5 v6
                               = Fix
                                   wf
                                   (fun (a : T0) => T1 -> String -> T2)
                                   fh
                                   v1 v2 str v4 v5 v6) in
             refine (_ : GT); change GT;
             let H := fresh in
             assert (H : forall a b vstr' d e f0,
                           Fix wf (fun (a : T0) => T1 -> varT -> T2) (f'h (fst (of_string str))) a b vstr' d e f0
                           = Fix wf (fun (a : T0) => T1 -> String -> T2) fh a b (to_string (fst (of_string str), vstr')) d e f0);
               [ let a := fresh in intro a; induction (wf a) as [?? IH]
               | specialize (fun a b => H a b (snd (of_string str)));
                 rewrite <- surjective_pairing in H;
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
                 => apply fold_right_f_eq_mor; [ intros ?? | | ]
               | [ |- (match ?x with _ => _ end) = (match ?x with _ => _ end) ]
                 => destruct x eqn:?
               | [ |- (match ?x with _ => _ end) _ _ _ _ = (match ?x with _ => _ end) _ _ _ _ ]
                 => destruct x eqn:?
               | [ H : fst (of_string _) = ?x |- context[?x] ] => rewrite <- H
               | [ |- fold_left _ _ _ = fold_left _ _ _ ]
                 => rewrite <- !fold_left_rev_right
               | [ |- rev _ = rev _ ]
                 => apply f_equal
               | [ |- map _ ?ls = map _ ?ls ]
                 => apply map_ext; intro
               | [ |- EqNat.beq_nat ?x ?y = EqNat.beq_nat ?x' ?y ]
                 => apply f_equal2
               | [ |- context[(fst ?x, snd ?x)] ]
                 => rewrite <- surjective_pairing
               | [ |- context[to_string (of_string _)] ]
                 => rewrite to_of
               | [ |- context[of_string (to_string _)] ]
                 => rewrite of_to
               | [ H : context[(fst ?x, snd ?x)] |- _ ]
                 => rewrite <- surjective_pairing in H
               | [ H : context[to_string (of_string _)] |- _ ]
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

Ltac solve_default_str_carrier :=
  match goal with |- str_carrier _ _ => idtac end;
  eapply str_carrier_default; hnf; simpl;
  match goal with |- { to_string : _ * _ -> string * _ & _ } => idtac end;
  let T := match goal with |- { to_string : _ * _ -> string * ?T & _ } => constr:T end in
  exists (fun x : string * T => x);
    exists (fun x : string * T => x);
    simpl;
    solve [ repeat split ].

Hint Extern 1 (str_carrier _ _) => solve_default_str_carrier : typeclass_instances.
