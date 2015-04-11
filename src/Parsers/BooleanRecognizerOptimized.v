(** * Definition of a boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarNotations.
Require Import ADTSynthesis.Parsers.BaseTypes ADTSynthesis.Parsers.BooleanBaseTypes.
Require Import ADTSynthesis.Parsers.StringLike.Properties.
Require Import ADTSynthesis.Common ADTSynthesis.Common.Wf.
Require Import ADTSynthesis.Parsers.BooleanRecognizer.
Require Import ADTSynthesis.Common.Match.
Require Import ADTSynthesis.Common.List.ListFacts.
Require Import ADTSynthesis.Common.Equality.
Require Export ADTSynthesis.Common.SetoidInstances.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Global Arguments string_dec : simpl never.
Global Arguments string_beq : simpl never.
Global Arguments parse_production _ _ _ _ _ _ _ _ !_.

Lemma parse_production_respectful {Char HSL HSLP predata A B}
      {f g : forall (a : _ * A) (b : B a) (str : @String Char HSL), str ≤s (fst a) -> String.string -> bool}
      (H : forall a b c d e, f a b c d e = g a b c d e)
      str0 a b str pf
: pointwise_relation
    _ eq
    (@parse_production Char HSL HSLP predata str0 (f (str0, a) b) str pf)
    (@parse_production Char HSL HSLP predata str0 (g (str0, a) b) str pf).
Proof.
  intro ls.
  revert str0 a b str pf; induction ls; simpl; trivial; intros.
  setoid_rewrite IHls.
  f_equal.
  apply map_Proper_eq; trivial; repeat intro.
  f_equal.
  unfold parse_item.
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
  Local Notation G := (list_to_grammar (nil::nil) ls) (only parsing).

  Definition parse_nonterminal_opt
             (str : String)
             (nt : String.string)
  : { b : bool | b = parse_nonterminal (G := G) str nt }.
  Proof.
    let G := match goal with |- context[_ = parse_nonterminal (G := ?G) _ _] => constr:G end in
    let G' := head G in
    try unfold G';
      cbv beta iota zeta delta [parse_nonterminal parse_nonterminal_or_abort parse_nonterminal_step parse_productions parse_item Lookup list_to_grammar list_to_productions];
      simpl;
      eexists;
      let L := match goal with |- ?L = _ => constr:L end in
      let e := fresh "e" in
      let e' := fresh "e" in
      let pp := fresh "pp" in
      set (e := L);
        etransitivity;
        [
        | match goal with
            | [ |- _ = @Fix ?A ?R ?Rwf (fun a : ?A => forall (b :@?B a) (c : @?C a b) (d : @?D a b c), @?P a b c d) ?f ?a ?b ?c ?d ]
              => refine ((fun H => @Fix3_Proper_eq A B C D R Rwf P _ f H a b c d) _)
          end;
          unfold forall_relation, pointwise_relation, respectful;
          let H' := fresh in
          (intros ??? H' ???);
            let L := match goal with |- ?L = ?R => constr:L end in
            let R := match goal with |- ?L = ?R => constr:R end in
            set (e' := L);
              let R' := match type of H' with
                          | forall a0 a1 a2 a3 a4, ?x a0 a1 a2 a3 a4 = ?y a0 a1 a2 a3 a4
                            => let Rp := (eval pattern y in R) in
                               match Rp with
                                 | ?R' y => (eval cbv beta in (R' x))
                               end
                        end in
              transitivity R';
                [ clear H';
                  match goal with
                    | [ |- appcontext[@parse_production ?a ?b ?c ?d ?e ?f ?g ?h] ]
                      => set (pp := @parse_production a b c d e f g h)
                  end
                | clear -H'; unfold sumbool_rect;
                  repeat match goal with
                           | _ => reflexivity
                           | [ |- appcontext[match ?e with left _ => _ | right _ => _ end] ]
                             => destruct e
                         end;
                  setoid_rewrite (parse_production_respectful H');
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
                 end;
          subst pp; simpl;
          subst e'; instantiate; reflexivity ];
        cbv beta iota zeta delta [bool_rect sumbool_rect];
        subst e; instantiate.
    reflexivity.
  Defined.
End recursive_descent_parser.
