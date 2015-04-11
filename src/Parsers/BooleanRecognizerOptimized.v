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

Ltac Fix3_setoid_rewrite H :=
  etransitivity;
  [ try clear H
  | match goal with
      | [ |- _ = @Fix ?A ?R ?Rwf (fun a : ?A => forall (b :@?B a) (c : @?C a b) (d : @?D a b c), @?P a b c d) ?f ?a ?b ?c ?d ]
        => refine ((fun H => @Fix3_Proper_eq A B C D R Rwf P _ f H a b c d) _)
    end;
    unfold forall_relation, pointwise_relation, respectful;
    let H' := fresh in
    (intros ??? H' ???);
      let L := match goal with |- ?L = _ => constr:L end in
      let e := fresh "e" in
      set (e := L);
        setoid_rewrite <- (parse_production_respectful H');
        setoid_rewrite H; try clear H;
        subst e;
        reflexivity ].

Ltac extract_parser_opt :=
  eexists;
  let L := match goal with |- ?L = _ => constr:L end in
  let e := fresh "e" in
  set (e := L);
  let G := match goal with |- _ = parse_nonterminal (G := ?G) _ _ => constr:G end in
  let G' := head G in
  try unfold G';
    cbv beta iota zeta delta [parse_nonterminal parse_nonterminal_or_abort parse_nonterminal_step parse_productions parse_item Lookup list_to_grammar list_to_productions];
    simpl;
    repeat Fix3_setoid_rewrite (fun ls => eq_sym (@fold_symmetric _ orb Bool.orb_assoc Bool.orb_comm false ls));
    repeat
      (let H0 := fresh "H0" in
       match goal with
         | [ |- context[fold_right ?f ?i (map _ (bool_rect _ ?x ?y (string_beq ?s _)))] ]
           => (pose proof (fun g s' => @pull_bool_rect _ _ (fun ls => fold_right f i (map g ls)) x y (string_beq s s')) as H0;
               simpl in H0;
               Fix3_setoid_rewrite H0)
         | [ |- appcontext[fold_right (fun str_t else_case s => bool_rect (fun _ => ?T) (@?a str_t) (else_case s) (@?b str_t s))] ]
           => (pose proof (@fold_right_fun _ _ _ (fun str_t else_cases s => bool_rect (fun _ => T) (a str_t) else_cases (b str_t s))) as H0;
               simpl in H0;
               Fix3_setoid_rewrite H0)
         | [ |- context[@map _ ?B _ (fold_right (fun x acc => bool_rect (fun _ => _) (@?a x) acc _) ?init ?ls)] ]
           => (pose proof (fun b' f => @f_fold_right_bool_rect _ (list B) _ (map f) init ls a b') as H0;
               simpl in H0;
               Fix3_setoid_rewrite H0)
         | [ |- appcontext[?f (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls) ?x] ]
           => (pose proof (fun init => @f_fold_right_bool_rect _ _ _ (fun k => f k x) init ls) as H0;
               simpl in H0;
               Fix3_setoid_rewrite H0)
         | [ |- appcontext[?f (fold_right (fun x acc => bool_rect (fun _ => _) _ acc _) _ ?ls)] ]
           => (pose proof (fun init => @f_fold_right_bool_rect _ _ _ f init ls) as H0;
               simpl in H0;
               Fix3_setoid_rewrite H0)
       end;
       instantiate;
       simpl);
    repeat Fix3_setoid_rewrite Bool.orb_false_r;
    subst e;
    cbv beta iota zeta delta [bool_rect sumbool_rect];
    reflexivity.

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
    extract_parser_opt.
  Defined.
End recursive_descent_parser.
