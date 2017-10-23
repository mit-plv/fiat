(** * Some simple examples with the boolean-returning CFG parser-recognizer *)
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Compare_dec Coq.Arith.Wf_nat.
Require Import Fiat.Parsers.Grammars.Trivial Fiat.Parsers.Grammars.ABStar.
Require Import Fiat.Parsers.Splitters.RDPList Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.BooleanRecognizer.
Require Import Fiat.Parsers.BooleanRecognizerFull.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Module example_parse_empty_grammar.
  Definition parse : string -> bool
    := brute_force_parse trivial_grammar.

  Time Compute parse "".
  Check eq_refl : true = parse "".
  Time Compute parse "a".
  Check eq_refl : false = parse "a".
  Time Compute parse "aa".
  Check eq_refl : false = parse "aa".
End example_parse_empty_grammar.

Section examples.
  Section ab_star.
    Local Open Scope string_scope.

    Definition parse : string -> bool
      := brute_force_parse ab_star_grammar.

    Time Eval lazy in parse "".
    Check eq_refl : parse "" = true.
    Time Eval lazy in parse "a".
    Check eq_refl : parse "a" = false.
    Time Eval lazy in parse "ab".
    Check eq_refl : parse "ab" = true.
    Time Eval lazy in parse "aa".
    Check eq_refl : parse "aa" = false.
    Time Eval lazy in parse "ba".
    Check eq_refl : parse "ba" = false.
    Time Eval lazy in parse "aba".
    Check eq_refl : parse "aba" = false.
    Time Eval lazy in parse "abab".
    Time Eval lazy in parse "ababab".
    Check eq_refl : parse "ababab" = true.
  (* For debugging: *)(*
    Goal True.
    pose proof (eq_refl (parse "")) as s.
    unfold parse in s.
    unfold brute_force_parse, brute_force_parse_nonterminal in s.
    cbv beta zeta delta [parse_nonterminal] in s.
    cbv beta zeta delta [parse_nonterminal_or_abort] in s.
    rewrite Fix3_eq in s.
    Ltac do_compute_in c H :=
      let c' := fresh in
      set (c' := c) in H;
        compute in c';
        subst c'.
    Tactic Notation "do_compute" open_constr(c) "in" ident(H) :=
      match type of H with
        | context[?c0] => unify c c0
      end;
      do_compute_in c H.
    cbv beta zeta delta [parse_nonterminal_step] in s.
    change (fst (?a, ?b)) with a in s.
    change (snd (?a, ?b)) with b in s.
    unfold split_stateT, brute_force_data, default_string_with_no_state, default_String_with_no_state in s.
    repeat change (string_val {| string_val := ?x |}) with x in s.
    do_compute_in (Start_symbol ab_star_grammar) s.
    do_compute_in (@Length Ascii.ascii string_stringlike "ab_star") s.
    do_compute (lt_dec _ _) in s.
    cbv beta iota zeta in s.
    unfold is_valid_nonterminal, initial_nonterminals_data in s.
    do_compute (is_valid_nonterminal initial_nonterminals_data "") in s.
    set (n := @Length Ascii.ascii string_stringlike ab_star_grammar) in s.
    pose ((Length ab_star_grammar)).
    do_compute_in (Length ab_star_grammar) s.
    do_compute_in (lt_dec (Length ab_star_grammar) (Length string_stringlike "abab"%string)) s.
    change (if in_right then ?x else ?y) with y in s.
    cbv beta zeta delta [rdp_list_is_valid_nonterminal] in s.*)
  End ab_star.
End examples.
