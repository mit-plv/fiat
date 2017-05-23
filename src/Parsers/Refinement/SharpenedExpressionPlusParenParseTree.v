(** Sharpened ADT for #, +, () *)
Require Import Fiat.Parsers.Grammars.ExpressionNumPlusParen.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.ActionEvaluator.
Require Import Fiat.Parsers.Refinement.SharpenedExpressionPlusParen.
Require Import Fiat.Parsers.Grammars.EvalGrammarTactics.

Definition parser_informative_opaque (str : Coq.Strings.String.string)
  : option (parse_of_item plus_expr_grammar str (NonTerminal (Start_symbol plus_expr_grammar))).
Proof.
  Time make_parser_informative_opaque ComputationalSplitter.
Defined.

Definition parser_informative (str : Coq.Strings.String.string)
  : option (@simple_parse_of_item Ascii.ascii).
Proof.
  Time make_parser_informative ComputationalSplitter.
Defined.

Definition parser_eval (str : Coq.Strings.String.string)
  : option nat.
Proof.
  refine match parser_informative str with
         | Some (SimpleParseNonTerminal nt pt)
           => option_map (fun d : digits => d : nat)
                         (evaluate_item plus_expr_pregrammar_with_actions (SimpleParseNonTerminal nt pt))
         | Some (SimpleParseTerminal _) => None
         | None => None
         end.
Defined.

Check let n := 3 in eq_refl (Some n) <: parser_eval "(1+1)+1" = Some n.
Check let n := 5 in eq_refl (Some n) <: parser_eval "((1+1)+(1+1))+1" = Some n.
Check let n := 55 in eq_refl (Some n) <: parser_eval "(((((55)))))" = Some n.
