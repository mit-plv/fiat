(** * Definition of a simple_parse_of-returning CFG parser-recognizer *)
(** * Definition of a boolean-returning CFG parser-recognizer *)

Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.GenericRecognizer.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}.
  Context (str : String).

  Local Notation simple_parse_of := (@simple_parse_of Char) (only parsing).
  Local Notation simple_parse_of_production := (@simple_parse_of_production Char) (only parsing).

  Definition option_SimpleParseProductionCons
    : option simple_parse_of_item
      -> option simple_parse_of_production
      -> option simple_parse_of_production
    := fun pit pits
       => match pit, pits with
          | Some pit', Some pits' => Some (SimpleParseProductionCons pit' pits')
          | None, _ => None
          | _, None => None
          end.

  Definition option_orb {A} (x y : option A) : option A
    := match x, y with
       | Some x', _ => Some x'
       | None, Some y' => Some y'
       | None, None => None
       end.

  Definition option_simple_parse_of_orb
             (x : option simple_parse_of_production)
             (xs : option simple_parse_of)
    : option simple_parse_of
    := match x, xs with
       | Some x', _ => Some (SimpleParseHead x')
       | None, Some xs' => Some (SimpleParseTail xs')
       | None, None => None
       end.

  Local Instance simple_gendata : generic_parser_dataT Char
    := { parse_nt_T := option simple_parse_of;
         parse_item_T := option simple_parse_of_item;
         parse_production_T := option simple_parse_of_production;
         parse_productions_T := option simple_parse_of;
         ret_Terminal_false ch := None;
         ret_Terminal_true ch := Some (SimpleParseTerminal ch);
         ret_NonTerminal_false nt := None;
         ret_NonTerminal_true nt := option_map (SimpleParseNonTerminal nt);
         ret_production_cons := option_SimpleParseProductionCons;
         ret_orb_production := option_orb;
         ret_orb_production_base := None;
         ret_production_nil_true := Some SimpleParseProductionNil;
         ret_production_nil_false := None;
         ret_orb_productions := option_simple_parse_of_orb;
         ret_orb_productions_base := None;
         ret_nt nt b := b;
         ret_nt_invalid := None }.

  Definition parse_item'
    := Eval cbv [parse_item' parse_nt_T parse_item_T parse_production_T simple_gendata] in
        parse_item' str.

  Definition parse_production'_for {len0}
    := Eval cbv [parse_production'_for parse_nt_T simple_gendata parse_production_T] in
        parse_production'_for str (len0 := len0).

  Definition parse_production' {len0}
    := Eval cbv [parse_production' parse_nt_T simple_gendata parse_production_T] in
        parse_production' str (len0 := len0).

  Definition parse_productions' {len0}
    := Eval cbv [parse_productions' parse_nt_T simple_gendata parse_production_T] in
        parse_productions' str (len0 := len0).

  Definition parse_nonterminal_step {len0 valid_len}
    := Eval cbv [parse_nonterminal_step parse_nt_T simple_gendata parse_production_T] in
        parse_nonterminal_step str (len0 := len0) (valid_len := valid_len).

  Definition parse_nonterminal_or_abort
    : forall (p : nat * nat)
             (valid : nonterminals_listT)
             (offset : nat) (len : nat),
      len <= fst p
      -> nonterminal_carrierT
      -> option simple_parse_of
    := parse_nonterminal_or_abort str.

  Definition parse_nonterminal'
             (nt : nonterminal_carrierT)
    : option simple_parse_of
    := parse_nonterminal' str nt.

  Definition parse_nonterminal
             (nt : String.string)
    : option simple_parse_of
    := parse_nonterminal str nt.

  Definition parse_item
             (it : item Char)
    : option simple_parse_of_item
    := parse_item str it.

  Definition parse_production
             (pat : production_carrierT)
    : option simple_parse_of_production
    := parse_production str pat.

  Definition parse_productions
             (pats : list production_carrierT)
    : option simple_parse_of
    := parse_productions str pats.
End recursive_descent_parser.
