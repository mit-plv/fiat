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

  Local Instance boolean_gendata : generic_parser_dataT Char
    := { parse_nt_T := bool;
         parse_item_T := bool;
         parse_production_T := bool;
         parse_productions_T := bool;
         ret_Terminal_false ch := false;
         ret_Terminal_true ch := true;
         ret_NonTerminal_false nt := false;
         ret_NonTerminal_true nt pnt := pnt;
         ret_production_cons := andb;
         ret_orb_production := orb;
         ret_orb_production_base := false;
         ret_production_nil_true := true;
         ret_production_nil_false := false;
         ret_orb_productions := orb;
         ret_orb_productions_base := false;
         ret_nt nt b := b;
         ret_nt_invalid := false }.

  Definition parse_item'
    := parse_item' str.

  Definition parse_production'_for {len0}
    := parse_production'_for str (len0 := len0).

  Definition parse_production' {len0}
    := parse_production' str (len0 := len0).

  Definition parse_productions' {len0}
    := parse_productions' str (len0 := len0).

  Definition parse_nonterminal_step {len0 valid_len}
    := parse_nonterminal_step str (len0 := len0) (valid_len := valid_len).

  Definition parse_nonterminal_or_abort
    : forall (p : nat * nat)
             (valid : nonterminals_listT)
             (offset : nat) (len : nat),
      len <= fst p
      -> nonterminal_carrierT
      -> bool
    := parse_nonterminal_or_abort str.

  Definition parse_nonterminal'
             (nt : nonterminal_carrierT)
    : bool
    := parse_nonterminal' str nt.

  Definition parse_nonterminal
             (nt : String.string)
    : bool
    := parse_nonterminal str nt.

  Definition parse_item
             (it : item Char)
    : bool
    := parse_item str it.

  Definition parse_production
             (pat : production_carrierT)
    : bool
    := parse_production str pat.

  Definition parse_productions
             (pats : list production_carrierT)
    : bool
    := parse_productions str pats.
End recursive_descent_parser.
