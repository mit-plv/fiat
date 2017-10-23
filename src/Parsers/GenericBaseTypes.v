(** * Definition of the generic part of the interface of the CFG parser *)
Require Import Coq.Strings.String.

Set Implicit Arguments.

Section recursive_descent_parser.
  Context {Char : Type}.

  Class generic_parser_dataT :=
    { parse_nt_T : Type;
      parse_item_T : Type;
      parse_production_T : Type;
      parse_productions_T : Type;
      ret_Terminal_false : Char -> parse_item_T;
      ret_Terminal_true : Char -> parse_item_T;
      ret_NonTerminal_false : String.string -> parse_item_T;
      ret_NonTerminal_true : String.string -> parse_nt_T -> parse_item_T;
      ret_production_cons : parse_item_T -> parse_production_T -> parse_production_T;
      ret_orb_production : parse_production_T -> parse_production_T -> parse_production_T;
      ret_orb_production_base : parse_production_T;
      ret_production_nil_true : parse_production_T;
      ret_production_nil_false : parse_production_T;
      ret_orb_productions : parse_production_T -> parse_productions_T -> parse_productions_T;
      ret_orb_productions_base : parse_productions_T;
      ret_nt : String.string -> parse_productions_T -> parse_nt_T;
      ret_nt_invalid : parse_nt_T }.
End recursive_descent_parser.

Arguments generic_parser_dataT : clear implicits.
