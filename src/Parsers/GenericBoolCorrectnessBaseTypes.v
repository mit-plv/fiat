(** * Definition of the generic part of the interface of the correctness proof of the CFG parser *)

Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.GenericBaseTypes.
Require Import Fiat.Parsers.BaseTypes.

Set Implicit Arguments.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {predata : @parser_computational_predataT Char}
          {gendata : @generic_parser_dataT Char}.

  Class generic_parser_decidable_data {gendata : @generic_parser_dataT Char} :=
    {
      parse_nt_T_to_bool : parse_nt_T -> bool;
      parse_item_T_to_bool : parse_item_T -> bool;
      parse_production_T_to_bool : parse_production_T -> bool;
      parse_productions_T_to_bool : parse_productions_T -> bool
    }.

  Class generic_parser_decidable_correctness_data {gendata : @generic_parser_dataT Char} {gddata : generic_parser_decidable_data} :=
    {
      ret_Terminal_true_to_bool
      : forall ch, parse_item_T_to_bool (ret_Terminal_true ch) = true;
      ret_Terminal_false_to_bool
      : forall ch, parse_item_T_to_bool (ret_Terminal_false ch) = false;
      ret_NonTerminal_true_to_bool
      : forall nt rv, parse_item_T_to_bool (ret_NonTerminal_true nt rv) = parse_nt_T_to_bool rv;
      ret_NonTerminal_false_to_bool
      : forall nt, parse_item_T_to_bool (ret_NonTerminal_false nt) = false;
      ret_production_nil_true_to_bool
      : parse_production_T_to_bool ret_production_nil_true = true;
      ret_production_nil_false_to_bool
      : parse_production_T_to_bool ret_production_nil_false = false;
      ret_orb_production_base_to_bool
      : parse_production_T_to_bool ret_orb_production_base = false;
      ret_orb_production_to_bool
      : forall rv1 rv2, parse_production_T_to_bool (ret_orb_production rv1 rv2)
                        = orb (parse_production_T_to_bool rv1) (parse_production_T_to_bool rv2);
      ret_production_cons_to_bool
      : forall rv1 rv2, parse_production_T_to_bool (ret_production_cons rv1 rv2)
                        = andb (parse_item_T_to_bool rv1) (parse_production_T_to_bool rv2);
      ret_orb_productions_base_to_bool
      : parse_productions_T_to_bool ret_orb_productions_base = false;
      ret_orb_productions_to_bool
      : forall rv1 rv2, parse_productions_T_to_bool (ret_orb_productions rv1 rv2)
                        = orb (parse_production_T_to_bool rv1) (parse_productions_T_to_bool rv2);
      ret_nt_to_bool
      : forall nt v, parse_nt_T_to_bool (ret_nt nt v) = parse_productions_T_to_bool v;
      ret_nt_invalid_to_bool
      : parse_nt_T_to_bool ret_nt_invalid = false
    }.
End correctness.

Create HintDb generic_parser_decidable_correctness discriminated.
Hint Rewrite @ret_Terminal_true_to_bool @ret_Terminal_false_to_bool @ret_NonTerminal_true_to_bool @ret_NonTerminal_false_to_bool @ret_production_nil_true_to_bool @ret_production_nil_false_to_bool @ret_orb_production_base_to_bool @ret_orb_production_to_bool @ret_production_cons_to_bool @ret_orb_productions_base_to_bool @ret_orb_productions_to_bool @ret_nt_to_bool @ret_nt_invalid_to_bool : generic_parser_decidable_correctness.

Lemma fold_right_ret_orb_production_eq
      {Char}
      {gendata : @generic_parser_dataT Char}
      {gddata : generic_parser_decidable_data}
      {gdcdata : generic_parser_decidable_correctness_data}
      ls b
  : parse_production_T_to_bool (List.fold_right ret_orb_production b ls)
    = List.fold_right orb (parse_production_T_to_bool b) (List.map parse_production_T_to_bool ls).
Proof.
  revert b; induction ls as [|?? IHls]; simpl; trivial; intros; [].
  rewrite <- IHls; clear IHls.
  autorewrite with generic_parser_decidable_correctness; trivial.
Qed.

Lemma fold_right_ret_orb_productions_eq
      {Char}
      {gendata : @generic_parser_dataT Char}
      {gddata : generic_parser_decidable_data}
      {gdcdata : generic_parser_decidable_correctness_data}
      ls b
  : parse_productions_T_to_bool (List.fold_right ret_orb_productions b ls)
    = List.fold_right orb (parse_productions_T_to_bool b) (List.map parse_production_T_to_bool ls).
Proof.
  revert b; induction ls as [|?? IHls]; simpl; trivial; intros; [].
  rewrite <- IHls; clear IHls.
  autorewrite with generic_parser_decidable_correctness; trivial.
Qed.

Hint Rewrite @fold_right_ret_orb_production_eq @fold_right_ret_orb_productions_eq : generic_parser_decidable_correctness.
