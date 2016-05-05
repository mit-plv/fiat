Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.SemanticsOptimized.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.List.Operations.
Set Implicit Arguments.

Module opt.
  Definition interp_has_parse_term
             (is_valid_nonterminal : list nat -> nat -> bool)
             (strlen : nat)
             (char_at_matches : nat -> (Ascii.ascii -> bool) -> bool)
             (split_string_for_production : nat * (nat * nat) -> nat -> nat -> list nat)
             (t : has_parse_term interp_TypeCode) : bool
    := Eval cbv [step_option_rec] in
        match t with
        | RFix2 G_length up_to_G_length f valid_len valids nt_idx
          => Wf2.Fix2
               (Wf.well_founded_prod_relation Wf_nat.lt_wf Wf_nat.lt_wf)
               (fun aa' : nat * nat =>
                  list nat -> nat -> forall a1 : nat, a1 <= fst aa' -> nat -> bool)
               (fun (len0 valid_len0 : nat)
                    (parse_nt : forall len0' valid_len : nat,
                        Wf.prod_relation lt lt (len0', valid_len) (len0, valid_len0) ->
                        list nat -> nat -> forall len : nat, len <= len0' -> nat -> bool)
                    (valids : list nat) (offset len : nat)
                    (pf : len <= len0)
                    (nt : nat)
                => option_rect
                     (fun _ => bool)
                     (fun parse_nt
                      => opt.interp_Term
                           f
                           (fun n => char_at_matches n (*str*))
                           (fun n => split_string_for_production n (*str*))
                           len0 valid_len parse_nt valids offset len nt)
                     false
                     (@step_option_rec is_valid_nonterminal len0 valid_len0 parse_nt G_length up_to_G_length valids offset len nt))
               strlen
               valid_len
               valids
               0
               strlen
               (le_n _)
               nt_idx
        end.
End opt.
Declare Reduction propt_red := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_args_for opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data opt.interp_has_parse_term].
Ltac propt_red := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_args_for opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data opt.interp_has_parse_term].
Ltac propt_red_in H := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_args_for opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data opt.interp_has_parse_term] in H.
