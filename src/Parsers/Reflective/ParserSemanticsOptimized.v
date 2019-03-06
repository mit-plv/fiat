
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.ParserSemantics.
Require Import Fiat.Parsers.Reflective.SemanticsOptimized.
Set Implicit Arguments.

Module opt.
  Definition interp_has_parse_term {T}
    := Eval cbv [step_option_rec interp_has_parse_term'] in
        @interp_has_parse_term' T (@opt.interp_Term).
End opt.
Declare Reduction propt_red := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data opt.interp_has_parse_term].
Ltac propt_red := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data opt.interp_has_parse_term].
Ltac propt_red_in H := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data opt.interp_has_parse_term] in H.
