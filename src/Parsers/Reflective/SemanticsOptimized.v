Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.List.Operations.
Set Implicit Arguments.

Local Open Scope list_scope.

Module opt.
  Definition map {A B} := Eval cbv [List.map] in @List.map A B.
  Definition fold_left {A B} := Eval cbv [List.fold_left] in @List.fold_left A B.
  Definition nth' {A} := Eval cbv [nth'] in @List.nth' A.

  Definition interp_RLiteralTerm {T} (t : RLiteralTerm T) : interp_TypeCode T
    := Eval cbv [interp_RLiteralTerm] in
        match t with
        | RLC t'
          => interp_RLiteralTerm (RLC t')
        | RLNC t'
          => match t' in (RLiteralNonConstructor T') return interp_TypeCode T' with
             | Rnth' _ => nth'
             | Rmap _ _ => @map _ _
             | Rfold_left _ _ => @fold_left _ _
             | t'' => interp_RLiteralTerm (RLNC t'')
             end
        end.

  Fixpoint interp_Term {T} (t : Term interp_TypeCode T) : interp_TypeCode T
    := match t in (Term _ T') return interp_TypeCode T' with
       | RVar T v => v
       | RLambda A B f => fun x => @interp_Term _ (f x)
       | RApp A B f x => @interp_Term _ f (@interp_Term _ x)
       | RLiteralApp c t args => interp_args_for (interp_RLiteralTerm t) args
       end
  with interp_args_for {T} (f : interp_TypeCode T)
                       (args : args_for interp_TypeCode T)
       : interp_TypeCode (range_of T)
       := match args in args_for _ T return interp_TypeCode T -> interp_TypeCode (range_of T) with
          | an_arg A B arg args => fun f => @interp_args_for _ (f (@interp_Term _ arg)) args
          | noargs T => fun f => f
          end f.
End opt.

Declare Reduction ropt_red := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_args_for opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data].
Ltac ropt_red := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_args_for opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data].
Ltac ropt_red_in H := cbv [opt.map opt.fold_left opt.nth' opt.interp_RLiteralTerm opt.interp_args_for opt.interp_Term interp_TypeCode interp_SimpleTypeCode interp_SimpleTypeCode_step Reflective.interp_RCharExpr Reflective.irbeq Reflective.ascii_interp_RCharExpr_data] in H.
