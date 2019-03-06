Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Semantics.
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

  Definition interp_Term {T} (t : Term interp_TypeCode T) : interp_TypeCode T
    := interp_Term_gen (@interp_RLiteralTerm) t.
End opt.
