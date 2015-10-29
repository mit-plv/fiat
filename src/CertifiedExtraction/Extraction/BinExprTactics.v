Require Import
        CertifiedExtraction.Extraction.Core
        CertifiedExtraction.Extraction.BinExpr.

Ltac translate_op gallina_op :=
  let hd := head_constant gallina_op in
  match hd with
  | @Word.wplus => constr:(@inl IL.binop IL.test IL.Plus)
  | @Word.wminus => constr:(@inl IL.binop IL.test IL.Minus)
  | @Word.wmult => constr:(@inl IL.binop IL.test IL.Times)
  | @Word.weqb => constr:(@inr IL.binop IL.test IL.Eq)
  | @IL.weqb => constr:(@inr IL.binop IL.test IL.Eq)
  | @IL.wneb => constr:(@inr IL.binop IL.test IL.Ne)
  | @IL.wltb => constr:(@inr IL.binop IL.test IL.Lt)
  | @IL.wleb => constr:(@inr IL.binop IL.test IL.Le)
  | @Word.wlt_dec => constr:(@inr IL.binop IL.test IL.Lt)
  | _ => fail 1 "Unknown operator" gallina_op
  end.

Ltac compile_binop av facade_op lhs rhs ext :=
  let vlhs := find_fast (SCA av lhs) ext in
  let vrhs := find_fast (SCA av rhs) ext in
  lazymatch constr:(vlhs, vrhs) with
  | (Some ?vlhs, Some ?vrhs) =>
    apply (CompileBinopOrTest (var1 := vlhs) (var2 := vrhs) facade_op)
  | (Some ?vlhs, None) =>
    let vrhs := gensym "r" in
    apply (CompileBinopOrTest_left (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, Some ?vrhs) =>
    let vlhs := gensym "l" in
    apply (CompileBinopOrTest_right (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, None) =>
    let vlhs := gensym "l" in
    let vrhs := gensym "r" in
    apply (CompileBinopOrTest_full (var1 := vlhs) (var2 := vrhs) facade_op)
  end.
