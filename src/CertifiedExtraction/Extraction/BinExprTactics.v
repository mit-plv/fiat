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

Ltac av_from_ext ext :=
  match type of ext with
  | StringMap.t (Value ?av) => constr:av
  end.

Ltac compile_binop facade_op lhs rhs ext :=
  let av := av_from_ext ext in
  let vlhs := find_fast (wrap (FacadeWrapper := FacadeWrapper_SCA (av := av)) lhs) ext in
  let vrhs := find_fast (wrap (FacadeWrapper := FacadeWrapper_SCA (av := av)) rhs) ext in
  lazymatch constr:(vlhs, vrhs) with
  | (Some ?vlhs, Some ?vrhs) =>
    apply (BinExpr.CompileBinopOrTest (var1 := vlhs) (var2 := vrhs) facade_op)
  | (Some ?vlhs, None) =>
    let vrhs := gensym "r" in
    apply (BinExpr.CompileBinopOrTest_left (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, Some ?vrhs) =>
    let vlhs := gensym "l" in
    apply (BinExpr.CompileBinopOrTest_right (var1 := vlhs) (var2 := vrhs) facade_op)
  | (None, None) =>
    let vlhs := gensym "l" in
    let vrhs := gensym "r" in
    apply (BinExpr.CompileBinopOrTest_full (var1 := vlhs) (var2 := vrhs) facade_op)
  end.
