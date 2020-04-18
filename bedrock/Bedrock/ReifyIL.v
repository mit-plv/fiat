Require Import Coq.Lists.List.
Require Import Bedrock.IL.
Require Import Bedrock.ReifyExpr.
Require Import Bedrock.SymIL.

(* Reify the instructions *)
Ltac collectTypes_loc isConst l Ts k :=
  match l with
    | Reg _ => k Ts
    | Imm ?i => ReifyExpr.collectTypes_expr isConst i Ts k
    | Indir _ ?i => ReifyExpr.collectTypes_expr isConst i Ts k
  end.
Ltac reify_loc isConst l types funcs uvars vars k :=
  match l with
    | Reg ?r =>
      let res := constr:(@SymReg types r) in
        k uvars funcs res
    | Imm ?i =>
      ReifyExpr.reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymImm types i) in k uvars funcs l)
    | Indir ?r ?i =>
      ReifyExpr.reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymIndir types r i) in k uvars funcs l)
  end.

Ltac collectTypes_lvalue isConst l Ts k :=
  match l with
    | LvReg _ => k Ts
    | LvMem ?l => collectTypes_loc isConst l Ts k
    | LvMem8 ?l => collectTypes_loc isConst l Ts k
  end.

Ltac reify_lvalue isConst l types funcs uvars vars k :=
  match l with
    | LvReg ?r => let l := constr:(@SymLvReg types r) in k uvars funcs l
    | LvMem ?l =>
      reify_loc isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymLvMem types l) in k uvars funcs l)
    | LvMem8 ?l =>
      reify_loc isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymLvMem8 types l) in k uvars funcs l)
  end.

Ltac collectTypes_rvalue isConst r Ts k :=
  match r with
    | RvLval ?l => collectTypes_lvalue isConst l Ts k
    | RvImm ?i => ReifyExpr.collectTypes_expr isConst i Ts k
    | RvLabel _ => let Ts := Reflect.cons_uniq label Ts in k Ts
  end.

Ltac reify_rvalue isConst r types funcs uvars vars k :=
  match r with
    | RvLval ?l =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        let l := constr:(@SymRvLval types l) in k uvars funcs l)
    | RvImm ?i =>
      ReifyExpr.reify_expr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        let l := constr:(@SymRvImm types i) in k uvars funcs l)
    | RvLabel ?l =>
      let r := constr:(@SymRvLabel types l) in k uvars funcs r
  end.

Ltac collectTypes_instr isConst i Ts k :=
  match i with
    | Assign ?l ?r =>
      collectTypes_lvalue isConst l Ts ltac:(fun Ts =>
        collectTypes_rvalue isConst r Ts k)
    | Binop ?l ?r1 _ ?r2 =>
      collectTypes_lvalue isConst l Ts ltac:(fun Ts =>
        collectTypes_rvalue isConst r1 Ts ltac:(fun Ts =>
          collectTypes_rvalue isConst r2 Ts k ))
  end.
Ltac reify_instr isConst i types funcs uvars vars k :=
  match i with
    | Assign ?l ?r =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        reify_rvalue isConst r types funcs uvars vars ltac:(fun uvars funcs r =>
          let res := constr:(@SymAssign types l r) in k uvars funcs res))
    | Binop ?l ?r1 ?o ?r2 =>
      reify_lvalue isConst l types funcs uvars vars ltac:(fun uvars funcs l =>
        reify_rvalue isConst r1 types funcs uvars vars ltac:(fun uvars funcs r1 =>
          reify_rvalue isConst r2 types funcs uvars vars ltac:(fun uvars funcs r2 =>
            let res := constr:(@SymBinop types l r1 o r2) in k uvars funcs res)))
  end.

Ltac collectTypes_instrs isConst is Ts k :=
  match is with
    | nil => k Ts
    | ?i :: ?is =>
      collectTypes_instr isConst i Ts ltac:(fun Ts =>
        collectTypes_instrs isConst is Ts k)
  end.
Ltac reify_instrs isConst is types funcs uvars vars k :=
  match is with
    | nil =>
      let is := constr:(@nil (sym_instr types)) in k uvars funcs is
    | ?i :: ?is =>
      reify_instr isConst i types funcs uvars vars ltac:(fun uvars funcs i =>
        reify_instrs isConst is types funcs uvars vars ltac:(fun uvars funcs is =>
          let res := constr:(i :: is) in k uvars funcs res))
  end.
