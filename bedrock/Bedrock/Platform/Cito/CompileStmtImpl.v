Set Implicit Arguments.

Section Body.

  Require Import Bedrock.Platform.AutoSep.
  Variable vars : list string.

  Variable temp_size : nat.

  Variable imports : LabelMap.t assert.

  Variable imports_global : importsGlobal imports.

  Variable modName : string.

  Require Import Bedrock.Platform.Cito.SemanticsExpr.

  Definition stack_slot n := LvMem (Sp + (4 * n)%nat)%loc.
  Definition vars_start := 4 * 2.
  Definition var_slot x := LvMem (Sp + (vars_start + variablePosition vars x)%nat)%loc.
  Definition temp_start := vars_start + 4 * length vars.
  Definition temp_slot n := LvMem (Sp + (temp_start + 4 * n)%nat)%loc.
  Definition frame_len := temp_start + 4 * temp_size.
  Definition frame_len_w := natToW frame_len.
  Definition callee_stack_start := frame_len.
  Definition callee_stack_slot n := LvMem (Sp + (callee_stack_start + 4 * n)%nat)%loc.

  Definition Seq2 := @Seq_ _ imports_global modName.

  Definition Strline := Straightline_ imports modName.

  Definition Skip__ := Skip_ imports modName.

  Definition If__ := Structured.If_ imports_global.

  Definition While__ := Structured.While_ imports_global.

  Fixpoint Seq__ ls :=
    match ls with
      | nil => Skip__
      | a :: ls' => Seq2 a (Seq__ ls')
    end.

  Definition SaveRv lv := Strline (IL.Assign lv (RvLval (LvReg Rv)) :: nil).

  Definition CheckExtraStack (n : nat) cmd :=
    Seq2
      (Strline (IL.Assign Rv (stack_slot 1) :: nil))
      (Structured.If_ imports_global n Le Rv cmd
                      (Diverge_ imports modName)).

  Require Bedrock.Platform.Cito.SaveRet.
  Local Open Scope nat.

  Require Import Bedrock.Platform.Cito.ConvertLabel.
  Import Syntax.
  Variable loop_inv : Expr -> Stmt -> Stmt -> assert.
  Variable after_call : option string -> Stmt -> assert.
  Variable compile_expr : Expr -> nat -> cmd imports modName.
  Variable compile_exprs : list Expr -> nat -> nat -> cmd imports modName.

  Fixpoint cmp (s k : Stmt) : cmd imports modName :=
    match s with
      | Syntax.Skip =>
        Skip__
      | Syntax.Seq a b =>
        Seq2 (cmp a (Syntax.Seq b k))
             (cmp b k)
      | Syntax.If cond t f =>
        Seq2 (compile_expr cond 0)
             (If__ Rv Ne (natToW 0) (cmp t k) (cmp f k))
      | Syntax.While cond body =>
        Seq2 (compile_expr cond 0)
             (While__ (loop_inv cond body k) Rv Ne (natToW 0)
                      (Seq2 (cmp body (Syntax.Seq (Syntax.While cond body) k))
                            (compile_expr cond 0)))
      | Syntax.Call var f args =>
        let callee_frame_len := 2 + length args in
        CheckExtraStack
          callee_frame_len
          (Seq__
             (compile_exprs
                args 0 (callee_stack_start + 8)
                :: compile_expr f 0
                :: Strline
                (IL.Binop
                   (callee_stack_slot 1) (stack_slot 1) Minus callee_frame_len
                   :: IL.Binop Sp Sp Plus frame_len_w :: nil)
                :: Structured.ICall_ imports modName Rv (after_call var k)
                :: Strline (IL.Binop Sp Sp Minus frame_len_w :: nil)
                :: SaveRet.compile vars var imports_global modName :: nil))
      | Syntax.Label x lbl =>
        Strline (IL.Assign (var_slot x) lbl :: nil)
      | Syntax.Assign x e =>
        Seq2 (compile_expr e 0)
             (SaveRv (var_slot x))
    end.

End Body.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.Inv.
  Module Import InvMake := Make E.
  Import SemanticsMake.
  Module Import InvMake2 := Make M.

  Section TopSection.

    Variable vars : list string.

    Variable temp_size : nat.

    Variable rv_postcond : W -> vals -> Prop.

    Definition loop_inv cond body k : assert :=
      let s := Syntax.Seq (Syntax.While cond body) k in
      inv_template vars temp_size (fun rv v => rv = eval (fst v) cond) rv_postcond s.

    Require Import Bedrock.Platform.Malloc.
    Require Import Bedrock.Platform.Cito.Semantics.

    Definition after_call ret k : assert :=
      st ~> Ex fs,
      let stn := fst st in
      funcs_ok stn fs /\
      ExX, Ex vs, Ex heap1, Ex heap2, Ex temps, Ex rp, Ex e_stack, Ex ret_w, Ex ret_a,
      let old_sp := st#Sp ^- (frame_len_w vars temp_size) in
      ![^[is_state old_sp rp e_stack e_stack vars (vs, heap1) temps * is_heap heap2 * layout_option ret_w ret_a * mallocHeap 0] * #0] st /\
      let env := (ConvertLabel.from_bedrock_label_map (Labels stn), fs stn) in
      [| let vs := upd_option vs ret st#Rv in
         let heap12 := heap_merge heap1 heap2 in
         let heap := heap_upd_option heap12 ret_w ret_a in
         let v := (vs, heap) in
         (separated heap12 ret_w ret_a -> Safe env k v) /\
         length temps = temp_size |] /\
      (rp, stn)
        @@@ (
          st' ~> Ex v', Ex temps',
          ![^[is_state st'#Sp rp e_stack e_stack vars v' temps' * mallocHeap 0] * #1] st' /\
          [| let vs := upd_option vs ret st#Rv in
             let heap12 := heap_merge heap1 heap2 in
             let heap := heap_upd_option heap12 ret_w ret_a in
             let v := (vs, heap) in
             separated heap12 ret_w ret_a /\
             RunsTo env k v v' /\
             length temps' = temp_size /\
             st'#Sp = old_sp /\
             rv_postcond st'#Rv (fst v') |]).

    Variable imports : LabelMap.t assert.

    Variable imports_global : importsGlobal imports.

    Variable modName : string.

    Require Bedrock.Platform.Cito.CompileExpr.

    Definition compile_expr e n := CompileExpr.compile vars temp_size imports_global modName e n.

    Require Bedrock.Platform.Cito.CompileExprs.

    Definition compile_exprs es n dst := CompileExprs.compile vars temp_size es n dst imports_global modName.

    Definition compile := cmp vars temp_size imports_global loop_inv after_call compile_expr compile_exprs.

  End TopSection.

End Make.
