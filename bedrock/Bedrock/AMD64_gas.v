Require Import Coq.Lists.List Coq.Strings.String Coq.Strings.Ascii.

Require Import Bedrock.LabelMap Bedrock.Word Bedrock.IL Bedrock.XCAP.

Set Implicit Arguments.

Global Open Scope string_scope.


Fixpoint wordS sz (w : word sz) : string :=
  match w with
    | WO => ""
    | WS false _ w' => wordS w' ++ "0"
    | WS true _ w' => wordS w' ++ "1"
  end.

Definition binS sz (w : word sz) : string :=
  "0b" ++ wordS w.

Definition regS (r : reg) : string :=
  match r with
    | Sp => "%ebx"
    | Rp => "%esi"
    | Rv => "%edi"
  end.

Definition tab := String (ascii_of_nat 9) "".
Definition nl := String (ascii_of_nat 10) "".

Definition locS (l : loc) : string :=
  match l with
    | Reg r => "bedrock_heap(" ++ regS r ++ ")"
    | Imm w => binS w ++ "+bedrock_heap"
    | Indir r w => binS w ++ "+bedrock_heap(" ++ regS r ++ ")"
  end.

Record registerPair := {
  Name8 : string;
  Name32 : string
}.

Definition ecx := {| Name8 := "cl"; Name32 := "ecx" |}.
Definition edx := {| Name8 := "dl"; Name32 := "edx" |}.

Definition lvalueS (lv : lvalue) (tmp : registerPair) : string * string :=
  match lv with
    | LvReg r => (regS r, "")
    | LvMem l => (locS l, "")
    | LvMem8 l => ("%" ++ Name32 tmp, tab ++ "mov %" ++ Name8 tmp ++ "," ++ locS l ++ nl)
  end.

Definition label'S (lab' : label') : string :=
  match lab' with
    | Global s => s
    | Local n => wordS (NToWord 32 n)
  end.

Definition labelS (lab : label) : string :=
  let (mod, blk) := lab in
    mod ++ "_" ++ label'S blk.

Definition rvalueS (rv : rvalue) (tmp : registerPair) : string * string :=
  match rv with
    | RvLval (LvReg r) => ("", regS r)
    | RvLval (LvMem l) => ("", locS l)
    | RvLval (LvMem8 l) => (tab ++ "xorl %" ++ Name32 tmp ++ ",%" ++ Name32 tmp ++ nl
      ++ tab ++ "mov " ++ locS l ++ ",%" ++ Name8 tmp ++ nl, "%" ++ Name32 tmp)
    | RvImm w => ("", "$" ++ binS w)
    | RvLabel lab => ("", "$" ++ labelS lab)
  end.

Definition rvalueSnomem (rv : rvalue) (tmp : registerPair) : string * string :=
  match rv with
    | RvLval (LvReg r) => ("", regS r)
    | RvLval (LvMem l) => (tab ++ "movl " ++ locS l ++ ",%" ++ Name32 tmp ++ nl, "%" ++ Name32 tmp)
    | RvLval (LvMem8 l) => (tab ++ "xorl %" ++ Name32 tmp ++ ",%" ++ Name32 tmp ++ nl
      ++ tab ++ "mov " ++ locS l ++ ",%" ++ Name8 tmp ++ nl, "%" ++ Name32 tmp)
    | RvImm w => ("", "$" ++ binS w)
    | RvLabel lab => ("", "$" ++ labelS lab)
  end.

Definition rvalueSnoimm (rv : rvalue) (tmp : registerPair) : string * string :=
  match rv with
    | RvLval (LvReg r) => ("", regS r)
    | RvLval (LvMem l) => (tab ++ "movl " ++ locS l ++ ",%" ++ Name32 tmp ++ nl, "%" ++ Name32 tmp)
    | RvLval (LvMem8 l) => (tab ++ "xorl %" ++ Name32 tmp ++ ",%" ++ Name32 tmp ++ nl
      ++ tab ++ "mov " ++ locS l ++ ",%" ++ Name8 tmp ++ nl, "%" ++ Name32 tmp)
    | RvImm w => (tab ++ "movl $" ++ binS w ++ ",%" ++ Name32 tmp ++ nl, "%" ++ Name32 tmp)
    | RvLabel lab => (tab ++ "movl $" ++ labelS lab ++ ",%" ++ Name32 tmp ++ nl, "%" ++ Name32 tmp)
  end.

Definition rvalueSinto (rv : rvalue) (tmp : registerPair) : string :=
  match rv with
    | RvLval (LvReg r) => tab ++ "movl " ++ regS r ++ ",%" ++ Name32 tmp ++ nl
    | RvLval (LvMem l) => tab ++ "movl " ++ locS l ++ ",%" ++ Name32 tmp ++ nl
    | RvLval (LvMem8 l) => tab ++ "xorl %" ++ Name32 tmp ++ ",%" ++ Name32 tmp ++ nl
      ++ tab ++ "mov " ++ locS l ++ ",%" ++ Name8 tmp ++ nl
    | RvImm w => tab ++ "movl $" ++ binS w ++ ",%" ++ Name32 tmp ++ nl
    | RvLabel lab => tab ++ "movl $" ++ labelS lab ++ ",%" ++ Name32 tmp ++ nl
  end.

Definition binopS (o : binop) : string :=
  match o with
    | Plus => "addl"
    | Minus => "subl"
    | Mult => "imull"
  end.

Definition lvalueIsMem (lv : lvalue) : bool :=
  match lv with
    | LvMem _ => true
    | LvMem8 _ => true
    | LvReg _ => false
  end.

Definition rvalueIsMem (rv : rvalue) : bool :=
  match rv with
    | RvLval lv => lvalueIsMem lv
    | _ => false
  end.

Definition rvalueIsImm (rv : rvalue) : bool :=
  match rv with
    | RvImm _ => true
    | RvLabel _ => true
    | _ => false
  end.

Definition instrS (i : instr) : string :=
  match i with
    | Assign lv rv =>
      let (lvS, lvI) := lvalueS lv ecx in
      let (rvI, rvS) := (if rvalueIsMem rv then rvalueSnomem else rvalueS) rv edx in
        rvI ++ tab ++ "movl " ++ rvS ++ "," ++ lvS ++ nl ++ lvI

    | Binop lv rv1 o rv2 =>
      let (lvS, lvI) := lvalueS lv ecx in
      let rv1I := rvalueSinto rv1 edx in
      let (rv2I, rv2S) := rvalueS rv2 ecx in
      rv1I ++ rv2I
      ++ tab ++ binopS o ++ " " ++ rv2S ++ ",%edx" ++ nl
      ++ tab ++ "movl %edx," ++ lvS ++ nl ++ lvI
  end.

Definition testS (t : test) : string :=
  match t with
    | Eq => "z"
    | Ne => "nz"
    | Lt => "b"
    | Le => "na"
  end.

Definition jmpS (j : jmp) : string :=
  match j with
    | Uncond (RvLabel lab) =>
      tab ++ "jmp " ++ labelS lab ++ nl
    | Uncond rv =>
      rvalueSinto rv edx
      ++ tab ++ "jmp *%rdx" ++ nl
    | Cond rv1 t rv2 lab1 lab2 =>
      let '(rv1, t, rv2, lab1, lab2) :=
        if rvalueIsMem rv2
          then match t with
                 | Eq => (rv2, Eq, rv1, lab1, lab2)
                 | Ne => (rv2, Ne, rv1, lab1, lab2)
                 | Lt => (rv2, Le, rv1, lab2, lab1)
                 | Le => (rv2, Lt, rv1, lab2, lab1)
               end
          else (rv1, t, rv2, lab1, lab2) in
      match rv1, rv2 with
        | RvImm w1, RvImm w2 => if evalTest t w1 w2
          then tab ++ "jmp " ++ labelS lab1 ++ nl
          else tab ++ "jmp " ++ labelS lab2 ++ nl
        | _, _ =>
          let (rv1I, rv1S) := (if rvalueIsImm rv1 then rvalueSnoimm else rvalueS) rv1 ecx in
          let (rv2I, rv2S) := (if rvalueIsMem rv1 then rvalueSnomem else rvalueS) rv2 edx in
            rv1I ++ rv2I
            ++ tab ++ "cmpl " ++ rv2S ++ "," ++ rv1S ++ nl
            ++ tab ++ "j" ++ testS t ++ " " ++ labelS lab1 ++ nl
            ++ tab ++ "jmp " ++ labelS lab2 ++ nl
      end
  end.

Definition blockS (b : block) : string :=
  let (is, j) := b in
    fold_right (fun i s => instrS i ++ s) (jmpS j) is.

Definition moduleS (m : module) : LabelMap.t string :=
  LabelMap.mapi (fun lab (bl : assert * block) => let (_, b) := bl in
    labelS lab ++ ":" ++ nl ++ blockS b) m.(Blocks).

Global Transparent natToWord.
Require Export Coq.extraction.ExtrOcamlString.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
