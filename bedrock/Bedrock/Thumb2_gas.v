(* Thumb2_gas -- Thumb-2 code generator *)

(** printing ++ $+\kern-0.3em+$ *)

(** This module, like [I386_gas] and [AMD64_gas] before it, generates ARM
Thumb-2 code from the Bedrock IL.  Unlike those generators, however,
[Thumb2_gas] generates code in two steps.  In the first, it converts the
Bedrock IL (an abstract CISC ISA) to an embedded subset of ARM assembly (a RISC
ISA); in the second, it serializes the embedded ARM assembly to a [string]
suitable for GAS consumption.

Note that the generated assembly uses the new ‘unified’ syntax for ARM/Thumb
assembly.  To assemble files generated with this generator, you’ll thus need to
place
<<
    .syntax unified
    .text
>>
at the top of the file. *)

Require Import Coq.Lists.List.  Import ListNotations.

Require Import Bedrock.FastString.

Require Coq.Strings.Ascii Bedrock.Memory Bedrock.Word.


(** A function application operator, à la Haskell, makes quite a bit of the
code below much more readable. *)

Notation "f $ x" := (f x) (at level 100, right associativity, only parsing).


(** * Partial Thumb-2 machine definition

We support only a subset of the Thumb-2 ISA.  Should other opcodes become
useful at a later date, it will be easy to add them. *)

Module Thumb.
  Import Ascii.

  Import Memory.
  Import Word.

  Local Open Scope nat.
  Local Open Scope string.
  Set Implicit Arguments.

  (** Thumb-2 has full support for the first eight general-purpose registers
  (R0–R7), the condition flag register, and the program counter.  It also has
  limited support for R8-R15.  Of course, we don't need all of these registers
  to compile Bedrock. *)

  Inductive register := R0 | R1 | R2 | R3 | R4 | R5 | R6 | PC.

  Inductive litOrLabel :=
  | Lit : W -> litOrLabel
  | Label : string -> litOrLabel.

  Definition register_eq : forall x y: register, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition register_eqb x y := if register_eq x y then true else false.

  Inductive registerOrLiteral :=
  | Register : register -> registerOrLiteral
  | Literal : W -> registerOrLiteral.

  (** Thumb-2 supports a whole host of condition flags, but these six are
  sufficient to compile Bedrock.  Comparison flags are for unsigned comparison,
  as defined by the Bedrock IL semantics. *)

  Inductive condition :=
  | EQ | NE
  | HS (* ≥ *) | LO (* < *)
  | HI (* > *) | LS (* ≤ *).

  (** We need fairly few Thumb mnemonics to actually compile Bedrock code.
  Note that <<ldr =>> (e.g., <<ldr r1, =12345>>) is not an actual Thumb
  mnemonic but rather a GAS-provided pseudo-opcode that cleverly skirts Thumb’s
  limitations on immediates in <<mov>> instructions.  See
  <<https://sourceware.org/binutils/docs/as/ARM-Opcodes.html#index-g_t_0040code_007bLDR-reg_002c_003d_003clabel_003e_007d-pseudo-op_002c-ARM-700>>
  for a more complete rundown. *)

  Inductive instruction :=
  | Mov : register -> register -> instruction
  | LdrEq : register -> litOrLabel -> instruction
  | CondLdrEq : condition -> register -> litOrLabel -> instruction
  | Ldr : register -> register -> instruction
  | LdrB : register -> register -> instruction
  | Str : register -> register -> instruction
  | StrB : register -> register -> instruction
  | Add : register -> register -> registerOrLiteral -> instruction
  | Sub : register -> register -> registerOrLiteral -> instruction
  | Mul : register -> register -> registerOrLiteral -> instruction
  | Cmp : register -> register -> instruction
  | Ite : condition -> instruction.


  (** ** Serializing to [string] *)

  Module Show.
    Definition tab := String (ascii_of_nat 9) "".
    Definition newline := String (ascii_of_nat 10) "".

    Fixpoint wordS sz (w : word sz) : string :=
      match w with
        | WO => ""
        | WS false _ w' => wordS w' ++ "0"
        | WS true _ w' => wordS w' ++ "1"
      end.

    Definition register r :=
      match r with
        | R0 => "r0"
        | R1 => "r1"
        | R2 => "r2"
        | R3 => "r3"
        | R4 => "r4"
        | R5 => "r5"
        | R6 => "r6"
        | PC => "pc"
      end.

    Definition litOrLabel x :=
      match x with
        | Lit lit => "0b" ++ wordS lit
        | Label s => s
      end.

    Definition registerOrLiteral x :=
      match x with
        | Register r => register r
        | Literal lit => "#0b" ++ wordS lit
      end.

    Definition condition (cond : condition) : string :=
      match cond with
        | EQ => "eq"
        | NE => "ne"
        | HS => "hs"
        | LO => "lo"
        | HI => "hi"
        | LS => "ls"
      end.

    Definition mnemonic (name : string) (operands : list string) : string :=
      tab ++ name ++ " " ++ intercalate ", " operands ++ newline.

    Definition instruction (instr : instruction) : string :=
      match instr with
        | Mov rd rn => mnemonic "mov" $ map register [rd; rn]
        | LdrEq rd x => mnemonic "ldr" [register rd; "=" ++ litOrLabel x]
        | CondLdrEq cond rd x => mnemonic ("ldr" ++ condition cond) [register rd; "=" ++ litOrLabel x]
        | Ldr rd rn => mnemonic "ldr" [register rd; "[" ++ register rn ++ "]"]
        | LdrB rd rn => mnemonic "ldrb" [register rd; "[" ++ register rn ++ "]"]
        | Str rd rn => mnemonic "str" [register rd; "[" ++ register rn ++ "]"]
        | StrB rd rn => mnemonic "strb" [register rd; "[" ++ register rn ++ "]"]
        | Add rd rn rm => mnemonic "add" [register rd; register rn; registerOrLiteral rm]
        | Sub rd rn rm => mnemonic "sub" [register rd; register rn; registerOrLiteral rm]
        | Mul rd rm rs => mnemonic "mul" [register rd; register rm; registerOrLiteral rs]
        | Cmp rn rm => mnemonic "cmp" $ map register [rn; rm]
        | Ite cond => mnemonic "ite" [condition cond]
      end.

  End Show.

End Thumb.


(** * Converting [IL.instr] to [Thumb.instruction] *)

Require Import Coq.Arith.Compare_dec.

Require Bedrock.IL.
Require Import Bedrock.LabelMap.
Require Import Bedrock.Labels.
Require Import Bedrock.Memory.
Require Import Bedrock.Word.
Require Bedrock.XCAP.

(** Make [natToWord] transparent so Coq can actually compute the result of
[moduleS] far enough to actually yield a string of assembly. *)

Global Transparent natToWord.


(** ** Atoms

Words, registers, and labels are very easy to convert. *)

Local Open Scope string.

Fixpoint wordS {sz} (w : word sz) : string :=
  match w with
    | WO => ""
    | WS false _ w' => wordS w' ++ "0"
    | WS true _ w' => wordS w' ++ "1"
  end.

Definition binS {sz} (w : word sz) : string :=
  "0b" ++ wordS w.

(** The Bedrock IL requires only three registers.  We map them to the first
three ARM registers, leaving R3–R6 available for scratchpad use. *)

Definition regS (r : IL.reg) : Thumb.register :=
  match r with
    | IL.Sp => Thumb.R0
    | IL.Rp => Thumb.R1
    | IL.Rv => Thumb.R2
  end.

Definition labelS (lab : label) : string :=
  let (mod, blk) := lab in
  mod ++ "_" ++ match blk with
                  | Global s => s
                  | Local n => wordS $ NToWord 32 n
                end.

Local Close Scope string.


(** ** Arithmetic

Assuming all arithmetic operations are register-register makes them quite easy
as well. *)

Definition binop (op : IL.binop)
                 (dest : Thumb.register)
                 (left : Thumb.register)
                 (right : Thumb.register)
                 : Thumb.instruction
                 :=
  let mnemonic := match op with
                    | IL.Plus => Thumb.Add
                    | IL.Minus => Thumb.Sub
                    | IL.Times => Thumb.Mul
                  end
  in
  mnemonic dest left $ Thumb.Register right.

(** *** Optimization: Eliminate unnecessary register addition

Later on, we’re going to be doing a lot of offset computation.  While we can do
this with a <<ldr =>> followed by a register-register <<add>>, we can sometimes
exploit the constant field available in a register-constant <<add>>.  To make
this optimization, we first need to be able to determine if a word can be
truncated without incident. *)

Definition wordIsZero {size} : word size -> bool := weqb (wzero _).

Theorem wordIsZero_def: forall size (w : word size),
                          wordIsZero w = true <-> wzero _ = w.
Proof.
  intros.  apply weqb_true_iff.
Qed.

Definition canFitIn {upper : nat}
                    (lower : nat)
                    (w : word (lower + upper))
                    : bool
                    := weqb (split2 _ upper w) (wzero _).

Example canFitIn_ex1: canFitIn 5 (WO~0~0~0~1~0~0~0~0) = true.
  reflexivity.  Qed.
Example canFitIn_ex2: canFitIn 5 (WO~0~1~0~0~1~0) = true.
  reflexivity.  Qed.
Example canFitIn_ex3: canFitIn 3 (WO~0~0~1~0~0~1~0) = false.
  reflexivity.  Qed.

(** Now we can implement the actual optimization. *)

Definition addLiteral (tmp : Thumb.register)
                      (dst : Thumb.register)
                      (src : Thumb.register)
                      (lit : W)
                      : list Thumb.instruction
                      :=
  if orb (canFitIn 3 lit)
         (andb (canFitIn 8 lit)
               (Thumb.register_eqb dst src))
  then [Thumb.Add dst src $ Thumb.Literal lit]
  else [ Thumb.LdrEq tmp $ Thumb.Lit lit;
         Thumb.Add dst src $ Thumb.Register tmp ].

(** ** Branches

We don’t use Thumb’s branches – they’re limited in how far you can branch.
(For conditional branches, the limit is 258 bytes; for unconditional branches,
it’s 2 kiB.)  Instead, we do a conditional <<ldr =>> instruction to load the
destination address into a temporary register, and then we simply replace the
program counter. *)

Definition cmpAndBranch (tmp : Thumb.register)
                        (left : Thumb.register)
                        (op : IL.test)
                        (right : Thumb.register)
                        (ifTrue : label)
                        (ifFalse : label)
                      : list Thumb.instruction
                      :=
  let (condTrue, condFalse) := match op with
                                 | IL.Eq => (Thumb.EQ, Thumb.NE)
                                 | IL.Ne => (Thumb.NE, Thumb.EQ)
                                 | IL.Lt => (Thumb.LO, Thumb.HS)
                                 | IL.Le => (Thumb.LS, Thumb.HI)
                               end
  in
  [ Thumb.Cmp left right;
    Thumb.Ite condTrue;
    Thumb.CondLdrEq condTrue  tmp (Thumb.Label $ labelS ifTrue);
    Thumb.CondLdrEq condFalse tmp (Thumb.Label $ labelS ifFalse);
    Thumb.Mov Thumb.PC tmp ].

(** ** Memory operations

Here’s where things start to get complicated.  Thumb’s chief limitation is
memory addressing – it supports a 32-bit address bus, but instructions may only
be 16 bits wide.  Thus, many memory-related [IL.instr]s (e.g., memory-to-memory
assignments) become multiple Thumb instructions. *)

(** [memS] applies [mnemonic] to the register [reg] and the memory location
described by [loc] to execute a load or a store.  It uses [tmp1] and [tmp2] as
scratchpad registers; each must be different from [reg] (and the other).  _This
precondition is currently unchecked_.

Handling memory operations with offsets is easy thanks to the register-addition
offset implemented earlier. *)

Definition memS (tmp : Thumb.register * Thumb.register)
                (mnemonic : Thumb.register
                            -> Thumb.register
                            -> Thumb.instruction)
                (reg : Thumb.register)
                (loc : IL.loc)
                : list Thumb.instruction
                :=
  let (tmp1, tmp2) := tmp in
  let heap := Thumb.Label "bedrock_heap" in
  match loc with
    | IL.Reg r => [ Thumb.LdrEq tmp1 heap;
                    Thumb.Add tmp1 tmp1 $ Thumb.Register $ regS r;
                    mnemonic reg tmp1]
    | IL.Imm w => Thumb.LdrEq tmp1 heap
                    :: addLiteral tmp2 tmp1 tmp1 w
                    ++ [mnemonic reg tmp1]
    | IL.Indir r w => Thumb.LdrEq tmp1 heap
                        :: addLiteral tmp2 tmp1 tmp1 w
                        ++ [ Thumb.Add tmp1 tmp1 $ Thumb.Register $ regS r;
                             mnemonic reg tmp1 ]
  end.

(** Fetches [rvalue] from memory and stores it in [reg]. *)

Definition fetch (tmp : Thumb.register * Thumb.register)
                 (reg : Thumb.register)
                 (rvalue : IL.rvalue)
                 : list Thumb.instruction
                 :=
  let mem := memS tmp in
  match rvalue with
    | IL.RvLval lv => match lv with
                        | IL.LvReg r => [Thumb.Mov reg (regS r)]
                        | IL.LvMem loc => mem Thumb.Ldr reg loc
                        | IL.LvMem8 loc => mem Thumb.LdrB reg loc
                      end
    | IL.RvImm w => [Thumb.LdrEq reg $ Thumb.Lit w]
    | IL.RvLabel lab => [Thumb.LdrEq reg $ Thumb.Label $ labelS lab]
  end.

(** Stores the value of [reg] in memory at [lvalue]. *)

Definition writeback (tmp : Thumb.register * Thumb.register)
                     (lvalue : IL.lvalue)
                     (reg : Thumb.register)
                     : list Thumb.instruction
                     :=
  let mem := memS tmp in
  match lvalue with
    | IL.LvReg r => [Thumb.Mov (regS r) reg]
    | IL.LvMem loc => mem Thumb.Str reg loc
    | IL.LvMem8 loc => mem Thumb.StrB reg loc
  end.


(** ** Instructions and blocks *)

(** On Intel, an assignment can be quite CISCy.  However, on a RISC ISA like
Thumb, it’s easiest to think of an assignment in two stages: a fetch and a
writeback.

For a binary operation, think about four stages: fetch the first rvalue, fetch
the second rvalue, do the operation, and write back.  We’ll use R3 and R4 to
store the first and second rvalues, respectively, and we’ll reuse R3 to store
the result of the operation between the operation stage and the writeback. *)

Definition instrS (instr : IL.instr) : list Thumb.instruction :=
  let tmp := (Thumb.R5, Thumb.R6) in
  match instr with
    | IL.Assign lvalue rvalue =>
    fetch tmp Thumb.R3 rvalue ++ writeback tmp lvalue Thumb.R3
    | IL.Binop lvalue one op two =>
      fetch tmp Thumb.R3 one
        ++ fetch tmp Thumb.R4 two
        ++ [binop op Thumb.R3 Thumb.R3 Thumb.R4]
        ++ writeback tmp lvalue Thumb.R3
  end.

Definition jmpS (j : IL.jmp) : list Thumb.instruction :=
  let tmp := (Thumb.R5, Thumb.R6) in
  match j with
    | IL.Uncond target =>
      match target with
        | IL.RvLabel lab => [ Thumb.LdrEq Thumb.R5 (Thumb.Label $ labelS lab);
                              Thumb.Mov Thumb.PC Thumb.R5 ]
        | rvalue => fetch tmp Thumb.R3 rvalue
                      ++ [ Thumb.Mov Thumb.PC Thumb.R3 ]
      end
    | IL.Cond one op two ifTrue ifFalse =>
      fetch tmp Thumb.R3 one
        ++ fetch tmp Thumb.R4 two
        ++ cmpAndBranch Thumb.R5 Thumb.R3 op Thumb.R4 ifTrue ifFalse
  end.

Definition blockS (b : IL.block) : list Thumb.instruction :=
  let (instructions, jump) := b in
  fold_right (fun instr text => instrS instr ++ text) (jmpS jump) instructions.


(** ** Final serialization *)

Local Open Scope string.

(** [moduleS] presents the public interface for the assembler.  It extracts the
[LabelMap.t] from an [XCAP.module] and folds over it to produce a [LabelMap.t]
mapping labels to strings of assembly. *)

Definition moduleS (m : XCAP.module) : LabelMap.t string :=
  let labeledBlockS (lab : label) (bl : XCAP.assert * IL.block) :=
      let (_, b) := bl in
      (* If this function is to e exported, declare it global. *)
      (match lab with
         | (_, Labels.Global functionName) =>
           ".globl " ++ labelS lab ++ Thumb.Show.newline
         | _ => ""
       end)
        ++ (* Write the function label. *)
           labelS lab ++ ":" ++ Thumb.Show.newline
        ++ (* Print the function. *)
           (concat $ map Thumb.Show.instruction $ blockS b)
        ++ (* Since every block ends with a branch, we can put literal pools
           anywhere.  Mark this as a good place to put a literal pool. *)
           Thumb.Show.tab ++ ".ltorg" ++ Thumb.Show.newline
  in
  LabelMap.mapi labeledBlockS m.(XCAP.Blocks).

Global Transparent natToWord.
Require Export Coq.extraction.ExtrOcamlString.
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
