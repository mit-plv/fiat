Require Import Coq.Classes.Morphisms. (* for reserved [-->] notation *)
Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Common.Notations.

Set Implicit Arguments.
Delimit Scope typecode_scope with typecode.
Delimit Scope term_scope with term.
Delimit Scope termargs_scope with termargs.
Local Set Boolean Equality Schemes.
Inductive SimpleTypeCode : Set :=
| cnat
| cbool
| cstring
| cascii
| critem_ascii
| crchar_expr_ascii
| clist (T : SimpleTypeCode)
| cprod (A B : SimpleTypeCode).
Inductive TypeCode : Set :=
| csimple (T : SimpleTypeCode)
| carrow (A B : TypeCode).
Module Export TypeCodeCoercions.
  Global Coercion csimple : SimpleTypeCode >-> TypeCode.
End TypeCodeCoercions.
Local Unset Boolean Equality Schemes.

Bind Scope typecode_scope with TypeCode.
Bind Scope typecode_scope with SimpleTypeCode.
Arguments clist _%typecode.
Arguments carrow (_ _)%typecode.
Arguments cprod (_ _)%typecode.

Infix "-->" := carrow : typecode_scope.
Infix "*" := cprod : typecode_scope.

Fixpoint range_of (T : TypeCode) : SimpleTypeCode
  := match T with
     | carrow A B => range_of B
     | csimple T => T
     end.

Section term.
  Context (var : TypeCode -> Type).

  Inductive RLiteralConstructor : TypeCode -> Set :=
  | Rpair {A B : SimpleTypeCode} : RLiteralConstructor (A --> B --> A * B)
  | RS : RLiteralConstructor (cnat --> cnat)
  | RO : RLiteralConstructor cnat
  | Rnil {A} : RLiteralConstructor (clist A)
  | Rcons {A : SimpleTypeCode} : RLiteralConstructor (A --> clist A --> clist A)
  | Rfalse : RLiteralConstructor cbool
  | Rtrue : RLiteralConstructor cbool
  | Rrchar_expr_ascii (_ : Reflective.RCharExpr ascii) : RLiteralConstructor crchar_expr_ascii
  | Rstring (_ : string) : RLiteralConstructor cstring
  | Rritem_ascii (_ : Reflective.ritem ascii) : RLiteralConstructor critem_ascii.
  Inductive RLiteralNonConstructor : TypeCode -> Set :=
  | Rfst {A B} : RLiteralNonConstructor (A * B --> A)
  | Rsnd {A B} : RLiteralNonConstructor (A * B --> B)
  | Rnth' {A} : RLiteralNonConstructor (cnat --> clist A --> A --> csimple A)
  | Rnth {A} : RLiteralNonConstructor (cnat --> clist A --> A --> csimple A)
  | Rbeq_nat : RLiteralNonConstructor (cnat --> cnat --> cbool)
  | Rmap {A B : SimpleTypeCode} : RLiteralNonConstructor ((A --> B) --> clist A --> clist B)
  | Rfold_left {A B : SimpleTypeCode} : RLiteralNonConstructor ((A --> B --> A) --> clist B --> A --> csimple A)
  | Rorb : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Randb : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Randbr : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Rorbr : RLiteralNonConstructor (cbool --> cbool --> cbool)
  | Rminusr : RLiteralNonConstructor (cnat --> cnat --> cnat)
  | Rpred : RLiteralNonConstructor (cnat --> cnat)
  | Rlength A : RLiteralNonConstructor (clist A --> cnat)
  | Rbool_rect_nodep {A : SimpleTypeCode} : RLiteralNonConstructor (A --> A --> cbool --> csimple A)
  | Rlist_rect_nodep {A : SimpleTypeCode} {P : TypeCode} : RLiteralNonConstructor (P --> (A --> clist A --> P --> P) --> clist A --> P)
  | Rlist_caset_nodep {A P : SimpleTypeCode} : RLiteralNonConstructor (P --> (A --> clist A --> P) --> clist A --> P)
  | Rleb : RLiteralNonConstructor (cnat --> cnat --> cbool)
  | Rcombine {A B} : RLiteralNonConstructor (clist A --> clist B --> clist (A * B))
  | Rrev {A} : RLiteralNonConstructor (clist A --> clist A)
  | Rup_to : RLiteralNonConstructor (cnat --> clist cnat)
  | Rplus : RLiteralNonConstructor (cnat --> cnat --> cnat)
  | Rmax : RLiteralNonConstructor (cnat --> cnat --> cnat)
  | Rritem_rect_nodep {A : SimpleTypeCode} : RLiteralNonConstructor ((crchar_expr_ascii --> A) --> (cstring --> A) --> critem_ascii --> csimple A)
  | Rfirst_index_default {A : SimpleTypeCode} : RLiteralNonConstructor ((A --> cbool) --> cnat --> clist A --> cnat)
  | Rinterp_RCharExpr_ascii : RLiteralNonConstructor (crchar_expr_ascii --> cascii --> cbool)
  | Rstring_beq : RLiteralNonConstructor (cstring --> cstring --> cbool).
  (*| Rchar_at_matches
    : RLiteralNonConstructor (cnat --> (cascii --> cbool) --> cbool)
  | Rsplit_string_for_production
    : RLiteralNonConstructor (cnat * (cnat * cnat) --> cnat --> cnat --> (clist cnat)).*)

  Inductive RLiteralTerm (T : TypeCode) : Set :=
  | RLC (_ : RLiteralConstructor T)
  | RLNC (_ : RLiteralNonConstructor T).

  Inductive Term : TypeCode -> Type :=
  | RVar {T} (v : var T) : Term T
  | RLambda {A B} (f : var A -> Term B)
    : Term (A --> B)
  | RApp {A B} (f : Term (A --> B)) (x : Term A)
    : Term B
  | RLiteralApp c (t : RLiteralTerm c) (args : args_for c)
    : Term (range_of c)
  with args_for : TypeCode -> Type :=
       | an_arg {A B} (arg : Term A) (args : args_for B) : args_for (A --> B)
       | noargs {T} : args_for (csimple T).
  Bind Scope term_scope with Term.
  Bind Scope termargs_scope with args_for.

  Definition ahd {A B} (af : args_for (A --> B)) : Term A :=
    match af in args_for T return match T with
                                  | carrow A B => Term A
                                  | _ => unit
                                  end with
    | an_arg _ _ arg _ => arg
    | _ => tt
    end.

  Definition atl {A B} (af : args_for (A --> B)) : args_for B :=
    match af in args_for T return match T with
                                  | carrow A B => args_for B
                                  | _ => unit
                                  end with
    | an_arg _ _ _ af' => af'
    | _ => tt
    end.
End term.

Bind Scope term_scope with Term.
Bind Scope termargs_scope with args_for.
Arguments RVar {var T%typecode} v.
Arguments RLambda {var} {A B}%typecode f%term.
Arguments RApp {var} {A B}%typecode (f x)%term.
Arguments RLiteralApp {var} {c}%typecode t%term args%termargs.
Arguments an_arg {var} {A B}%typecode arg%term args%termargs.
Arguments noargs {var T}.

Notation "# v" := (RVar v) : term_scope.
Infix "@" := RApp : term_scope.

Notation "\ x , e" := (RLambda (fun x => e)) : source_scope.
Notation "\ ! , e" := (RLambda (fun _ => e)) : source_scope.

Infix "::" := an_arg : termargs_scope.

Definition polyTerm T := forall var, Term var T.

Local Notation rcStepT cbool :=
  ((*Rchar_at_matches*)
    (cnat --> (cascii --> cbool) --> cbool)
      --> (*Rsplit_string_for_production*)
      (cnat * (cnat * cnat) --> cnat --> cnat --> (clist cnat))
      --> cnat --> cnat --> (cnat --> cnat --> cnat --> cbool) --> clist cnat --> cnat --> cnat --> cnat --> cbool)%typecode
                                                                                                                   (only parsing).

Inductive has_parse_term var : Type :=
| RFix2
    (G_length : nat) (up_to_G_length : list nat)
    (f : Term var (rcStepT cbool))
    (valid_len : nat)
    (valids : list nat)
    (nt_idx : nat).

Definition polyhas_parse_term := forall var, has_parse_term var.

Module Export Coercions.
  Export TypeCodeCoercions.
  Coercion RLC : RLiteralConstructor >-> RLiteralTerm.
  Coercion RLNC : RLiteralNonConstructor >-> RLiteralTerm.
End Coercions.
