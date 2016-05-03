Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.List.Operations.
Set Implicit Arguments.

Local Open Scope list_scope.

Definition interp_SimpleTypeCode_step
           (interp_SimpleTypeCode : SimpleTypeCode -> Type)
           (t : SimpleTypeCode)
  : Type
  := match t with
     | cnat => nat
     | cbool => bool
     | cascii => Ascii.ascii
     | cstring => string
     | critem_ascii => Reflective.ritem Ascii.ascii
     | crchar_expr_ascii => Reflective.RCharExpr Ascii.ascii
     | clist T => list (interp_SimpleTypeCode T)
     | cprod A B => interp_SimpleTypeCode A * interp_SimpleTypeCode B
     end%type.

Fixpoint interp_SimpleTypeCode (t : SimpleTypeCode)
  := interp_SimpleTypeCode_step (@interp_SimpleTypeCode) t.

Fixpoint interp_TypeCode (t : TypeCode) : Type
  := match t with
     | csimple T => interp_SimpleTypeCode T
     | carrow A B => interp_TypeCode A -> interp_TypeCode B
     end%type.

Definition interp_RLiteralTerm {T} (t : RLiteralTerm T) : interp_TypeCode T
  := match t with
     | RLC t'
       => match t' in (RLiteralConstructor T') return interp_TypeCode T' with
          | Rpair _ _ => @pair _ _
          | RS => S
          | RO => O
          | Rnil _ => @nil _
          | Rcons _ => @cons _
          | Rfalse => false
          | Rtrue => true
          | Rrchar_expr_ascii v
          | Rstring v
          | Rritem_ascii v
            => v
          end
     | RLNC t'
       => match t' in (RLiteralNonConstructor T') return interp_TypeCode T' with
          | Rfst _ _ => @fst _ _
          | Rsnd _ _ => @snd _ _
          | Rnth' A => nth'
          | Rnth A => @List.nth _
          | Rmap A B => @List.map _ _
          | Rfold_left A B => @List.fold_left _ _
          | Rorb => orb
          | Randb => andb
          | Randbr => andbr
          | Rorbr => orbr
          | Rminusr => minusr
          | Rpred => pred
          | Rplus => plus
          | Rleb => Compare_dec.leb
          | Rbeq_nat => EqNat.beq_nat
          | Rstring_beq => Equality.string_beq
          | Rlength _ => @List.length _
          | Rbool_rect_nodep _ => @bool_rect_nodep _
          | Rlist_rect_nodep _ _ => @list_rect_nodep _ _
          | Rlist_caset_nodep _ _ => @list_caset_nodep _ _
          | Rritem_rect_nodep _ => @Reflective.ritem_rect_nodep _ _
          | Rcombine _ _ => @List.combine _ _
          | Rfirst_index_default _ => @first_index_default _
          | Rrev _ => @List.rev _
          | Rup_to => up_to
          | Rmax => max
          | Rinterp_RCharExpr_ascii => Reflective.interp_RCharExpr
          (*| Rchar_at_matches => fun n => char_at_matches n str
          | Rsplit_string_for_production => fun n => split_string_for_production n str*)
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

Section defaulted_fun.
  Context {var}
          (interp_var : forall T, var T -> interp_TypeCode T)
          (uninterp_var : forall T, interp_TypeCode T -> var T).

  Fixpoint interp_Term_fun
           {T}
           (t : Term var T) : interp_TypeCode T
    := match t in (Term _ T') return interp_TypeCode T' with
       | RVar _ v
         => interp_var v
       | RLambda A B f
         => fun x => @interp_Term_fun _ (f (uninterp_var _ x))
       | RApp A B f x
         => @interp_Term_fun
              _ f
              (@interp_Term_fun _ x)
       | RLiteralApp _ t' args
         => interp_args_for_fun (interp_RLiteralTerm t') args
       end
  with interp_args_for_fun {T} (f : interp_TypeCode T) (args : args_for _ T) : interp_TypeCode (range_of T)
       := match args in args_for _ T return interp_TypeCode T -> interp_TypeCode (range_of T) with
          | an_arg A B arg args => fun f => interp_args_for_fun (f (interp_Term_fun arg)) args
          | noargs T => fun f => f
          end f.
End defaulted_fun.
