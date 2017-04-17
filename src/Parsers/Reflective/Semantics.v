Require Import Coq.Strings.String.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.Syntactify.
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

Fixpoint apply_args_for {T}
         (f : interp_TypeCode T)
         (argsv : args_for interp_TypeCode T)
  : interp_TypeCode (range_of T)
  := match argsv in args_for _ T return interp_TypeCode T -> interp_TypeCode (range_of T) with
     | an_arg A B arg args => fun f => @apply_args_for _ (f arg) args
     | noargs T => fun f => f
     end f.

Section step.
  Context (interp_RLiteralTerm : forall {T}, RLiteralTerm T -> interp_TypeCode T).
  Context (interp_Term_gen : forall {T} (t : Term interp_TypeCode T), interp_TypeCode T).

  Definition interp_Term_gen_step {T} (t : Term interp_TypeCode T) : interp_TypeCode T
    := match t in (Term _ T') return interp_TypeCode T' with
       | RVar T v => v
       | RLambda A B f => fun x => @interp_Term_gen _ (f x)
       | RApp A B f x => @interp_Term_gen _ f (@interp_Term_gen _ x)
       | RLiteralApp c t args => apply_args_for (interp_RLiteralTerm t)
                                                (map_args_for (@interp_Term_gen) args)
       end.
End step.

Fixpoint interp_Term_gen (interp_RLiteralTerm : forall T, RLiteralTerm T -> interp_TypeCode T)
         {T} (t : Term interp_TypeCode T) : interp_TypeCode T
  := @interp_Term_gen_step interp_RLiteralTerm (@interp_Term_gen interp_RLiteralTerm) T t.

Definition interp_RLiteralTerm {T} (t : RLiteralTerm T) : interp_TypeCode T
  := match t with
     | RLC t'
       => match t' in (RLiteralConstructor T') return interp_TypeCode T' with
          | Rpair _ _ => @pair _ _
          | RS => S
          | RO => O
          | Rnil _ => @nil _
          | Rcons _ => @cons _
          | Rbool v
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
          end
     end.

Definition interp_Term : forall {T} (t : Term interp_TypeCode T), interp_TypeCode T
  := @interp_Term_gen (@interp_RLiteralTerm).

(* Section equality.
  Context {M : Type -> Type}.

  Definition args_for_values_code {T} (a0 : @args_for_values M T)
    : @args_for_values M T -> Prop
    := match a0 in @args_for_values _ T return @args_for_values _ T -> Prop with
       | an_argv A B a0 as0
         => fun a1
            => a0 = ahdv a1 /\ as0 = atlv a1
       | noargsv _
         => fun a1 => noargsv = a1
       end.

  Global Instance args_for_values_code_refl {T} : RelationClasses.Reflexive (@args_for_values_code T).
  Proof.
    intro a; destruct a; simpl; repeat split.
  Qed.

  Lemma args_for_values_encode {T} (a0 a1 : @args_for_values M T)
    : a0 = a1 -> args_for_values_code a0 a1.
  Proof.
    intro; subst; reflexivity.
  Qed.
End equality.
 *)

Ltac fold_interp_Term :=
  change (@interp_Term_gen (@interp_RLiteralTerm)) with (@interp_Term) in *;
  fold @interp_TypeCode in *.

Ltac simpl_interp_Term :=
  unfold interp_Term; simpl @interp_Term_gen;
  fold_interp_Term.

Ltac simpl_interp_Term_in_all :=
  unfold interp_Term in *; simpl @interp_Term_gen in *;
  fold_interp_Term.

Lemma interp_Term_syntactify_list {T : SimpleTypeCode}
      (ls : list (Term interp_TypeCode T))
: List.map interp_Term ls = interp_Term (Syntactify.syntactify_list ls).
Proof.
  unfold interp_Term; induction ls; simpl; [ reflexivity | ].
  rewrite <- IHls; reflexivity.
Qed.

Lemma interp_Term_syntactify_nat
      (v : nat)
: v = interp_Term (Syntactify.syntactify_nat _ v).
Proof.
  unfold interp_Term.
  induction v as [|v IHv]; [ reflexivity | simpl ].
  rewrite <- IHv; reflexivity.
Qed.

Lemma interp_Term_syntactify_rproductions
      ls
: ls = interp_Term (Syntactify.syntactify_rproductions _ ls).
Proof.
  repeat match goal with
         | [ |- ?x = ?x ] => reflexivity
         | _ => progress unfold Syntactify.syntactify_rproductions, syntactify_prod, syntactify_string
         | _ => progress simpl
         | _ => progress simpl_interp_Term
         | _ => rewrite <- interp_Term_syntactify_list, List.map_map
         | [ |- ?x = List.map _ ?x ]
           => etransitivity; [ symmetry; apply List.map_id | ]
         | [ |- List.map _ ?x = List.map _ ?x ]
           => apply List.map_ext; intro
         | [ |- _ = _ :> prod _ _ ]
           => apply injective_projections
         end.
Qed.
