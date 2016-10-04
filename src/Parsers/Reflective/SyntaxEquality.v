Require Import Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.ContextFreeGrammar.Reflective.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.BoolFacts.

Global Instance SimpleTypeCode_BoolDecR : BoolDecR SimpleTypeCode := SimpleTypeCode_beq.
Global Instance SimpleTypeCode_BoolDec_bl : BoolDec_bl _ := internal_SimpleTypeCode_dec_bl.
Global Instance SimpleTypeCode_BoolDec_lb : BoolDec_lb _ := internal_SimpleTypeCode_dec_lb.
Global Instance TypeCode_BoolDecR : BoolDecR TypeCode := TypeCode_beq.
Global Instance TypeCode_BoolDec_bl : BoolDec_bl _ := internal_TypeCode_dec_bl.
Global Instance TypeCode_BoolDec_lb : BoolDec_lb _ := internal_TypeCode_dec_lb.

Definition RLiteralConstructor_beq {t1 t2} (e1 : RLiteralConstructor t1) (e2 : RLiteralConstructor t2) : bool
  := match e1, e2 with
     | Rpair A B, Rpair A' B' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq B B'
     | Rpair _ _, _ => false
     | RS, RS => true
     | RS, _ => false
     | RO, RO => true
     | RO, _ => false
     | Rnil A, Rnil A' => SimpleTypeCode_beq A A'
     | Rnil _, _ => false
     | Rcons A, Rcons A' => SimpleTypeCode_beq A A'
     | Rcons _, _ => false
     | Rbool b, Rbool b' => bool_beq b b'
     | Rbool _, _ => false
     | Rrchar_expr_ascii x, Rrchar_expr_ascii x' => Reflective.RCharExpr_beq ascii_beq x x'
     | Rrchar_expr_ascii _, _ => false
     | Rstring x, Rstring x' => string_beq x x'
     | Rstring _, _ => false
     | Rritem_ascii x, Rritem_ascii x' => Reflective.ritem_beq ascii_beq x x'
     | Rritem_ascii _, _ => false
     end%bool.
Global Instance RLiteralConstructor_BoolDecR {t} : BoolDecR (RLiteralConstructor t) := RLiteralConstructor_beq.
Definition RLiteralNonConstructor_beq {t1 t2} (e1 : RLiteralNonConstructor t1) (e2 : RLiteralNonConstructor t2) : bool
  := match e1, e2 with
     | Rfst A B, Rfst A' B' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq B B'
     | Rfst _ _, _ => false
     | Rsnd A B, Rsnd A' B' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq B B'
     | Rsnd _ _, _ => false
     | Rnth' A, Rnth' A' => SimpleTypeCode_beq A A'
     | Rnth' _, _ => false
     | Rnth A, Rnth A' => SimpleTypeCode_beq A A'
     | Rnth _, _ => false
     | Rbeq_nat, Rbeq_nat => true
     | Rbeq_nat, _ => false
     | Rmap A B, Rmap A' B' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq B B'
     | Rmap _ _, _ => false
     | Rfold_left A B, Rfold_left A' B' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq B B'
     | Rfold_left _ _, _ => false
     | Rorb, Rorb => true
     | Rorb, _ => false
     | Randb, Randb => true
     | Randb, _ => false
     | Randbr, Randbr => true
     | Randbr, _ => false
     | Rorbr, Rorbr => true
     | Rorbr, _ => false
     | Rminusr, Rminusr => true
     | Rminusr, _ => false
     | Rpred, Rpred => true
     | Rpred, _ => false
     | Rlength A, Rlength A' => SimpleTypeCode_beq A A'
     | Rlength _, _ => false
     | Rbool_rect_nodep A, Rbool_rect_nodep A' => SimpleTypeCode_beq A A'
     | Rbool_rect_nodep _, _ => false
     | Rlist_rect_nodep A P, Rlist_rect_nodep A' P' => SimpleTypeCode_beq A A' && TypeCode_beq P P'
     | Rlist_rect_nodep _ _, _ => false
     | Rlist_caset_nodep A P, Rlist_caset_nodep A' P' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq P P'
     | Rlist_caset_nodep _ _, _ => false
     | Rleb, Rleb => true
     | Rleb, _ => false
     | Rcombine A B, Rcombine A' B' => SimpleTypeCode_beq A A' && SimpleTypeCode_beq B B'
     | Rcombine _ _, _ => false
     | Rrev A, Rrev A' => SimpleTypeCode_beq A A'
     | Rrev _, _ => false
     | Rup_to, Rup_to => true
     | Rup_to, _ => false
     | Rplus, Rplus => true
     | Rplus, _ => false
     | Rmax, Rmax => true
     | Rmax, _ => false
     | Rritem_rect_nodep A, Rritem_rect_nodep A' => SimpleTypeCode_beq A A'
     | Rritem_rect_nodep _, _ => false
     | Rfirst_index_default A, Rfirst_index_default A' => SimpleTypeCode_beq A A'
     | Rfirst_index_default _, _ => false
     | Rinterp_RCharExpr_ascii, Rinterp_RCharExpr_ascii => true
     | Rinterp_RCharExpr_ascii, _ => false
     | Rstring_beq, Rstring_beq => true
     | Rstring_beq, _ => false
     end%bool.
Global Instance RLiteralNonConstructor_BoolDecR {t} : BoolDecR (RLiteralNonConstructor t) := RLiteralNonConstructor_beq.
Definition RLiteralTerm_beq {t1 t2} (e1 : RLiteralTerm t1) (e2 : RLiteralTerm t2) : bool
  := match e1, e2 with
     | RLC e1, RLC e2 => RLiteralConstructor_beq e1 e2
     | RLC _, _ => false
     | RLNC e1, RLNC e2 => RLiteralNonConstructor_beq e1 e2
     | RLNC _, _ => false
     end.
Global Instance RLiteralTerm_BoolDecR {t} : BoolDecR (RLiteralTerm t) := RLiteralTerm_beq.
Local Ltac extra_t := idtac.
Local Ltac t :=
  progress simpl in *;
  repeat match goal with
         | _ => intro
         | [ H : true = false |- _ ] => exfalso; exact (Bool.diff_true_false H)
         | [ H : false = true |- _ ] => exfalso; exact (Bool.diff_false_true H)
         | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : sig _ |- _ ] => destruct H
         | _ => progress subst
         | [ |- sig _ ] => exists eq_refl
         | [ |- ?x = ?x ] => reflexivity
         | [ H : SimpleTypeCode_beq ?x ?y = true |- _ ] => apply internal_SimpleTypeCode_dec_bl in H
         | [ H : TypeCode_beq ?x ?y = true |- _ ] => apply internal_TypeCode_dec_bl in H
         | _ => progress extra_t
         | [ H : ?beq ?x ?y = true |- _ ] => apply bl in H
         | [ H : ?beq ?x ?y = true |- _ ] => let T := type of x in
                                             let lem := constr:(@bl T _ eq _) in
                                             apply lem in H
         | _ => progress simpl in *
         end.

Lemma RLiteralConstructor_beq_bl {t1 t2} (e1 : RLiteralConstructor t1) (e2 : RLiteralConstructor t2)
  : RLiteralConstructor_beq e1 e2 = true -> { pf : t1 = t2 | eq_rect _ RLiteralConstructor e1 _ pf = e2 }.
Proof. destruct e1, e2; t. Defined.
Lemma RLiteralNonConstructor_beq_bl {t1 t2} (e1 : RLiteralNonConstructor t1) (e2 : RLiteralNonConstructor t2)
  : RLiteralNonConstructor_beq e1 e2 = true -> { pf : t1 = t2 | eq_rect _ RLiteralNonConstructor e1 _ pf = e2 }.
Proof. destruct e1, e2; t. Defined.

Local Ltac extra_t ::=
      match goal with
      | [ H : RLiteralConstructor_beq ?x ?y = true |- _ ] => apply RLiteralConstructor_beq_bl in H
      | [ H : RLiteralNonConstructor_beq ?x ?y = true |- _ ] => apply RLiteralNonConstructor_beq_bl in H
      end.

Lemma RLiteralTerm_beq_bl {t1 t2} (e1 : RLiteralTerm t1) (e2 : RLiteralTerm t2)
  : RLiteralTerm_beq e1 e2 = true -> { pf : t1 = t2 | eq_rect _ RLiteralTerm e1 _ pf = e2 }.
Proof. destruct e1, e2; t. Defined.
