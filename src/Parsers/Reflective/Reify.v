Require Export Coq.Strings.String. (* for error messages *)
Require Import Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.Semantics.
Require Import Fiat.Parsers.Reflective.Syntactify.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.List.Operations.
Export Syntax.Coercions.
Set Implicit Arguments.

Local Open Scope list_scope.
Local Open Scope string_scope.

Class cidtac_error {T T'} (msg0 : T) (msg1 : T') := dummy_idtac : True.
Hint Extern 0 (cidtac_error ?msg0 ?msg1) => idtac "<infomsg>Error:" msg0 msg1 "</infomsg>"; fail : typeclass_instances.
Ltac cidtac_error msg0 msg1 := constr:(_ : cidtac_error msg0 msg1).

Ltac reify_TypeCode ty :=
  lazymatch eval cbv beta in ty with
  | interp_TypeCode ?T => T
  | ?ty
    => let ty' := (eval hnf in ty) in
       lazymatch eval cbv beta in ty' with
       | nat => cnat
       | bool => cbool
       | Ascii.ascii => cascii
       | string => cstring
       | Reflective.ritem Ascii.ascii => critem_ascii
       | Reflective.RCharExpr Ascii.ascii => crchar_expr_ascii
       | list ?T => let T' := reify_TypeCode T in
                    constr:(clist T')
       | (?A -> ?B)%type => let A' := reify_TypeCode A in
                            let B' := reify_TypeCode B in
                            constr:(carrow A' B')
       | (?A * ?B)%type => let A' := reify_TypeCode A in
                           let B' := reify_TypeCode B in
                           constr:(cprod A' B')
       | Prop => let failc := constr:(I : I) in failc
       | Set => let failc := constr:(I : I) in failc
       | Type => let failc := constr:(I : I) in failc
       | ?ty'' => let dummy := match constr:(Set) with
                               | _ => constr:(eq_refl : Type = ty'')
                               | _ => cidtac_error "Cannot reify type" ty''
                               end in
                  let failc := constr:(I : I) in
                  failc
       end
  end.

Ltac reify_Term_lit0 var Rterm
  := match constr:(Set) with
     | _ => constr:(@RLiteralApp var _ Rterm)
     | _ => cidtac_error "Failed to reify0" Rterm
     end.
Ltac reify_Term_lit1 var A Rterm
  := match constr:(Set) with
     | _ => let A' := reify_TypeCode A in
            constr:(@RLiteralApp var _ (Rterm A'))
     | _ => cidtac_error "Failed to reify1" Rterm
     end.
Ltac reify_Term_lit2 var A B Rterm
  := match constr:(Set) with
     | _ => let A' := reify_TypeCode A in
            let B' := reify_TypeCode B in
            constr:(@RLiteralApp var _ (Rterm A' B'))
     | _ => cidtac_error "Failed to reify2" (Rterm, A, B)
     end.
Ltac reify_Term_lit5 var A B C D E Rterm
  := match constr:(Set) with
     | _ => let A' := reify_TypeCode A in
            let B' := reify_TypeCode B in
            let C' := reify_TypeCode C in
            let D' := reify_TypeCode D in
            let E' := reify_TypeCode E in
            match constr:(Set) with
            | _ => constr:(@RLiteralApp var _ (Rterm A' B' C' D' E'))
            | _ => cidtac_error "Failed to reify5" (Rterm, A', B', C', D', E')
            end
     | _ => cidtac_error "Failed to reify5 (types)" (Rterm, A, B, C, D, E)
     end.

Ltac reify_args_for_apply0 reify_Term var ret :=
  match constr:(Set) with
  | _ => constr:(ret noargs)
  | _ => cidtac_error "Failed to apply0" ret
  end.

Ltac reify_args_for_apply1 reify_Term var ret x :=
  let rx := reify_Term var x in
  match constr:(Set) with
  | _ => constr:(ret (an_arg rx noargs))
  | _ => cidtac_error "Failed to apply1" (ret, rx)
  end.

Ltac reify_args_for_apply2 reify_Term var ret x y :=
  let rx := reify_Term var x in
  let ry := reify_Term var y in
  match constr:(Set) with
  | _ => constr:(ret (an_arg rx (an_arg ry noargs)))
  | _ => cidtac_error "Failed to apply2" (ret, rx, ry)
  end.

Ltac reify_args_for_apply3 reify_Term var ret x y z :=
  let rx := reify_Term var x in
  let ry := reify_Term var y in
  let rz := reify_Term var z in
  match constr:(Set) with
  | _ => constr:(ret (an_arg rx (an_arg ry (an_arg rz noargs))))
  | _ => cidtac_error "Failed to apply3" (ret, rx, ry, rz)
  end.

Ltac reify_args_for_apply6 reify_Term var ret x y z a b c :=
  let rx := reify_Term var x in
  let ry := reify_Term var y in
  let rz := reify_Term var z in
  let ra := reify_Term var a in
  let rb := reify_Term var b in
  let rc := reify_Term var c in
  match constr:(Set) with
  | _ => constr:(ret (an_arg rx (an_arg ry (an_arg rz (an_arg ra (an_arg rb (an_arg rc noargs)))))))
  | _ => cidtac_error "Failed to apply6" (ret, rx, ry, rz, ra, rb, rc)
  end.


Class reif_Term_of {T T' T''} (var : T) (term : T') := Build_reif_Term_of : T''.

Ltac reify_Term var term
  := match eval cbv beta iota zeta in term with
     | context G[bool_rect (fun _ => ?T)]
       => let term' := context G[@bool_rect_nodep T] in reify_Term var term'
     | context G[@Reflective.ritem_rect ?A (fun _ => ?T)]
       => let term' := context G[@Reflective.ritem_rect_nodep A T] in reify_Term var term'
     | context G[@list_rect ?A (fun _ => ?T)]
       => let term' := context G[@list_rect_nodep A T] in reify_Term var term'
     | context G[@list_caset ?A (fun _ => ?T)]
       => let term' := context G[@list_caset_nodep A T] in reify_Term var term'
     | context G[if ?b then ?t else ?f]
       => let term' := context G[@bool_rect_nodep _ t f b] in reify_Term var term'
     | context G[?f ?v]
       => let test := match v with
                      | @fst _ _ => constr:(I)
                      | @snd _ _ => constr:(I)
                      | @Reflective.interp_RCharExpr _ _ _ => constr:(I)
                      | Equality.string_beq _ => constr:(I)
                      | @List.length _ => constr:(I)
                      end in
          let term' := context G[f (fun x => v x)] in reify_Term var term'
     | context G[?f ?v]
       => let test := match v with
                      | orb => constr:(I)
                      | orbr => constr:(I)
                      | andb => constr:(I)
                      | andbr => constr:(I)
                      | Equality.string_beq => constr:(I)
                      end in
          let term' := context G[f (fun x y => v x y)] in reify_Term var term'
     | ?term'
       => let Rterm := match term' with
                       | O => constr:(@RO)
                       | true => constr:(@Rbool true)
                       | false => constr:(@Rbool false)
                       end in
          let ret := reify_Term_lit0 var Rterm in
          reify_args_for_apply0 reify_Term var ret
     | ?term' ?x
       => let Rterm := match term' with
                       | S => constr:(@RS)
                       | pred => constr:(@Rpred)
                       | up_to => constr:(@Rup_to)
                       end in
          let ret := reify_Term_lit0 var Rterm in
          reify_args_for_apply1 reify_Term var ret x
     | ?term' ?x ?y
       => let Rterm := match term' with
                       | max => constr:(@Rmax)
                       | orb => constr:(@Rorb)
                       | andb => constr:(@Randb)
                       | orbr => constr:(@Rorbr)
                       | pred => constr:(@Rpred)
                       | plus => constr:(@Rplus)
                       | true => constr:(@Rbool true)
                       | false => constr:(@Rbool false)
                       | andbr => constr:(@Randbr)
                       | minusr => constr:(@Rminusr)
                       | Compare_dec.leb => constr:(@Rleb)
                       | EqNat.beq_nat => constr:(@Rbeq_nat)
                       | Equality.string_beq => constr:(@Rstring_beq)
                       | @Reflective.interp_RCharExpr _ _ => constr:(@Rinterp_RCharExpr_ascii)
                       end in
          let ret := reify_Term_lit0 var Rterm in
          reify_args_for_apply2 reify_Term var ret x y
     | ?term' ?A
       => let Rterm := match term' with
                       | @nil => constr:(@Rnil)
                       end in
          let ret := reify_Term_lit1 var A Rterm in
          reify_args_for_apply0 reify_Term var ret
     | ?term' ?A ?x
       => let Rterm := match term' with
                       | @List.rev => constr:(@Rrev)
                       | @List.length => constr:(@Rlength)
                       end in
          let ret := reify_Term_lit1 var A Rterm in
          reify_args_for_apply1 reify_Term var ret x
     | ?term' ?A ?x ?y
       => let Rterm := match term' with
                       | @cons => constr:(@Rcons)
                       end in
          let ret := reify_Term_lit1 var A Rterm in
          reify_args_for_apply2 reify_Term var ret x y
     | ?term' ?A ?x ?y ?z
       => let Rterm := match term' with
                       | @nth' => constr:(@Rnth')
                       | @List.nth => constr:(@Rnth)
                       | @bool_rect_nodep => constr:(@Rbool_rect_nodep)
                       | @first_index_default => constr:(@Rfirst_index_default)
                       | @Reflective.ritem_rect_nodep _ => constr:(@Rritem_rect_nodep)
                       end in
          let ret := reify_Term_lit1 var A Rterm in
          reify_args_for_apply3 reify_Term var ret x y z
     | ?term' ?A ?B ?x
       => let Rterm := match term' with
                       | @fst => constr:(@Rfst)
                       | @snd => constr:(@Rsnd)
                       end in
          let ret := reify_Term_lit2 var A B Rterm in
          reify_args_for_apply1 reify_Term var ret x
     | ?term' ?A ?B ?x ?y
       => let Rterm := match term' with
                       | @pair => constr:(@Rpair)
                       | @List.map => constr:(@Rmap)
                       | @List.combine => constr:(@Rcombine)
                       end in
          let ret := reify_Term_lit2 var A B Rterm in
          reify_args_for_apply2 reify_Term var ret x y
     | ?term' ?A ?B ?x ?y ?z
       => let Rterm := match term' with
                       | @List.fold_left => constr:(@Rfold_left)
                       | @list_rect_nodep => constr:(@Rlist_rect_nodep)
                       | @list_caset_nodep => constr:(@Rlist_caset_nodep)
                       end in
          let ret := reify_Term_lit2 var A B Rterm in
          reify_args_for_apply3 reify_Term var ret x y z
     | ?term' ?A ?B ?x ?y ?z ?a ?b ?c
       => let Rterm := match term' with
                       | @list_rect_nodep => constr:(@Rlist_rect_nodep)
                       end in
          let ret := reify_Term_lit2 var A B Rterm in
          reify_args_for_apply6 reify_Term var ret x y z a b c
     (*| split_string_for_production ?x ?str ?y ?z
       => let ret := reify_Term_lit0 var (@Rsplit_string_for_production) in
          reify_args_for_apply3 reify_Term var ret x y z
     | char_at_matches ?x ?str ?y
       => let ret := reify_Term_lit0 var (@Rchar_at_matches) in
          reify_args_for_apply2 reify_Term var ret x y*)
     | ?term'
       => match goal with
          | [ H : reif_Term_of var term' |- _ ]
            => H
          end
     | pregrammar_rproductions ?G
       => match constr:(Set) with
          | _ => constr:(syntactify_rproductions var (pregrammar_rproductions G))
          | _ => cidtac_error "Internal error on" (pregrammar_rproductions G)
          end
     | ?f ?x
       => let T := type of f in
          let T := (eval hnf in T) in
          let A := match T with ?A -> ?B => A end in
          let B := match T with ?A -> ?B => B end in
          let A' := reify_TypeCode A in
          let B' := reify_TypeCode B in
          let x' := reify_Term var x in
          let f' := reify_Term var f in
          constr:(@RApp var A' B' f' x')
     | (fun x : ?T => @?f x)
       => let T' := reify_TypeCode T in
          let res := match constr:(Set) with
                     | _ => constr:(fun (x : T) (v : var T')
                                    => let vx : reif_Term_of var x := (@RVar var T' v) in
                                       (_ : reif_Term_of var (f x)))
                     | _ => cidtac_error "Unable to reify function" f
                     end in
          let res := (eval cbv beta iota zeta in res) in
          let res := match res with
                     | (fun _ => ?f) => f
                     | _ => cidtac_error "Unable to remove first argument to" f
                     end in
          match constr:(Set) with
          | _ => constr:(@RLambda var T' _ res)
          | _ => cidtac_error "Type error" res
          end
     | ?term'
       => cidtac_error "Unable to reify term:" term'
     end.
Hint Extern 0 (reif_Term_of ?var ?term)
=> (let term' := reify_Term var term in eexact term') : typeclass_instances.

Module Exports.
  Export Syntax.Coercions.
  Export Coq.Strings.String.
  Open Scope string_scope.
End Exports.
