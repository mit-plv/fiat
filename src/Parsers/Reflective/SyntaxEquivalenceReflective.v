(** * Equivalence on syntax *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat Coq.Logic.Eqdep_dec.
Require Import Fiat.Parsers.Reflective.Syntax.
Require Import Fiat.Parsers.Reflective.SyntaxEquality.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.
Require Import Fiat.Common.PointedProp.
Require Import Fiat.Common.OptionFacts.
Require Import Fiat.Common.Prod.
Require Import Fiat.Common.Sigma.
Require Import Fiat.Common.

Local Open Scope list_scope.

Section Term_equiv.
  Context (var1 var2 : TypeCode -> Type).

  Local Notation nvar1 t := (nat * var1 t)%type.
  Local Notation fnvar1 := (fun t => nvar1 t).
  Local Notation nvar2 t := (nat * var2 t)%type.
  Local Notation fnvar2 := (fun t => nvar2 t).
  Local Notation eP := (fun t : TypeCode => var1 t * var2 t)%type (only parsing).
  Local Notation eP2 := (fun t : TypeCode * TypeCode => var1 (fst t) * var2 (snd t))%type (only parsing).
  Local Notation vpair := (sigT eP).
  Local Notation vpair2 := (sigT eP2).
  Local Notation vars x1 x2 := (existT eP _ (x1, x2)).
  Local Notation vars2 x1 x2 := (existT eP2 (_, _) (x1, x2)).
  Local Notation ctxt := (list vpair).
  Local Notation ctxt2 := (list vpair2).

  Definition duplicate_type (ls : list (sigT eP)) : list (sigT eP2)
    := List.map (fun v => existT eP2 (projT1 v, projT1 v) (projT2 v)) ls.

  Local Ltac inversion_TypeCode_step :=
    match goal with
    | [ H : ?x = ?x :> TypeCode |- _ ]
      => assert (H = eq_refl) by eapply UIP_dec, TypeCode_eq_dec; subst H
    | [ H : ?x = ?x :> SimpleTypeCode |- _ ]
      => assert (H = eq_refl) by eapply UIP_dec, SimpleTypeCode_eq_dec; subst H
    | [ H : ?x = ?y :> TypeCode |- _ ] => subst x || subst y
    | [ H : ?x = ?y :> SimpleTypeCode |- _ ] => subst x || subst y
    end.
  Local Ltac inversion_TypeCode := repeat inversion_TypeCode_step.

  Lemma duplicate_type_in t v ls
    : List.In (existT _ (t, t) v) (duplicate_type ls) -> List.In (existT _ t v) ls.
  Proof.
    unfold duplicate_type; rewrite List.in_map_iff.
    intros [ [? ?] [? ?] ].
    inversion_sigma; inversion_prod; inversion_TypeCode; subst; simpl.
    assumption.
  Qed.
  Lemma duplicate_type_length ls
    : List.length (duplicate_type ls) = List.length ls.
  Proof. apply List.map_length. Qed.

  Definition eq_semidec_and_gen {T} (semidec : forall x y : T, option (x = y))
             (t t' : T) (f : T -> Type) (x : f t) (x' : f t')
    : option pointed_Prop
    := match semidec t t' with
       | Some p
         => Some (inject (eq_rect _ f x _ p = x'))
       | None => None
       end.

  (* Here is where we use the generality of [pointed_Prop], to say
     that two things of type [var1] are equal, and two things of type
     [var2] are equal. *)
  Definition eq_type_and_var : sigT eP2 -> sigT eP2 -> option pointed_Prop
    := fun x y => (eq_semidec_and_gen
                  TypeCode_eq_semidec_transparent _ _ var1 (fst (projT2 x)) (fst (projT2 y))
                /\ eq_semidec_and_gen
                     TypeCode_eq_semidec_transparent _ _ var2 (snd (projT2 x)) (snd (projT2 y)))%option_pointed_prop.

  (* This function strips De Bruijn indices from expressions *)
  Fixpoint unnatize_Term {var t} (base : nat) (e : @Term (fun t => nat * var t)%type t) : @Term var t
    := match e in @Term _ t return @Term _ t with
       | RVar T v => RVar (snd v)
       | RLambda A B f => RLambda (fun x => @unnatize_Term _ _ (S base) (f (base, x)))
       | RApp A B f x => RApp (@unnatize_Term _ _ base f) (@unnatize_Term _ _ base x)
       | RLiteralApp c t args =>  RLiteralApp t (map_args_for (fun t => @unnatize_Term _ t base) args)
       end.

  Section args_for_requivT.
    Context {var1' var2' : TypeCode -> Type}
            (f : forall t1 t2, var1' t1 -> var2' t2 -> option pointed_Prop).
    Fixpoint args_for_requivT {t1 t2} (e1 : args_for var1' t1) (e2 : args_for var2' t2)
      : option pointed_Prop
      := match e1, e2 with
         | noargs T1, noargs T2
           => if SimpleTypeCode_beq T1 T2 then Some trivial else None
         | noargs _, _ => None
         | an_arg tx txs x xs, an_arg ty tys y ys
           => match TypeCode_beq tx ty, f x y, @args_for_requivT _ _ xs ys with
              | true, Some p, Some q => Some (p /\ q)%pointed_prop
              | _, _, _ => None
              end
         | an_arg _ _ _ _, _ => None
         end.
  End args_for_requivT.

  Fixpoint Term_requivT (G : ctxt2) {t1 t2} (e1 : Term fnvar1 t1) (e2 : Term fnvar2 t2) {struct e1}
    : option pointed_Prop
    := match e1, e2 return option _ with
       | RVar t0 x, RVar t1 y
         => match beq_nat (fst x) (fst y), List.nth_error G (List.length G - S (fst x)) with
            | true, Some v => eq_type_and_var v (existT _ (t0, t1) (snd x, snd y))
            | _, _ => None
            end
       | RVar _ _, _ => None
       | RLambda A1 B1 f1, RLambda A2 B2 f2
         => match TypeCode_eq_semidec_transparent A1 A2, TypeCode_eq_semidec_transparent B1 B2 with
            | Some _, Some _
              => Some (inject (forall (v1 : var1 A1) (v2 : var2 A2),
                                  match @Term_requivT (vars2 v1 v2 :: G)
                                                      B1 B2
                                                      (f1 (List.length G, v1))
                                                      (f2 (List.length G, v2))
                                  with
                                  | Some p => to_prop p
                                  | None => False
                                  end))
            | _, _ => None
            end
       | RLambda _ _ _, _ => None
       | RApp tx tC eC ex, RApp tx' tC' eC' ex'
         => match TypeCode_beq tx tx', TypeCode_beq tC tC',
                  @Term_requivT G _ _ eC eC', @Term_requivT G _ _ ex ex' with
            | true, true, Some p, Some q
              => Some (p /\ q)%pointed_prop
            | _, _, _, _ => None
            end
       | RApp _ _ _ _, _ => None
       | RLiteralApp c1 t1 args1, RLiteralApp c2 t2 args2
         => if RLiteralTerm_beq t1 t2
            then args_for_requivT (@Term_requivT G) args1 args2
            else None
       | RLiteralApp _ _ _, _ => None
       end.

  Local Ltac t_step :=
    idtac;
    match goal with
    | _ => progress unfold eq_type_and_var, option_map, and_option_pointed_Prop, eq_semidec_and_gen in *
    | _ => progress simpl in *
    | _ => progress break_match
    | _ => progress subst
    | _ => progress inversion_option
    | _ => progress inversion_pointed_Prop
    | _ => progress inversion_TypeCode
    | _ => congruence
    | _ => tauto
    | _ => progress specialize_by tauto
    | _ => progress intros
    | [ v : sigT _ |- _ ] => destruct v
    | [ v : sig _ |- _ ] => destruct v
    | [ v : prod _ _ |- _ ] => destruct v
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : ?x = ?y |- _ ] => subst x || subst y
    | [ H : RLiteralTerm_beq _ _ = true |- _ ]
      => apply RLiteralTerm_beq_bl in H
    | [ H : TypeCode_beq _ _ = true |- _ ]
      => apply internal_TypeCode_dec_bl in H
    | [ H : SimpleTypeCode_beq _ _ = true |- _ ]
      => apply internal_SimpleTypeCode_dec_bl in H
    | [ H : context[List.length (duplicate_type _)] |- _ ]
      => rewrite duplicate_type_length in H
    | [ H : forall v1' v2', _ |- Term_equiv (SyntaxEquivalence.vars ?v1 ?v2 :: ?G) _ _ ]
      => specialize (H v1 v2)
    | [ H : forall v1' v1'' v2', _ |- Term_equiv (SyntaxEquivalence.vars ?v1 ?v2 :: ?G) _ _ ]
      => specialize (H v1 v1 v2)
    | [ H : forall t1 t2 a1 a2, _ |- args_for_related_ind _ (map_args_for _ ?args) (map_args_for _ ?args') ]
      => specialize (H _ _ args args')
    (*| [ H : List.nth_error _ _ = Some _ |- _ ] => apply List.nth_error_In in H*)
    | [ H : List.In _ (duplicate_type _) |- _ ] => apply duplicate_type_in in H
    | [ H : context[match _ with _ => _ end] |- _ ] => revert H; progress break_match
    | [ H : TypeCode_eq_semidec_transparent _ _ = None |- _ ] => apply TypeCode_eq_semidec_is_dec in H
    | [ |- Term_equiv _ _ _ ] => constructor
    | [ |- args_for_related_ind _ _ _ ] => constructor
    | _ => progress unfold and_pointed_Prop in *
    end.

  Local Ltac t := repeat t_step.

  Section args_for_requiv.
    Context (Term_requivT : forall t1 t2, Term fnvar1 t1 -> Term fnvar2 t2 -> option pointed_Prop)
            (Term_equiv : forall t, Term var1 t -> Term var2 t -> Prop)
            (unnatize_Term : forall var t, Term (fun t => nat * var t)%type t -> Term var t)
            (Term_requiv : forall t1 t2 (e1 : Term fnvar1 t1) (e2 : Term fnvar2 t2),
                match Term_requivT _ _ e1 e2, TypeCode_eq_semidec_transparent t1 t2 with
                | Some reflective_obligation, Some p
                  => to_prop reflective_obligation
                     -> @Term_equiv t2 (eq_rect _ (@Term _) (unnatize_Term _ _ e1) _ p) (unnatize_Term _ _ e2)
                | _, _ => True
                end).

    Fixpoint args_for_requiv
             {t1 t2}
             (e1 : args_for (Term fnvar1) t1) (e2 : args_for (Term fnvar2) t2)
             {struct e1}
      : match args_for_requivT Term_requivT e1 e2, TypeCode_eq_semidec_transparent t1 t2 with
        | Some reflective_obligation, Some p
          => to_prop reflective_obligation
             -> args_for_related_ind
                  Term_equiv
                  (eq_rect _ (@args_for _) (map_args_for (unnatize_Term _) e1) _ p)
                  (map_args_for (unnatize_Term _) e2)
        | _, _ => True
        end.
    Proof.
      destruct e1 as [ A B x xs | ], e2 as [ A' B' y ys | ]; simpl; try solve [ exact I ];
        [ specialize (@args_for_requiv _ _ xs ys); pose proof (@Term_requiv _ _ x y); clear Term_requiv
        | clear Term_requiv args_for_requiv ];
        t.
    Defined.
  End args_for_requiv.

  Fixpoint Term_requiv (G : ctxt)
           {t1 t2}
           (e1 : Term fnvar1 t1) (e2 : Term fnvar2 t2)
           {struct e1}
    : match Term_requivT (duplicate_type G) e1 e2, TypeCode_eq_semidec_transparent t1 t2 with
      | Some reflective_obligation, Some p
        => to_prop reflective_obligation
           -> @Term_equiv var1 var2 G t2 (eq_rect _ (@Term _) (unnatize_Term (List.length G) e1) _ p) (unnatize_Term (List.length G) e2)
      | _, _ => True
      end.
  Proof.
    destruct e1 as [ | A B f | A B f x | c f args ],
                   e2 as [ | A' B' f' | A' B' f' x' | c' f' args' ]; simpl; try solve [ exact I ];
      [ clear Term_requiv
      | specialize (fun v1 v1' v2 => @Term_requiv (vars v1' v2 :: G) _ _
                                                  (f (List.length G, v1))
                                                  (f' (List.length G, v2)))
      | pose proof (@Term_requiv G _ _ f f'); pose proof (@Term_requiv G _ _ x x'); clear Term_requiv
      | pose proof (@args_for_requiv (@Term_requivT (duplicate_type G)) (@Term_equiv _ _ G) (fun var t => @unnatize_Term var t (List.length G)) (@Term_requiv G)); clear Term_requiv ];
      t.
  Abort.

  Context (Term_requiv : forall (G : ctxt)
           {t1 t2}
           (e1 : Term fnvar1 t1) (e2 : Term fnvar2 t2),
              match Term_requivT (duplicate_type G) e1 e2, TypeCode_eq_semidec_transparent t1 t2 with
              | Some reflective_obligation, Some p
                => to_prop reflective_obligation
                   -> @Term_equiv var1 var2 G t2 (eq_rect _ (@Term _) (unnatize_Term (List.length G) e1) _ p) (unnatize_Term (List.length G) e2)
              | _, _ => True
              end).

  Lemma Term_requiv_onetype (G : ctxt) {t}
        (e1 : Term fnvar1 t) (e2 : Term fnvar2 t)
    : prop_of_option (Term_requivT (duplicate_type G) e1 e2)
      -> @Term_equiv var1 var2 G t (unnatize_Term (List.length G) e1) (unnatize_Term (List.length G) e2).
  Proof. pose proof (@Term_requiv G t t e1 e2) as H; t. Qed.
End Term_equiv.

Ltac generalize_reflect_Term_equiv :=
  lazymatch goal with
  | [ |- @Term_equiv ?var1 ?var2 ?G ?t ?e1 ?e2 ]
    => let e1 := match (eval pattern var1 in e1) with ?e _ => e end in
       let e2 := match (eval pattern var2 in e2) with ?e _ => e end in
       generalize (@Term_requiv_onetype var1 var2 G t (e1 _) (e2 _))
  end.
Ltac use_reflect_Term_equiv := vm_compute; let H := fresh in intro H; apply H; clear H.
Ltac fin_reflect_Term_equiv := repeat constructor.
(** The tactic [reflect_Term_equiv] is the main tactic of this file, used to
    prove [Syntax.Term_equiv] goals *)
Ltac reflect_Term_equiv :=
  generalize_reflect_Term_equiv;
  use_reflect_Term_equiv; fin_reflect_Term_equiv.
(*
Section Wf.
  Context {t1 : TypeCode}
          (e1 : @Expr base_type_code interp_base_type op t).

  Term_requiv (G : ctxt)
           {t1 t2}
           (e1 : Term fnvar1 t1) (e2 : Term fnvar2 t2)
           {struct e1}
    : match Term_requivT (duplicate_type G) e1 e2, TypeCode_eq_semidec_transparent t1 t2 with
      | Some reflective_obligation, Some p
        => to_prop reflective_obligation
           -> @Term_equiv var1 var2 G t2 (eq_rect _ (@Term _) (unnatize_Term (List.length G) e1) _ p) (unnatize_Term (List.length G) e2)
      | _, _ => True
      end.

  (** Leads to smaller proofs, but is less generally applicable *)
  Theorem reflect_Wf_unnatize
    : (forall var1 var2,
          prop_of_option (@reflect_wfT base_type_code interp_base_type base_type_eq_semidec_transparent op op_beq var1 var2 nil t t (e _) (e _)))
      -> Wf (fun var => unnatize_expr base_type_code interp_base_type op 0 (e (fun t => (nat * var t)%type))).
  Proof.
    intros H var1 var2; specialize (H var1 var2).
    pose proof (@reflect_wf base_type_code interp_base_type base_type_eq_semidec_transparent base_type_eq_semidec_is_dec op op_beq op_beq_bl var1 var2 nil t t (e _) (e _)) as H'.
    rewrite type_eq_semidec_transparent_refl in H' by assumption; simpl in *.
    edestruct reflect_wfT; simpl in *; tauto.
  Qed.

  Context (base_type_code : Type)
          (interp_base_type : base_type_code -> Type)
          (base_type_eq_semidec_transparent : forall t1 t2 : base_type_code, option (t1 = t2))
          (base_type_eq_semidec_is_dec : forall t1 t2, base_type_eq_semidec_transparent t1 t2 = None -> t1 <> t2)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (op_beq : forall t1 tR, op t1 tR -> op t1 tR -> option pointed_Prop)
          (op_beq_bl : forall t1 tR x y, prop_of_option (op_beq t1 tR x y) -> x = y)
          {t : type base_type_code}
          (e : @Expr base_type_code interp_base_type op t).


  (** Leads to larger proofs (an extra constant factor which is the
      size of the expression tree), but more generally applicable *)
  Theorem reflect_Wf
    : (forall var1 var2,
          unnatize_expr base_type_code interp_base_type op 0 (e (fun t => (nat * var1 t)%type)) = e _
          /\ prop_of_option (@reflect_wfT base_type_code interp_base_type base_type_eq_semidec_transparent op op_beq var1 var2 nil t t (e _) (e _)))
      -> Wf e.
  Proof.
    intros H var1 var2.
    rewrite <- (proj1 (H var1 var2)), <- (proj1 (H var2 var2)).
    apply reflect_Wf_unnatize, H.
  Qed.
End Wf.


*)
