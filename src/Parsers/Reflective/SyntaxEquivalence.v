(** * Equivalence on syntax *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.Reflective.Syntax.

Local Open Scope list_scope.

Section Term_equiv.
  Context (var1 var2 : TypeCode -> Type).

  Definition vpair := { t : TypeCode & var1 t * var2 t }%type.
  Definition vars t (x1 : var1 t) (x2 : var2 t) : vpair := existT _ _ (x1, x2).
  Definition ctxt := list vpair.

  Local Unset Elimination Schemes.
  Inductive Term_equiv : ctxt -> forall {t}, Term var1 t -> Term var2 t -> Prop :=
  | EqVar : forall G t (v1 : var1 t) v2,
    List.In (vars v1 v2) G
    -> Term_equiv G (#v1) (#v2)

  | EqLiteralApp : forall G T f v1 v2,
      args_for_related_ind (@Term_equiv G) v1 v2
      -> Term_equiv G (@RLiteralApp var1 T f v1) (@RLiteralApp var2 T f v2)

  | EqApp : forall G t1 t2 (f1 : Term _ (t1 --> t2)) (x1 : Term _ t1) f2 x2,
    Term_equiv G f1 f2
    -> Term_equiv G x1 x2
    -> Term_equiv G (f1 @ x1) (f2 @ x2)
  | EqLambda : forall G t1 t2 (f1 : var1 t1 -> Term var1 t2) f2,
    (forall v1 v2, Term_equiv (vars v1 v2 :: G) (f1 v1) (f2 v2))
    -> Term_equiv G (RLambda f1) (RLambda f2).

  Section ind_in.
    Context (P : ctxt -> forall t, Term var1 t -> Term var2 t -> Prop)
            (EqVarCase : forall G t v1 v2,
                In (vars v1 v2) G -> P G t (#v1)%term (#v2)%term)
            (EqLiteralAppCase : forall G T f v1 v2,
                args_for_related_ind (@Term_equiv G) v1 v2
                -> (forall A vv1 vv2, @aIn2 _ _ A _ vv1 vv2 v1 v2
                                      -> P G A vv1 vv2)
                -> P G (range_of T) (RLiteralApp f v1) (RLiteralApp f v2))
            (EqAppCase : forall G t1 t2 f1 x1 f2 x2,
                Term_equiv G f1 f2
                -> P G (t1 --> t2)%typecode f1 f2
                -> Term_equiv G x1 x2
                -> P G t1 x1 x2
                -> P G t2 (f1 @ x1)%term (f2 @ x2)%term)
            (EqLambdaCase : forall G t1 t2 f2 f3,
                (forall v1 v2, Term_equiv (vars v1 v2 :: G) (f2 v1) (f3 v2))
                -> (forall v1 v2, P (vars v1 v2 :: G) t2 (f2 v1) (f3 v2))
                -> P G (t1 --> t2)%typecode (\ x, f2 x)%term (\ x, f3 x)%term).

    Fixpoint Term_equiv_ind_in (c : ctxt) (t : TypeCode) (t0 : Term var1 t) (t1 : Term var2 t)
             (H : @Term_equiv c t t0 t1)
      : @P c t t0 t1.
    Proof.
      refine match H in @Term_equiv c t t0 t1 return @P c t t0 t1 with
             | EqVar G t v1 v2 x => EqVarCase _ _ _ x
             | EqLiteralApp G T f v1 v2 x => EqLiteralAppCase _ x _
             | EqApp G t1 t2 f1 x1 f2 x2 x x0 => EqAppCase
                                                   x
                                                   (@Term_equiv_ind_in _ _ _ _ x)
                                                   x0
                                                   (@Term_equiv_ind_in _ _ _ _ x0)
             | EqLambda G t1 t2 f1 f2 x => EqLambdaCase _ _ x (fun v1 v2 => @Term_equiv_ind_in _ _ _ _ (x v1 v2))
             end.
      clear f.
      induction x as [A B ?? x xs e es IHxs|].
      { specialize (Term_equiv_ind_in G _ _ _ e).
        simpl.
        intros ??? [[pf [H0 H1]]|H'].
        { destruct pf, H0, H1; simpl.
          exact Term_equiv_ind_in. }
        { apply IHxs; assumption. } }
      { simpl.
        intros ??? []. }
    Qed.
  End ind_in.

  Section ind.
    Context (P : ctxt -> forall t, Term var1 t -> Term var2 t -> Prop)
            (EqVarCase : forall G t v1 v2,
                In (vars v1 v2) G -> P G t (#v1)%term (#v2)%term)
            (EqLiteralAppCase : forall G T f v1 v2,
                args_for_related_ind (@Term_equiv G) v1 v2
                -> args_for_related_ind (@P G) v1 v2
                -> P G (range_of T) (RLiteralApp f v1) (RLiteralApp f v2))
            (EqAppCase : forall G t1 t2 f1 x1 f2 x2,
                Term_equiv G f1 f2
                -> P G (t1 --> t2)%typecode f1 f2
                -> Term_equiv G x1 x2
                -> P G t1 x1 x2
                -> P G t2 (f1 @ x1)%term (f2 @ x2)%term)
            (EqLambdaCase : forall G t1 t2 f2 f3,
                (forall v1 v2, Term_equiv (vars v1 v2 :: G) (f2 v1) (f3 v2))
                -> (forall v1 v2, P (vars v1 v2 :: G) t2 (f2 v1) (f3 v2))
                -> P G (t1 --> t2)%typecode (\ x, f2 x)%term (\ x, f3 x)%term).

    Fixpoint Term_equiv_ind (c : ctxt) (t : TypeCode) (t0 : Term var1 t) (t1 : Term var2 t)
             (H : @Term_equiv c t t0 t1)
      : @P c t t0 t1.
    Proof.
      refine match H in @Term_equiv c t t0 t1 return @P c t t0 t1 with
             | EqVar G t v1 v2 x => EqVarCase _ _ _ x
             | EqLiteralApp G T f v1 v2 x => EqLiteralAppCase _ x _
             | EqApp G t1 t2 f1 x1 f2 x2 x x0 => EqAppCase
                                                   x
                                                   (@Term_equiv_ind _ _ _ _ x)
                                                   x0
                                                   (@Term_equiv_ind _ _ _ _ x0)
             | EqLambda G t1 t2 f1 f2 x => EqLambdaCase _ _ x (fun v1 v2 => @Term_equiv_ind _ _ _ _ (x v1 v2))
             end.
      clear f.
      induction x as [A B ?? x xs e es IHxs|].
      { specialize (Term_equiv_ind G _ _ _ e).
        simpl.
        constructor.
        { exact Term_equiv_ind. }
        { exact IHxs. } }
      { simpl.
        constructor. }
    Qed.
  End ind.
End Term_equiv.

Arguments vars {var1 var2 t} _ _.
(*
Definition invert_args_for_equiv {var1 var2 G T v1 v2}
           (H : @args_for_equiv var1 var2 G T v1 v2)
  : match T return args_for var1 T -> args_for var2 T -> Prop
    with
    | csimple _ => fun v1 v2 => v1 = noargs /\ v2 = noargs
    | carrow A B
      => fun v1 v2
         => exists h1 t1 h2 t2,
             v1 = an_arg h1 t1 /\ v2 = an_arg h2 t2
             /\ Term_equiv G h1 h2
             /\ args_for_equiv G t1 t2
    end v1 v2.
Proof.
  destruct H; repeat esplit; assumption.
Defined.
*)
