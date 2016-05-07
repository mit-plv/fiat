(** * Equivalence on syntax *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.Reflective.Syntax.

Local Open Scope list_scope.

Section Term_equiv.
  Context (var1 var2 : TypeCode -> Type).

  Definition vpair := { t : TypeCode & var1 t * var2 t }%type.
  Definition vars t (x1 : var1 t) (x2 : var2 t) : vpair := existT _ _ (x1, x2).
  Definition ctxt := list vpair.

  Inductive Term_equiv : ctxt -> forall {t}, Term var1 t -> Term var2 t -> Prop :=
  | EqVar : forall G t (v1 : var1 t) v2,
    List.In (vars v1 v2) G
    -> Term_equiv G (#v1) (#v2)

  | EqLiteralApp : forall G T f v1 v2,
      args_for_equiv G v1 v2
      -> Term_equiv G (@RLiteralApp var1 T f v1) (@RLiteralApp var2 T f v2)

  | EqApp : forall G t1 t2 (f1 : Term _ (t1 --> t2)) (x1 : Term _ t1) f2 x2,
    Term_equiv G f1 f2
    -> Term_equiv G x1 x2
    -> Term_equiv G (f1 @ x1) (f2 @ x2)
  | EqLambda : forall G t1 t2 (f1 : var1 t1 -> Term var1 t2) f2,
    (forall v1 v2, Term_equiv (vars v1 v2 :: G) (f1 v1) (f2 v2))
    -> Term_equiv G (RLambda f1) (RLambda f2)
  with args_for_equiv : ctxt -> forall {t}, args_for var1 t -> args_for var2 t -> Prop :=
       | Eq_an_arg {G A B} (arg1 : Term var1 A) (arg2 : Term var2 A)
                   (args1 : args_for var1 B) (args2 : args_for var2 B)
         : Term_equiv G arg1 arg2
           -> args_for_equiv G args1 args2
           -> args_for_equiv G (an_arg arg1 args1) (an_arg arg2 args2)
       | Eq_noargs {G T} : args_for_equiv G (@noargs var1 T) (@noargs var2 T).
End Term_equiv.

Arguments vars {var1 var2 t} _ _.

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
