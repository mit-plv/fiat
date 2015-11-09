Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Classes.Morphisms.

Module Export Telescope.
  Inductive Telescope := bottom | tele (A : Type) (B : A -> Telescope).

  Fixpoint flattenT (t : Telescope) (X : Type)
    := match t with
         | bottom => X
         | tele A B => forall a : A, flattenT (B a) X
       end.

  Fixpoint Telescope_append (t : Telescope)
  : flattenT t Type -> Telescope
    := match t return flattenT t _ -> _ with
         | bottom => fun X => @tele X (fun _ => bottom)
         | tele A B => fun X => @tele A (fun a => Telescope_append (B a) (X a))
       end.

  Global Arguments Telescope_append : clear implicits.

  Fixpoint flatten_forall {t : Telescope} : flattenT t Type -> Type
    := match t return flattenT t _ -> _ with
         | bottom => fun P => P
         | tele A B => fun P => forall a : A, flatten_forall (P a)
       end.

  Fixpoint flatten_append_forall {t : Telescope}
  : forall {t' : flattenT t Type},
      flattenT (Telescope_append t t') Type -> flatten_forall t' -> Type
    := match t return forall {t' : flattenT t _},
                        flattenT (Telescope_append t t') _
                        -> flatten_forall t'
                        -> _
       with
         | bottom => fun t' P v => P v
         | tele A B => fun t' P v => forall a, @flatten_append_forall (B a) (t' a) (P a) (v a)
       end.

  Fixpoint flatten_forall_eq_relation {t : Telescope}
  : forall {P : flattenT t Type},
      relation (flatten_forall P)
    := match t
             return forall {P : flattenT t _},
                      relation (flatten_forall P)
       with
         | bottom => fun P => eq
         | tele A B => fun P => forall_relation (fun a : A => @flatten_forall_eq_relation (B a) (P a))
       end.

  Definition flatten_forall_eq {t : Telescope}
  : forall {P : flattenT t Type}
           (f g : flatten_forall P),
      Prop
    := Eval unfold flatten_forall_eq_relation, forall_relation in @flatten_forall_eq_relation t.

  Global Instance flatten_forall_eq_relation_Reflexive {t P}
  : Reflexive (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ reflexivity | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_Symmetric {t P}
  : Symmetric (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ symmetry; assumption | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_relation_Transitive {t P}
  : Transitive (@flatten_forall_eq_relation t P).
  Proof.
    hnf; induction t; simpl; unfold forall_relation; [ etransitivity; eassumption | eauto with nocore ].
  Defined.

  Global Instance flatten_forall_eq_Reflexive {t P}
  : Reflexive (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Reflexive.

  Global Instance flatten_forall_eq_Symmetric {t P}
  : Symmetric (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Symmetric.

  Global Instance flatten_forall_eq_Transitive {t P}
  : Transitive (@flatten_forall_eq t P)
    := flatten_forall_eq_relation_Transitive.

  Lemma flatten_append_forall_Proper {B P Q}
  : forall f g,
      @flatten_forall_eq B P f g
      -> @flatten_append_forall B P Q f
      -> @flatten_append_forall B P Q g.
  Proof.
    induction B; simpl in *; eauto with nocore.
    intros; subst; assumption.
  Defined.
End Telescope.
