Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Classes.Morphisms.
Require Import Fiat.Common.Equality.

Module Export Telescope.
  Inductive Telescope := bottom | tele (A : Type) (B : A -> Telescope).

  Fixpoint flattenT (t : Telescope) (X : Type)
    := match t with
         | bottom => X
         | tele A B => forall a : A, flattenT (B a) X
       end.

  Global Arguments tele : clear implicits.

  Fixpoint flattenT_sig (t : Telescope)
    := match t return Type with
         | bottom => unit
         | tele A B => { a : A & flattenT_sig (B a) }
       end.

  Fixpoint flattenT_apply {t : Telescope} {X : Type}
  : flattenT t X -> flattenT_sig t -> X
    := match t return flattenT t X -> flattenT_sig t -> X with
         | bottom => fun x _ => x
         | tele A B => fun f p => flattenT_apply (f (projT1 p)) (projT2 p)
       end.

  Fixpoint flattenT_unapply {t : Telescope} {X : Type}
  : (flattenT_sig t -> X) -> flattenT t X
    := match t return (flattenT_sig t -> X) -> flattenT t X with
         | bottom => fun f => f tt
         | tele A B => fun f x => flattenT_unapply (fun p => f (existT (fun x' => flattenT_sig (B x')) x p))
       end.

  Fixpoint flattenT_apply_unapply {t : Telescope} {X : Type} {struct t}
  : forall (f : flattenT_sig t -> X)
           (x : flattenT_sig t),
      f x = flattenT_apply (flattenT_unapply f) x
    := match t return forall (f : flattenT_sig t -> X)
                             (x : flattenT_sig t),
                        f x = flattenT_apply (flattenT_unapply f) x
       with
         | bottom => fun f x => match x with
                                  | tt => eq_refl
                                end
         | tele A B => fun f x => eq_trans (f_equal f match x return x = existT (fun a => flattenT_sig (B a)) (projT1 x) (projT2 x) with
                                                        | existT _ _ => eq_refl
                                                      end)
                                           (@flattenT_apply_unapply
                                              (B (projT1 x)) X
                                              (fun p => f (existT (fun x' => flattenT_sig (B x')) (projT1 x) p))
                                              (projT2 x))
       end.

  Fixpoint Telescope_append (t : Telescope)
  : flattenT t Type -> Telescope
    := match t return flattenT t _ -> _ with
         | bottom => fun X => @tele X (fun _ => bottom)
         | tele A B => fun X => @tele A (fun a => Telescope_append (B a) (X a))
       end.

  Global Arguments Telescope_append : clear implicits.

  Fixpoint flatten_forall {t : Telescope} : flattenT t Type -> Type
    := match t return flattenT t Type -> Type with
         | bottom => fun P => P
         | tele A B => fun P => forall a : A, flatten_forall (P a)
       end.

  Fixpoint flatten_forall_apply {t : Telescope}
  : forall {P : flattenT t Type},
      flatten_forall P
      -> forall x : flattenT_sig t,
           flattenT_apply P x
    := match t
             return forall {P : flattenT t Type},
                      flatten_forall P
                      -> forall x : flattenT_sig t,
                           flattenT_apply P x
       with
         | bottom => fun X x _ => x
         | tele A B => fun P f x => @flatten_forall_apply (B (projT1 x)) _ (f (projT1 x)) (projT2 x)
       end.

  Fixpoint flatten_forall_unapply {t : Telescope}
  : forall {P : flattenT_sig t -> Type},
      (forall x : flattenT_sig t, P x)
      -> flatten_forall (flattenT_unapply P)
    := match t
             return forall {P : flattenT_sig t -> Type},
                      (forall x : flattenT_sig t, P x)
                      -> flatten_forall (flattenT_unapply P)
       with
         | bottom => fun X x => x tt
         | tele A B => fun P f x => @flatten_forall_unapply (B x) _ (fun x' => f _)
       end.

  Fixpoint flatten_forall_apply_unapply {t : Telescope} {struct t}
  : forall {P : flattenT_sig t -> Type}
           (f : forall x, P x)
           (x : flattenT_sig t),
      eq_rect _ (fun Px => Px) (f x) _ (flattenT_apply_unapply P x)
      = flatten_forall_apply (flatten_forall_unapply f) x.
  Proof.
    refine match t return forall {P : flattenT_sig t -> Type}
                                 (f : forall x, P x)
                                 (x : flattenT_sig t),
                            eq_rect _ (fun Px => Px) (f x) _ (flattenT_apply_unapply P x)
                            = flatten_forall_apply (flatten_forall_unapply f) x
           with
             | bottom => fun f x ttt => match ttt with
                                          | tt => eq_refl
                                        end
             | tele A B => fun f x x' => eq_trans
                                           _
                                           (@flatten_forall_apply_unapply (B (projT1 x')) _ _ _)
           end.
    destruct x'; simpl in *.
    refine (f_equal _ (concat_1p _)).
  Defined.

  Fixpoint flatten_append_forall {t : Telescope}
  : forall {t' : flattenT t Type},
      flattenT (Telescope_append t t') Type -> flatten_forall t' -> Type
    := match t return forall {t' : flattenT t _},
                        flattenT (Telescope_append t t') Type
                        -> flatten_forall t'
                        -> Type
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
