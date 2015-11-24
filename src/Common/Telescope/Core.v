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

  Fixpoint flattenT_eq {t : Telescope} {X : Type} : relation (flattenT t X)
    := match t return relation (flattenT t X) with
         | bottom => fun P Q => P = Q :> X
         | tele A B => fun P Q => forall a : A, flattenT_eq (P a) (Q a)
       end.

  Global Instance flattenT_eq_Reflexive {t : Telescope} {X : Type}
  : Reflexive (@flattenT_eq t X).
  Proof.
    repeat intro; induction t; simpl in *.
    { reflexivity. }
    { eauto with nocore. }
  Defined.

  Global Instance flattenT_eq_Symmetric {t : Telescope} {X : Type}
  : Symmetric (@flattenT_eq t X).
  Proof.
    repeat intro; induction t; simpl in *.
    { symmetry; assumption. }
    { eauto with nocore. }
  Defined.

  Global Instance flattenT_eq_Transitive {t : Telescope} {X : Type}
  : Transitive (@flattenT_eq t X).
  Proof.
    repeat intro; induction t; simpl in *.
    { etransitivity; eassumption. }
    { eauto with nocore. }
  Defined.

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

  Fixpoint flattenT_unapply_apply {t : Telescope} {X : Type} {struct t}
  : forall (f : flattenT t X),
      flattenT_eq f (flattenT_unapply (flattenT_apply f))
    := match t return forall (f : flattenT t X),
                        flattenT_eq f (flattenT_unapply (flattenT_apply f))
       with
         | bottom => fun f => eq_refl
         | tele A B => fun f x => @flattenT_unapply_apply (B x) X (f x)
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

  Fixpoint flatten_forall_eq_rect {t : Telescope}
  : forall {P Q : flattenT t Type},
      flattenT_eq P Q
      -> flatten_forall P
      -> flatten_forall Q
    := match t return forall {P Q : flattenT t Type},
                        flattenT_eq P Q
                        -> flatten_forall P
                        -> flatten_forall Q
       with
         | bottom => fun P Q H k => eq_rect _ (fun x => x) k _ H
         | tele A B => fun P Q H k a => @flatten_forall_eq_rect (B a) (P a) (Q a) (H a) (k a)
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

  Fixpoint flatten_forall_unapply_apply {t : Telescope} {struct t}
  : forall {P : flattenT t Type}
           (f : flatten_forall P),
      flatten_forall_eq
        (flatten_forall_eq_rect (flattenT_unapply_apply P) f)
        (flatten_forall_unapply (flatten_forall_apply f))
    := match t return forall {P : flattenT t Type}
                             (f : flatten_forall P),
                        flatten_forall_eq
                          (flatten_forall_eq_rect (flattenT_unapply_apply P) f)
                          (flatten_forall_unapply (flatten_forall_apply f))
       with
         | bottom => fun P f => eq_refl
         | tele A B => fun P f a => @flatten_forall_unapply_apply (B a) (P a) (f a)
       end.

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

  Lemma flatten_append_forall_Proper {B P Q}
  : forall f g,
      @flatten_forall_eq B P f g
      -> @flatten_append_forall B P Q f
      -> @flatten_append_forall B P Q g.
  Proof.
    induction B; simpl in *; eauto with nocore.
    intros; subst; assumption.
  Defined.

  Global Instance flattenT_unapply_Proper {t X}
  : Proper (pointwise_relation _ eq ==> flattenT_eq)
           (@flattenT_unapply t X).
  Proof.
    repeat intro; unfold pointwise_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flattenT_apply_Proper {t X}
  : Proper (flattenT_eq ==> pointwise_relation _ eq)
           (@flattenT_apply t X).
  Proof.
    repeat intro; unfold pointwise_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_unapply_Proper {t P}
  : Proper (forall_relation (fun _ => eq) ==> flatten_forall_eq)
           (@flatten_forall_unapply t P).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_apply_Proper {t P}
  : Proper (flatten_forall_eq ==> forall_relation (fun _ => eq))
           (@flatten_forall_apply t P).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore.
  Defined.

  Global Instance flatten_forall_eq_rect_Proper {t P Q H}
  : Proper (flatten_forall_eq ==> flatten_forall_eq)
           (@flatten_forall_eq_rect t P Q H).
  Proof.
    repeat intro; unfold forall_relation in *; induction t as [|?? IHt]; simpl in *;
    auto with nocore;
    subst; simpl; reflexivity.
  Defined.

  Fixpoint flatten_forall_eq_rect_trans {t : Telescope}
  : forall {P Q R : flattenT t Type}
           (p : flattenT_eq P Q)
           (q : flattenT_eq Q R)
           (f : flatten_forall P),
      flatten_forall_eq (flatten_forall_eq_rect (transitivity p q) f)
                        (flatten_forall_eq_rect q (flatten_forall_eq_rect p f)).
  Proof.
    refine match t return forall {P Q R : flattenT t Type}
                                 (p : flattenT_eq P Q)
                                 (q : flattenT_eq Q R)
                                 (f : flatten_forall P),
                            flatten_forall_eq (flatten_forall_eq_rect (transitivity p q) f)
                                              (flatten_forall_eq_rect q (flatten_forall_eq_rect p f))
           with
             | bottom => fun P Q H k => _
             | tele A B => fun P Q R p q f a => @flatten_forall_eq_rect_trans (B a) _ _ _ _ _ _
           end;
    simpl in *.
    { intros; subst; simpl; reflexivity. }
  Defined.

  Fixpoint flatten_forall_eq_rect_flattenT_unapply_Proper {t}
  : forall {P Q : flattenT_sig t -> Type}
           (H : forall x, P x = Q x)
           (f : forall x, P x),
      flatten_forall_eq
        (flatten_forall_eq_rect (@flattenT_unapply_Proper t _ P (fun x => Q x) H) (flatten_forall_unapply f))
        (flatten_forall_unapply (fun x => eq_rect _ (fun P => P) (f x) _ (H x)))
    := match t return forall {P Q : flattenT_sig t -> Type}
                             (H : forall x, P x = Q x)
                             (f : forall x, P x),
                        flatten_forall_eq
                          (flatten_forall_eq_rect (@flattenT_unapply_Proper t _ P (fun x => Q x) H) (flatten_forall_unapply f))
                          (flatten_forall_unapply (fun x => eq_rect _ (fun P => P) (f x) _ (H x)))
       with
         | bottom => fun P Q H k => eq_refl
         | tele A B => fun P Q H f a => @flatten_forall_eq_rect_flattenT_unapply_Proper (B a) _ _ _ _
       end.

  Fixpoint eq_rect_symmetry_flattenT_apply_unapply {t}
  : forall {f x k},
      eq_rect _ (fun T => T) (flatten_forall_apply (flatten_forall_unapply k) x) _ (eq_sym (@flattenT_apply_unapply t Type f x))
      = k x
    := match t return forall {f x k},
                        eq_rect _ (fun T => T) (flatten_forall_apply (flatten_forall_unapply k) x) _ (eq_sym (@flattenT_apply_unapply t Type f x))
                        = k x
       with
         | bottom => fun f x k => match x with
                                    | tt => eq_refl
                                  end
         | tele A'' B'' => fun f x k =>
                             match x with
                               | existT x1 x2
                                 => eq_trans
                                      (y := eq_rect
                                              _ (fun T => T)
                                              (flatten_forall_apply
                                                 (flatten_forall_unapply (fun x' => k (existT (fun x'' => flattenT_sig (B'' x'')) x1 x')))
                                                 x2)
                                              _
                                              (eq_sym (flattenT_apply_unapply (fun p => f (existT (fun x' => flattenT_sig (B'' x')) x1 p)) x2)))
                                      (f_equal (fun p' => eq_rect
                                                            _ (fun T => T)
                                                            (flatten_forall_apply
                                                               (flatten_forall_unapply (fun x' => k (existT (fun x'' => flattenT_sig (B'' x'')) x1 x')))
                                                               x2)
                                                            _
                                                            (eq_sym p'))
                                               (concat_1p _))
                                      (@eq_rect_symmetry_flattenT_apply_unapply (B'' x1) (fun x2' => f (existT (fun a => flattenT_sig (B'' a)) x1 x2')) x2 (fun x2' => k (existT (fun a => flattenT_sig (B'' a)) x1 x2')))
                             end
       end.

  Fixpoint flatten_forall_eq_rect_symmetry_flattenT_unapply_apply {t}
  : forall {f k},
      flatten_forall_eq
        (flatten_forall_eq_rect
           (symmetry (@flattenT_unapply_apply t Type f))
           (flatten_forall_unapply (flatten_forall_apply k)))
        k
    := match t return forall {f k},
                        flatten_forall_eq
                          (flatten_forall_eq_rect
                             (symmetry (@flattenT_unapply_apply t Type f))
                             (flatten_forall_unapply (flatten_forall_apply k)))
                          k
       with
         | bottom => fun f k => eq_refl
         | tele A'' B'' => fun f k a => @flatten_forall_eq_rect_symmetry_flattenT_unapply_apply (B'' a) (f a) (k a)
       end.
End Telescope.
