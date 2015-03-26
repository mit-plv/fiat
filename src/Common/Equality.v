Require Import Coq.Lists.List.

Set Implicit Arguments.
Local Close Scope nat_scope.

Definition pr1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
: projT1 u = projT1 v
  := f_equal (@projT1 _ _) p.

Definition pr2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
: eq_rect _ _ (projT2 u) _ (pr1_path p) = projT2 v.
Proof.
  destruct p; reflexivity.
Defined.

Lemma in_map_iff_injective {A B} (f : A -> B) (l : list A) (y : A)
      (f_injective : forall x, f x = f y -> x = y)
: In (f y) (map f l) <-> In y l.
Proof.
  split; intro H.
  { apply in_map_iff in H.
    destruct H as [x [H H']].
    apply f_injective in H.
    subst; assumption. }
  { apply in_map_iff.
    exists y; split; trivial. }
Qed.

Section option.
  Context {A : Type}.

  Definition option_code (x y : option A) : Prop
    := match x, y with
         | Some x', Some y' => x' = y'
         | None, None => True
         | _, _ => False
       end.

  Definition option_code_idpath {x} : option_code x x
    := match x return option_code x x with
         | Some _ => eq_refl
         | None => I
       end.

  Definition option_encode {x y} (p : x = y) : option_code x y
    := eq_rect _ _ option_code_idpath _ p.

  Definition option_decode {x y} : option_code x y -> x = y
    := match x, y return option_code x y -> x = y with
         | Some x', Some y' => @f_equal _ _ (@Some _) _ _
         | None, None => fun _ => eq_refl
         | _, _ => fun H => match H : False with end
       end.

  Definition option_deenecode {x y} (p : x = y)
  : option_decode (option_encode p) = p.
  Proof.
    destruct p, x; reflexivity.
  Defined.

  Definition option_endecode {x y} (p : option_code x y)
  : option_encode (option_decode p) = p.
  Proof.
    destruct x, y, p; reflexivity.
  Defined.

  Definition Some_injective {x y : A} : Some x = Some y -> x = y
    := option_encode.
End option.

Section sum.
  Context {A B : Type}.

  Definition sum_code (x y : A + B) : Prop
    := match x, y with
         | inl x', inl y' => x' = y'
         | inr x', inr y' => x' = y'
         | _, _ => False
       end.

  Definition sum_code_idpath {x} : sum_code x x
    := match x return sum_code x x with
         | inl _ => eq_refl
         | inr _ => eq_refl
       end.

  Definition sum_encode {x y} (p : x = y) : sum_code x y
    := eq_rect _ _ sum_code_idpath _ p.

  Definition sum_decode {x y} : sum_code x y -> x = y
    := match x, y return sum_code x y -> x = y with
         | inl x', inl y' => @f_equal _ _ (@inl _ _) _ _
         | inr x', inr y' => @f_equal _ _ (@inr _ _) _ _
         | _, _ => fun H => match H : False with end
       end.

  Definition sum_deenecode {x y} (p : x = y)
  : sum_decode (sum_encode p) = p.
  Proof.
    destruct p, x; reflexivity.
  Defined.

  Definition sum_endecode {x y} (p : sum_code x y)
  : sum_encode (sum_decode p) = p.
  Proof.
    destruct x, y, p; reflexivity.
  Defined.

  Definition inl_injective {x y : A} : inl x = inl y -> x = y
    := sum_encode.

  Definition inr_injective {x y : B} : inr x = inr y -> x = y
    := sum_encode.
End sum.

Definition prod_dec {A B}
           (HA : forall a b : A, {a = b} + {a <> b})
           (HB : forall a b : B, {a = b} + {a <> b})
: forall a b : A * B, {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.

Definition option_dec {A}
           (H : forall a b : A, {a = b} + {a <> b})
: forall a b : option A, {a = b} + {a <> b}.
Proof.
  decide equality.
Defined.
