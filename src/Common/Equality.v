Require Import Coq.Lists.List.

Set Implicit Arguments.

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
