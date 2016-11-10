Require Import Coq.Program.Program.

Set Implicit Arguments.

Notation idmap := (fun x => x).

Class MonadOps (M : Type -> Type)
  := { bind : forall {A B}, M A -> (A -> M B) -> M B;
       ret : forall {A}, A -> M A }.

Global Arguments bind {M _ A B} _ _.
Global Arguments ret {M _ A} _.

Notation "x <- y ; f" := (bind y (fun x => f)) (at level 65, right associativity).

Class MonadLaws M `{MonadOps M}
  := { bind_bind : forall {A B C} (f : A -> M B) (g : B -> M C) x,
                     bind (bind x f) g = bind x (fun u => bind (f u) g);
       bind_unit : forall {A B} (f : A -> M B) x, bind (ret x) f = f x;
       unit_bind : forall {A} (x : M A), bind x ret = x;
       bind_ext : forall {A B} {f g : A -> M B},
                    (forall x, f x = g x)
                    -> forall x, bind x f = bind x g }.

Arguments MonadLaws M {_}.

Class MonadTransformerOps (T : (Type -> Type) -> (Type -> Type))
  := { Tops :> forall M `{MonadOps M}, MonadOps (T M);
       lift : forall {M} `{MonadOps M} {A}, M A -> T M A }.

Class MonadTransformerLaws T `{MonadTransformerOps T}
  := { Tlaws :> forall {M} `{MonadLaws M}, MonadLaws (T M);
       lift_ret : forall {M} `{MonadLaws M} {A} (x : A), lift (ret x) = ret x;
       lift_bind : forall {M} `{MonadLaws M} {A B} (f : A -> M B) x,
                     lift (bind x f) = bind (lift x) (fun u => lift (f u)) }.
Arguments MonadTransformerLaws T {_}.

Create HintDb monad discriminated.
Create HintDb monad' discriminated.
Hint Rewrite @bind_bind @bind_unit @unit_bind @lift_ret @lift_bind : monad.
Hint Rewrite @bind_unit @unit_bind @lift_ret @lift_bind : monad'.
Hint Rewrite <- @bind_bind : monad'.

Instance idM : MonadOps idmap
  := { bind A B x f := f x;
       ret A x := x }.
Instance idML : MonadLaws idmap.
Proof.
  constructor; trivial.
Defined.

Instance idT : MonadTransformerOps idmap
  := { Tops M H := H;
       lift M H A x := x }.
Instance idTL : MonadTransformerLaws idmap.
Proof.
  constructor; trivial.
Defined.

Instance monad_of_transformer T `{MonadTransformerOps T}
: MonadOps (T idmap) | 1000
  := _.
Coercion monad_of_transformer : MonadTransformerOps >-> MonadOps.

Instance monad_laws_of_transformer T `{MonadTransformerLaws T}
: MonadLaws (T idmap)
  := _.
Coercion monad_laws_of_transformer : MonadTransformerLaws >-> MonadLaws.

Instance optionT : MonadTransformerOps (fun M => M ∘ option) | 2
  := { Tops M H := {| ret A x := ret (Some x);
                      bind A B x f := _ |};
       lift M H A x := bind x (fun a => ret (Some a)) }.
Proof.
  { exact (bind (M:=M) x (fun a => match a with
                                   | None => ret None
                                   | Some a' => f a'
                                   end)). }
Defined.

Local Ltac t_option :=
  repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => assumption
           | _ => solve [ trivial ]
           | [ H : option _ |- _ ] => destruct H
           | [ |- appcontext[match ?a with None => _ end] ] => case_eq a
           | [ |- @bind ?M ?H ?A ?B ?x _ = bind ?x _ ] => let lem := constr:(@bind_ext M H _ A B) in apply lem
           | [ |- @bind ?M ?H ?A ?B ?x _ = ?x ] => etransitivity; [ | solve [ apply (@unit_bind M H _) ] ]
           | _ => progress autorewrite with monad; try assumption; []
         end.

Instance optionTLaws : MonadTransformerLaws (fun M => M ∘ option) | 2
  := { Tlaws M H L := _ }.
Proof.
  { constructor; simpl; t_option. }
  { simpl; t_option. }
  { simpl; t_option. }
Defined.

Instance optionM : MonadOps option | 2 := optionT.
Instance optionLaws : MonadLaws option | 2 := optionTLaws.

Definition liftA {T} `{MonadTransformerOps T} {M} `{MonadOps M} {A B}
           (f : M A -> M B)
: T M A -> T M B
  := fun x => y <- x; lift (f (ret y)).
