Require Import String Ensembles.
Require Import Common.
Require Import Computation.Core.

(* [Comp] obeys the monad laws, using [computes_to] as the
   notion of equivalence. .*)

Section monad.
  Context `{ctx : LookupContext}.

  Local Ltac t :=
    split;
    intro;
    repeat match goal with
             | [ H : _ |- _ ]
               => inversion H; clear H; subst; [];
                  repeat match goal with
                           | [ H : _ |- _ ] => apply inj_pair2 in H; subst
                         end
           end;
      repeat first [ eassumption
                   | solve [ constructor ]
                   | eapply BindComputes; (eassumption || (try eassumption; [])) ].

  Lemma bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x v
  : Bind (Bind x f) g ↝ v
    <-> Bind x (fun u => Bind (f u) g) ↝ v.
  Proof.
    t.
  Qed.

  Lemma bind_unit X Y (f : X -> Comp Y) x v
  : Bind (Return x) f ↝ v
    <-> f x ↝ v.
  Proof.
    t.
  Qed.

  Lemma unit_bind X (x : Comp X) v
  : (Bind x (@Return X)) ↝ v
    <-> x ↝ v.
  Proof.
    t.
  Qed.

  Lemma computes_under_bind X Y (f g : X -> Comp Y) x
  : (forall x v, f x ↝ v <-> g x ↝ v) ->
    (forall v, Bind x f ↝ v <-> Bind x g ↝ v).
  Proof.
    t; split_iff; eauto.
  Qed.

End monad.


(* [Comp] also obeys the monad laws using both [refineEquiv] 
   as our notions of equivalence. *)

Section monad_refine.

  Lemma refineEquiv_bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x
  : refineEquiv (Bind (Bind x f) g)
                (Bind x (fun u => Bind (f u) g)).
  Proof.
    split; intro; apply bind_bind.
  Qed.

  Lemma refineEquiv_bind_unit X Y (f : X -> Comp Y) x
  : refineEquiv (Bind (Return x) f)
                (f x).
  Proof.
    split; intro; simpl; apply bind_unit.
  Qed.

  Lemma refineEquiv_unit_bind X (x : Comp X)
  : refineEquiv (Bind x (@Return X))
                x.
  Proof.
    split; intro; apply unit_bind.
  Qed.

End monad_refine.

Create HintDb refine_monad discriminated.

(*Hint Rewrite refine_bind_bind refine_bind_unit refine_unit_bind : refine_monad.
Hint Rewrite <- refine_bind_bind' refine_bind_unit' refine_unit_bind' : refine_monad.*)
Hint Rewrite @refineEquiv_bind_bind @refineEquiv_bind_unit @refineEquiv_unit_bind : refine_monad.
(* Ideally we would throw refineEquiv_under_bind in here as well, but it gets stuck *)

Ltac interleave_autorewrite_refine_monad_with tac :=
  repeat first [ reflexivity
               | progress tac
               | progress autorewrite with refine_monad
               (*| rewrite refine_bind_bind'; progress tac
               | rewrite refine_bind_unit'; progress tac
               | rewrite refine_unit_bind'; progress tac
               | rewrite <- refine_bind_bind; progress tac
               | rewrite <- refine_bind_unit; progress tac
               | rewrite <- refine_unit_bind; progress tac ]*)
               | rewrite <- !refineEquiv_bind_bind; progress tac
               | rewrite <- !refineEquiv_bind_unit; progress tac
               | rewrite <- !refineEquiv_unit_bind; progress tac
               (*| rewrite <- !refineEquiv_under_bind; progress tac *)].
