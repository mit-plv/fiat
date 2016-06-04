Require Import Coq.Strings.String Coq.Sets.Ensembles.
Require Import Fiat.Common.
Require Import Fiat.Computation.Core.

(** [Comp] obeys the monad laws, using [computes_to] as the
    notion of equivalence. .*)

Definition equiv {A} (c1 c2 : Comp A) := forall v, c1 ↝ v <-> c2 ↝ v.

Infix "~" := equiv (at level 70) : comp_scope.

Section monad.

  Local Open Scope comp_scope.

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

  Lemma bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x
    : Bind (Bind x f) g ~ Bind x (fun u => Bind (f u) g).
  Proof.
    t.
  Qed.

  Lemma bind_unit X Y (f : X -> Comp Y) x
    : Bind (Return x) f ~ f x.
  Proof.
    t.
  Qed.

  Lemma unit_bind X (x : Comp X)
    : (Bind x (@Return X)) ~ x.
  Proof.
    t.
  Qed.

  Lemma computes_under_bind X Y (f g : X -> Comp Y) x
    : (forall x, f x ~ g x) ->
      Bind x f ~ Bind x g.
  Proof.
    t; unfold equiv in *; split_iff; eauto.
  Qed.
End monad.

(** [Comp] also obeys the monad laws using both [refineEquiv]
    as our notions of equivalence. *)

Section monad_refine.
  Lemma refineEquiv_bind_bind X Y Z (f : X -> Comp Y) (g : Y -> Comp Z) x
  : refineEquiv (Bind (Bind x f) g)
                (Bind x (fun u => Bind (f u) g)).
  Proof.
    split; intro; apply bind_bind.
  Qed.

  Definition refine_bind_bind X Y Z f g x
    := proj1 (@refineEquiv_bind_bind X Y Z f g x).
  Definition refine_bind_bind' X Y Z f g x
    := proj2 (@refineEquiv_bind_bind X Y Z f g x).

  Lemma refineEquiv_bind_unit X Y (f : X -> Comp Y) x
    : refineEquiv (Bind (Return x) f)
                  (f x).
  Proof.
    split; intro; simpl; apply bind_unit.
  Qed.

  Definition refine_bind_unit X Y f x
    := proj1 (@refineEquiv_bind_unit X Y f x).
  Definition refine_bind_unit' X Y f x
    := proj2 (@refineEquiv_bind_unit X Y f x).

  Lemma refineEquiv_unit_bind X (x : Comp X)
    : refineEquiv (Bind x (@Return X))
                  x.
  Proof.
    split; intro; apply unit_bind.
  Qed.

  Definition refine_unit_bind X x
    := proj1 (@refineEquiv_unit_bind X x).
  Definition refine_unit_bind' X x
    := proj2 (@refineEquiv_unit_bind X x).

  Lemma refineEquiv_bind2_bind A B C D Z (f : A -> B -> Comp (C * D))
        (g : C ->D -> Comp Z) x
    : refineEquiv (Bind2 (Bind2 x f) g)
                  (Bind2 x (fun a b => Bind2 (f a b) g)).
  Proof.
    split; intro; apply bind_bind.
  Qed.

  Lemma refineEquiv_bind2_unit A B C (f : A -> B -> Comp C) x
    : refineEquiv (Bind2 (Return x) f)
                  (f (fst x) (snd x)).
  Proof.
    unfold Bind2; split; intros; destruct x; simpl.
    rewrite refine_bind_unit; reflexivity.
    rewrite <- refine_bind_unit'; reflexivity.
  Qed.

  Lemma refineEquiv_unit_bind2 A B (x : Comp (A * B))
    : refineEquiv (Bind2 x (fun x y => Return (x, y))) x.
  Proof.
    unfold Bind2; split; intros; simpl.
    intros v Comp_v; computes_to_econstructor; eauto; destruct v; eauto.
    intros v Comp_v; computes_to_inv; subst; destruct v0; eauto.
  Qed.


End monad_refine.

Create HintDb refine_monad discriminated.

Hint Rewrite @refineEquiv_bind_bind @refineEquiv_bind_unit @refineEquiv_unit_bind : refine_monad.
(** We guard the [setoid_rewrite] with a [match] to work around
    "Anomaly: Uncaught exception
    Invalid_argument("decomp_pointwise"). Please report." *)
Tactic Notation "autosetoid_rewrite" "with" "refine_monad" :=
  repeat first [ match goal with |- appcontext[Bind (Bind _ _)] => idtac end;
                 setoid_rewrite refineEquiv_bind_bind
               | match goal with |- appcontext[Bind (Return _)] => idtac end;
                 setoid_rewrite refineEquiv_bind_unit
               | setoid_rewrite refineEquiv_unit_bind ].

Tactic Notation "simplify" "with" "setoid-y" "monad" "laws" :=
  autosetoid_rewrite with refine_monad.

(** Ideally we would throw [refineEquiv_under_bind] in here as well, but it gets stuck *)

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
