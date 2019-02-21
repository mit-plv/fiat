Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations.

Set Implicit Arguments.

Definition compose E B
           (monoid : Monoid B)
           (format1 : E -> Comp (B * E))
           (format2 : E -> Comp (B * E)) :=
  (fun e0 =>
     `(p, e1) <- format1 e0;
     `(q, e2) <- format2 e1;
       ret (mappend p q, e2))%comp.

Notation "x 'ThenC' y" := (compose _ x y) : format_scope .
Notation "x 'DoneC'"   := (x ThenC fun e => ret (mempty, e)) : format_scope.

Lemma refineEquiv_compose_compose E B
      (monoid : Monoid B)
      (format1 format2 format3 : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (compose _ (compose _ format1 format2) format3 ctx)
                (compose _ format1 (compose _ format2 format3) ctx).
Proof.
  unfold compose; intros.
  rewrite refineEquiv_bind2_bind.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro; rewrite refineEquiv_bind2_bind.
  symmetry; rewrite refineEquiv_bind2_bind.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro; rewrite refineEquiv_bind2_bind.
  rewrite refineEquiv_bind2_unit.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro; rewrite refineEquiv_bind2_unit; simpl.
  rewrite mappend_assoc; reflexivity.
Qed.

Lemma refineEquiv_compose_Done E B
      (monoid : Monoid B)
      (format2 : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (compose _ (fun ctx => ret (mempty, ctx)) format2 ctx)
                (format2 ctx).
Proof.
  unfold compose; simpl; intros.
  rewrite refineEquiv_bind2_unit; simpl.
  split; unfold Bind2; intros v Comp_v.
  - computes_to_econstructor; eauto; destruct v; simpl;
      rewrite mempty_left; eauto.
  - computes_to_inv; subst; destruct v0;
      rewrite mempty_left; eauto.
Qed.

Lemma refineEquiv_under_compose E B
      (monoid : Monoid B)
      (format1 format2 format2' : E -> Comp (B * E))
  : (forall ctx', refineEquiv (format2 ctx') (format2' ctx'))
    -> forall ctx,
      refineEquiv (compose _ format1 format2 ctx)
                  (compose _ format1 format2' ctx).
Proof.
  unfold compose; intros.
  eapply refineEquiv_bind; [ reflexivity | ].
  intro ab; destruct ab; simpl.
  eapply refineEquiv_bind; [ apply H | reflexivity ].
Qed.

Lemma decides_and :
  forall b b' P Q,
    decides b P
    -> decides b' Q
    -> decides (andb b b') (P /\ Q).
Proof.
  destruct b; destruct b'; simpl in *; intuition.
Qed.

Lemma decides_assumption :
  forall (P : Prop),
    P -> decides true P.
Proof. simpl in *; intuition. Qed.

Lemma decides_eq_refl {A} :
  forall (a : A), decides true (a = a).
Proof. simpl in *; intuition. Qed.

Lemma decides_dec_eq {A} :
  forall (A_eqb : A -> A -> bool)
         (A_eqb_sound : forall a a', a = a' <-> A_eqb a a' = true)
         (a a' : A), decides (A_eqb a a') (a = a').
Proof.
  simpl in *; intros; pose proof (A_eqb_sound a a');
    destruct (A_eqb a a'); simpl; intuition.
Qed.

Lemma decides_dec_lt
  : forall n n', decides (if (Compare_dec.lt_dec n n') then true else false) (lt n n').
Proof.
  intros; find_if_inside; simpl; eauto.
Qed.

Lemma refine_If_Then_Else_ThenC
  : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (ctx : E) b,
    refine (((If b Then format1 Else format2) ThenC format3) ctx)
           (If b Then ((format1 ThenC format3) ctx) Else ((format2 ThenC format3) ctx)).
Proof.
  intros; destruct b; reflexivity.
Qed.

Lemma refineEquiv_If_Then_Else_ThenC
  : forall (E B : Type) (monoid : Monoid B) (format1 format2 format3 : E -> Comp (B * E)) (ctx : E) b,
    refineEquiv (((If b Then format1 Else format2) ThenC format3) ctx)
                (If b Then ((format1 ThenC format3) ctx) Else ((format2 ThenC format3) ctx)).
Proof.
  intros; destruct b; reflexivity.
Qed.
