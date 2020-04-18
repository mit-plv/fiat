Require Import Coq.Sets.Ensembles.
Require Import Fiat.Computation Fiat.Common.Ensembles
        Fiat.ComputationalEnsembles.Core Fiat.ComputationalEnsembles.Laws.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Ltac fold_right_refine_mor_t :=
  repeat match goal with
           | _ => intro
           | [ H : EnsembleListEquivalence _ _ |- computes_to (Bind _ _) _ ] => computes_to_econstructor; [|]; eauto; []; clear H
           | _ => progress unfold pointwise_relation, fold_right, to_list in *
           | _ => progress destruct_head_hnf and
           | _ => progress hnf in *
           | _ => progress computes_to_inv
         end;
  match goal with
    | [ |- computes_to _ ?v ] => generalize dependent v
  end;
  match goal with
    | [ H : list _ |- _ ] => induction H; simpl in *; trivial; intros
  end;
  repeat first [ computes_to_inv
               | progress unfold refine in *
               | solve [ computes_to_econstructor; eauto ] ].

Local Ltac fold_right_refineEquiv_mor_t :=
  unfold pointwise_relation,refineEquiv in *; intros;
  split_and; split;
  repeat match goal with
           | [ H : forall a b, refine (?x a b) (?y a b) |- _ ]
             => change ((pointwise_relation _ (pointwise_relation _ refine)) x y) in H
         end;
  match goal with
    | [ H : _ |- _ ] => rewrite H; reflexivity
  end.

Add Parametric Morphism A B : (@fold_right A B)
    with signature (pointwise_relation _ (pointwise_relation _ refine)) ==> eq ==> eq ==> refine
      as fold_right_refine_mor1.
Proof. fold_right_refine_mor_t.
       computes_to_econstructor; eauto; eapply H; eauto.
Qed.

Add Parametric Morphism A B : (@fold_right A B)
    with signature (pointwise_relation _ (pointwise_relation _ refineEquiv)) ==> eq ==> eq ==> refineEquiv
      as fold_right_refineEquiv_mor1.
Proof. fold_right_refineEquiv_mor_t. Qed.

Add Parametric Morphism A B f : (@fold_right A B f)
    with signature refine ==> eq ==> refine
      as fold_right_refine_mor2.
Proof. fold_right_refine_mor_t.
       computes_to_econstructor; eauto; eapply H; eauto.
Qed.

Add Parametric Morphism A B f : (@fold_right A B f)
    with signature refineEquiv ==> eq ==> refineEquiv
      as fold_right_refineEquiv_mor2.
Proof. fold_right_refineEquiv_mor_t. Qed.

Add Parametric Morphism A B f b : (@fold_right A B f b)
    with signature Same_set _ ==> refine
      as fold_right_refine_mor.
Proof.
  unfold Same_set, Included;
  repeat match goal with
           | _ => intro
           | [ |- computes_to (Pick _) _ ] => constructor
           | [ |- and _ _ ] => split
           | [ H : EnsembleListEquivalence _ _ |- computes_to (Bind _ _) _ ] => econstructor; [|]; eauto; []
           | _ => progress split_iff
           | _ => progress unfold pointwise_relation, fold_right, to_list in *
           | _ => progress destruct_head_hnf and
           | _ => progress hnf in *
           | _ => progress computes_to_inv
           | _ => progress unfold Ensembles.In in *
           | _ => solve [ intuition eauto ]
         end.
  repeat computes_to_econstructor; eauto.
  econstructor; intuition eauto.
  eapply H1; eauto.
Qed.

Add Parametric Morphism A B f b : (@fold_right A B f b)
    with signature Same_set _ ==> refineEquiv
      as fold_right_refineEquiv_mor.
Proof.
  intros; split;
  let H := match goal with H : Same_set _ _ _ |- _ => constr:(H) end in
  setoid_rewrite H; reflexivity.
Qed.
