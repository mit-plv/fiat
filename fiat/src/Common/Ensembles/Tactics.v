Require Import Coq.Sets.Ensembles.
Require Import Fiat.Common.

Create HintDb ensembles discriminated.

Hint Constructors Singleton Union Intersection : ensembles.

Ltac finish_union_with t :=
  solve [ t
        | left; finish_union_with t
        | right; finish_union_with t ].

Ltac Ensembles_t_step :=
  idtac;
  match goal with
    | _ => intro
    | _ => progress destruct_head_hnf and
    | _ => progress destruct_head_hnf or
    | _ => progress destruct_head_hnf False
    | _ => progress destruct_head_hnf Union
    | _ => progress destruct_head_hnf Intersection
    | _ => progress destruct_head_hnf Singleton
    | _ => progress destruct_head_hnf Ensembles.Empty_set
    | _ => progress subst
    | _ => progress unfold Same_set, Included, Ensembles.In, Ensembles.Setminus in *
    | [ |- Singleton _ _ _ ] => constructor
    | [ |- Intersection _ _ _ _ ] => constructor
    | [ |- _ /\ _ ] => split
    | [ H : ~~(@eq bool _ _) |- _ ] => apply dn_eqb in H
    | [ H : ~(@eq bool _ _) |- _ ] => apply neq_to_eq_negb in H
    | [ H : context[negb (negb _)] |- _ ] => rewrite Bool.negb_involutive in H
    | [ H : ?x = negb ?x |- _ ] => symmetry in H; apply Bool.no_fixpoint_negb in H
    | [ H : negb ?x = ?x |- _ ] => apply Bool.no_fixpoint_negb in H
    (** slower tactics *)
    | _ => progress simplify_hyps
    | _ => solve [ eauto with ensembles ]
    | _ => finish_union_with ltac:(eauto with ensembles)
    | _ => finish_union_with ltac:(hnf in *; eauto with ensembles)
  end.

Ltac Ensembles_t :=
  repeat Ensembles_t_step.
