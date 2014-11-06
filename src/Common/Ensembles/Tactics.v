Require Import Coq.Sets.Ensembles.
Require Import ADTSynthesis.Common.

Create HintDb ensembles discriminated.

Hint Constructors Singleton Union Intersection : ensembles.

Ltac finish_union_with t :=
  solve [ t
        | left; finish_union_with t
        | right; finish_union_with t ].

Ltac Ensemble_mor_t :=
  repeat match goal with
           | _ => intro
           | _ => progress destruct_head_hnf and
           | _ => progress destruct_head_hnf or
           | _ => progress destruct_head_hnf False
           | _ => progress destruct_head_hnf Union
           | _ => progress destruct_head_hnf Intersection
           | _ => progress destruct_head_hnf Singleton
           | _ => progress destruct_head_hnf Ensembles.Empty_set
           | _ => progress subst
           | _ => progress unfold Same_set, Included, Ensembles.In in *
           | [ |- Singleton _ _ _ ] => constructor
           | [ |- Intersection _ _ _ _ ] => constructor
           | [ |- _ /\ _ ] => split
           | _ => solve [ eauto with ensembles ]
           | _ => finish_union_with ltac:(eauto with ensembles)
           | _ => finish_union_with ltac:(hnf in *; eauto with ensembles)
         end.
