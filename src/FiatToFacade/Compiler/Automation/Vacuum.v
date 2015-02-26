Require Import FiatToFacade.Compiler.
Require Import Cito.GLabelMapFacts.
Require Import Computation.ApplyMonad.
        
Ltac find_label_in_env :=
  try match goal with
        | |- GLabelMap.find _ basic_imports_wrapped = _ =>
          try rewrite basic_imports_yield_basic_env; unfold basic_env
      end;
  unfold AddPair, MakePair;
  simpl;
  try match goal with
        | |- GLabelMap.find ?k (GLabelMap.add ?k' (Axiomatic ?spec) _) = Some (Axiomatic ?spec) =>
          apply GLabelMapFacts.F.add_eq_o; try reflexivity
        | |- GLabelMap.find ?k (GLabelMap.add ?k' (Axiomatic ?spec) _) = Some (Axiomatic ?spec') =>
          rewrite GLabelMapFacts.F.add_neq_o; [ find_label_in_env | ]; congruence
      end.

Ltac vacuum :=
  trickle_deletion;
  match goal with
    | [ |- refine _ _ ] => try (simplify with monad laws)
    | [ |- ?a <> ?b ] => first [ is_evar a | is_evar b | discriminate ]
    | [ |- ~ StringMap.In ?k ∅ ] => solve [apply not_in_empty]
    | [ |- ~ StringMap.In ?k ?s ] => first [ is_evar s | solve [map_iff_solve ltac:(intuition discriminate)] ]
    | [ |- context[SCALoopBodyProgCondition] ] => progress (unfold SCALoopBodyProgCondition; intros; simpl)
    | [ |- context[ADTLoopBodyProgCondition] ] => progress (unfold ADTLoopBodyProgCondition; intros; simpl)
    | [ |- context[PairLoopBodyProgCondition] ] => progress (unfold PairLoopBodyProgCondition; intros; simpl)
    | [ |- context[ADTPairLoopBodyProgCondition] ] => progress (unfold ADTPairLoopBodyProgCondition; intros; simpl)
    | [ |- ?m[?k >> ?v] ] => solve [map_iff_solve_evar intuition]
    | [ |- SomeSCAs _ ∅ ] => solve [apply SomeSCAs_empty]
    | [ |- SomeSCAs _ _ ] => eassumption
    | [ |- AllADTs _ _ ] => eassumption
    | [ |- AllADTs _ _ ] => solve [unfold AllADTs, Superset; intros; map_iff_solve intuition]
    | [ |- Word2Spec ?env _ = Some (Axiomatic _) ] => reflexivity
    | [ |- Label2Word ?env _ = Some _ ] => reflexivity
    | [ |- StringMap.Equal ?a ?b ] => first [ is_evar a | is_evar b | solve_map_eq ]
    | [ |- Core.AbsR ?impl ?e (projT1 ?fs) ] => exact (proj2_sig (projT2 fs))
    | _ => solve [ find_label_in_env ]
  end.
