Require Import Setoid Morphisms.
Require Import FiatToFacade.Prog FiatToFacade.SupersetUtilities FiatToFacade.SupersetMorphisms.
Require Import StringMap.
Require Import Common Computation.Core.

Add Parametric Morphism av env :
  (@Prog av env)
    with signature (iff ==> StringMap.Equal ==> StringMap.Equal ==> StringMap.Equal ==> StringMap.Equal ==> refine)
      as Prog_morphism.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  constructor; intros; destruct_pairs.

  rewrite_Eq_in_all; split; intros;
  specialize_states; intuition.
Qed.
