Require Import Coq.Setoids.Setoid ADTSynthesis.ComputationalEnsembles.Morphisms.
Require Import ADTSynthesis.FiatToFacade.Prog ADTSynthesis.FiatToFacade.SupersetUtilities ADTSynthesis.FiatToFacade.SupersetMorphisms.
Require Import Bedrock.Platform.Cito.StringMap.
Require Import ADTSynthesis.Common ADTSynthesis.Computation.Core.

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
