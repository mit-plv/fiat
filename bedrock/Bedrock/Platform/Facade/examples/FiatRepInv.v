Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Facade.examples.FiatADTs.
Import Adt.
Require Import Bedrock.Platform.Cito.RepInv.

Require Import Bedrock.Platform.Facade.examples.FiniteSetF Bedrock.Platform.Facade.examples.ListSetF Bedrock.Platform.Facade.examples.SeqF Bedrock.Platform.Facade.examples.ListSeqF.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | List ls => lseq ls p
    | Junk _ => [| False |]
    | FEnsemble s => lset s p
  end%Sep.

Module Ri <: RepInv FiatADTs.Adt.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
    destruct a; simpl.
    eapply Himp_trans; [ apply lseq_fwd | sepLemma ]; apply any_easy.
    sepLemma.
    eapply Himp_trans; [ apply lset_fwd | sepLemma ]; apply any_easy.
  Qed.

End Ri.
