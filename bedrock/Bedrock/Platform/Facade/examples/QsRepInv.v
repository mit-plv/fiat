Set Implicit Arguments.

Require Import Bedrock.Platform.AutoSep.
Require Import Bedrock.Platform.Facade.examples.QsADTs.
Import Adt.
Require Import Bedrock.Platform.Cito.RepInv.

Require Import Bedrock.Platform.Facade.examples.ListSeqF Bedrock.Platform.Facade.examples.ArrayTupleF Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.Tuples0F Bedrock.Platform.Facade.examples.Tuples1F Bedrock.Platform.Facade.examples.Tuples2F Bedrock.Platform.Facade.examples.ByteString Bedrock.Platform.Facade.examples.WSTuple.

Definition rep_inv p adtvalue : HProp :=
  match adtvalue with
    | WTuple t => tuple t p
    | WordList ts => ListSeqF.Adt.lseq ts p
    | WTupleList ts => lseq ts p
    | WBagOfTuples0 len ts => tuples0 len ts p
    | WBagOfTuples1 len key ts => tuples1 len key ts p
    | WBagOfTuples2 len key1 key2 ts => tuples2 len key1 key2 ts p
    | WSTuple ws => wstuple ws p
    | WSTupleList _ => [| False |]
    | ByteString capacity bs => bytes capacity bs p
    | WSTrie _ _ _ => [| False |]
  end%Sep.

Module Ri <: RepInv QsADTs.Adt.

  Definition RepInv := W -> ADTValue -> HProp.

  Definition rep_inv := rep_inv.

  Lemma rep_inv_ptr : forall p a, rep_inv p a ===> p =?> 1 * any.
  Proof.
    destruct a; simpl.

    eapply Himp_trans; [ apply tuple_fwd | ].
    sepLemmaLhsOnly.
    fold (@length W) in *.
    Transparent Malloc.freeable.
    unfold Malloc.freeable in H0.
    destruct t; simpl in *; intuition (try omega).
    destruct t; simpl in *; intuition (try omega).
    unfold array; simpl.
    sepLemma; apply any_easy.

    eapply Himp_trans; [ apply ListSeqF.Adt.lseq_fwd | sepLemma ]; apply any_easy.

    eapply Himp_trans; [ apply lseq_fwd | sepLemma ]; apply any_easy.

    unfold tuples0; sepLemma; apply any_easy.

    eapply Himp_trans; [ apply tuples1_fwd | sepLemma ]; apply any_easy.

    eapply Himp_trans; [ apply tuples2_fwd | sepLemma ]; apply any_easy.

    eapply Himp_trans; [ apply wstuple_fwd | ].
    destruct t; simpl in *.
    sepLemma; omega.
    destruct w; sepLemma.
    eapply Himp_trans; [ apply wstuple'_word_fwd | sepLemma ]; apply any_easy.
    eapply Himp_trans; [ apply wstuple'_bytes_fwd | sepLemma ]; apply any_easy.

    sepLemma.

    unfold bytes; sepLemma; apply any_easy.

    sepLemma.

    Grab Existential Variables.
    exact 0.
  Qed.

End Ri.
