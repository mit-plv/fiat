Require Import
        Fiat.Common.ilist
        Fiat.Common.IterateBoundedIndex
        Fiat.Narcissus.Common.Specs.

Require Import
        Coq.Sets.Ensembles.

Section UnionFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)

  Definition Union_Format {m}
             (formats : Vector.t (FormatM S T) m)
    : FormatM S T :=
    fun s env tenv' =>
      exists idx, computes_to (Vector.nth formats idx s env) tenv'.

  Definition Union_Decode
             {m}
             (decoders : Vector.t (DecodeM S T) m)
             (idx : Fin.t m)
    : DecodeM S T := Vector.nth decoders idx.

  Definition Union_Encode
             {m}
             (encoders : Vector.t (EncodeM S T) m)
             (idx : Fin.t m)
    : EncodeM S T := Vector.nth encoders idx.

  Lemma CorrectDecoder_Union {m}
        (formats : Vector.t (FormatM S T) m)
        (decoders : Vector.t (DecodeM S T) m)
        (correct_decoders :
           Iterate_Ensemble_BoundedIndex'
             (fun idx =>
                CorrectDecoder_simpl (Vector.nth formats idx) (Vector.nth decoders idx)))
        (idx : Fin.t m)
        (unique_format :
           forall s env t env',
             (computes_to (Union_Format formats s env) (t, env') ->
              computes_to (Vector.nth formats idx s env) (t, env')))
    : CorrectDecoder_simpl (Union_Format formats) (Union_Decode decoders idx).
Proof.
  unfold CorrectDecoder_simpl, Union_Decode, Union_Format in *; split; intros.
  { eapply unique_format in H0.
    eapply Iterate_Ensemble_equiv' in correct_decoders.
    eapply correct_decoders in H0; eauto.
  }
  { eapply Iterate_Ensemble_equiv' in correct_decoders.
    eapply correct_decoders in H0; eauto.
    destruct_ex; intuition; eexists; split; eauto.
    apply unfold_computes.
    eexists; intuition eauto.
  }
Qed.

End UnionFormat.
