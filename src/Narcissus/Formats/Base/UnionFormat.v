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
      exists idx, Vector.nth formats idx s env ∋ tenv'.

  Definition Union_Decode
             {m}
             (decoders : Vector.t (DecodeM S T) m)
             (idx : Fin.t m)
    : DecodeM S T := Vector.nth decoders idx.

  Definition Union_Encode
             {m}
             (encoders : Vector.t (EncodeM S T) m)
             (idx : S -> Fin.t m)
    : EncodeM S T := fun s => Vector.nth encoders (idx s) s.

  Lemma CorrectEncoder_Union {m}
        (formats : Vector.t (FormatM S T) m)
        (encoders : Vector.t (EncodeM S T) m)
        (correct_encoders :
           Iterate_Ensemble_BoundedIndex'
             (fun idx =>
                CorrectEncoder (Vector.nth formats idx) (Vector.nth encoders idx)))
        (f_idx :
           forall (s : S),
             { idx : _ & forall env t env',
                   Union_Format formats s env ∋ (t, env') ->
                   Vector.nth formats idx s env ∋ (t, env')})
    : CorrectEncoder (Union_Format formats) (Union_Encode encoders (fun s => projT1 (f_idx s))).
  Proof.
    unfold CorrectEncoder, Union_Encode, Union_Format in *; split; intros.
    - apply Iterate_Ensemble_equiv' with (idx := projT1 (f_idx a)) in correct_encoders.
      eapply correct_encoders in H.
      apply unfold_computes; eauto.
    - intro; apply_in_hyp @unfold_computes; eauto.
      pose proof (projT2 (f_idx a) env _ _ H0); simpl in *.
      apply Iterate_Ensemble_equiv' with (idx := projT1 (f_idx a)) in correct_encoders.
      eapply correct_encoders in H.
      apply H; eauto.
  Qed.

End UnionFormat.
