Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.LaxTerminalFormat.

Section SequenceFormat.

  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {monoid : Monoid T}. (* Target type is a monoid. *)

  Definition sequence_Format
             {S : Type}
             (format1 format2 : FormatM S T)
    := (fun s env =>
          `(t1, env') <- format1 s env ;
          `(t2, env'') <- format2 s env';
           ret (mappend t1 t2, env''))%comp.

  Definition sequence_Decode
             {S S' : Type}
             (decode1 : DecodeM (S' * T) T)
             (decode2 : S' -> DecodeM S T)
    : DecodeM S T
    := (fun t env =>
          match decode1 t env with
          | Some (s', t', env') => decode2 s' t' env'
          | None => None
          end).

  Definition sequence_Encode
             {S : Type}
             (encode1 encode2 : EncodeM S T)
    := (fun s env =>
          `(t1, env') <- encode1 s env ;
          `(t2, env'') <- encode2 s env';
          Some (mappend t1 t2, env'')).

  Notation "x ++ y" := (sequence_Format x y) : format_scope .

  Lemma CorrectEncoder_sequence
        {S : Type}
        (format1 format2 : FormatM S T)
        (encode1 encode2 : EncodeM S T)
        (encode1_correct : CorrectEncoder format1 encode1)
        (encode1_consistent : (* If the first format produces *some*
                                 environment that makes the second format
                                 (and thus the composite format) non-empty,
                                 the encoder must also produce an environment
                                 that makes the second format non-empty. *)
           forall s env tenv' tenv'',
             format1 s env ∋ tenv'
             -> format2 s (snd tenv') ∋ tenv''
             -> exists tenv3 tenv4,
                 encode1 s env = Some tenv3
                 /\ format2 s (snd tenv3) ∋ tenv4)
        (encode2_correct : CorrectEncoder format2 encode2)
    : CorrectEncoder (format1 ++ format2)
                     (sequence_Encode encode1 encode2).
  Proof.
    unfold CorrectEncoder, sequence_Encode, sequence_Format,
    DecodeBindOpt, BindOpt in *; intuition; intros.
    - destruct (encode1 a env) as [ [t1 xxenv] | ] eqn: ? ;
        simpl in *; try discriminate.
      destruct (encode2 a xxenv) as [ [t2 xxxenv] | ] eqn: ? ;
        simpl in *; try discriminate; injections.
      repeat computes_to_econstructor; eauto.
    -  unfold Bind2 in *; computes_to_inv; destruct v;
         destruct v0; simpl in *.
       destruct (encode1 a env) as [ [t1 xxenv] | ] eqn: ? ;
        simpl in *; try discriminate; eauto.
       eapply H2; try eassumption.
       destruct (encode2 a xxenv) as [ [t2' xxxenv] | ] eqn: ? ;
        simpl in *; try discriminate; injections.
       specialize (encode1_consistent _ _ _ _ H4 H4');
         destruct_ex; split_and.
       rewrite H6 in Heqo; injections; simpl in *.
       destruct x0; elimtype False; eauto.
  Qed.

  Lemma CorrectDecoder_sequence
        {S S' : Type}
        (f : S -> S')
        (format1 : FormatM S' T)
        (format2 : FormatM S T)
        (decode1 : DecodeM (S' * T) T)
        (decode2 : S' -> DecodeM S T)
        (decode1_correct : CorrectDecoder_simpl ((Projection_Format (fun st => (fst st)) format1) ++ ?* ) decode1)
        (decode2_correct : forall (s' : S'), CorrectDecoder_simpl format2 (decode2 s'))
    : CorrectDecoder_simpl (Projection_Format f format1 ++ format2)
                           (sequence_Decode decode1 decode2).
  Proof.
    unfold CorrectDecoder_simpl, Projection_Format,
    sequence_Decode, sequence_Format, FMap_Format; split; intros.
    - unfold Bind2 in H0; computes_to_inv; subst.
      repeat apply_in_hyp @unfold_computes.
      destruct v; destruct v0; simpl in *.
      destruct_ex; intuition; injections.
      destruct decode1_correct as [? _].
      destruct (decode2_correct (f data)) as [? _].
      destruct (H0 env env' c (f data, t0) (mappend t t0)) as (xenv', (decode1_eq, Equiv_xenv));
        eauto.
      { unfold Projection_Format, FMap_Format, LaxTerminal_Format; repeat computes_to_econstructor; eauto.
        apply unfold_computes; eexists; intuition eauto.
        computes_to_econstructor. }
      rewrite decode1_eq; eauto.
    - destruct (decode1 bin env') as [ [ [s' t'] xenv'']  | ] eqn: ?; try discriminate.
      destruct decode1_correct as [decode1_correct' decode1_correct].
      specialize (decode2_correct s'); destruct decode2_correct as [_ decode2_correct].
      generalize Heqo; intro Heqo'.
      eapply decode1_correct in Heqo; eauto.
      destruct_ex; split_and.
      eapply decode2_correct in H0; eauto.
      destruct_ex; split_and.
      eexists; intuition eauto.
      unfold Projection_Format, FMap_Format, LaxTerminal_Format, sequence_Format,
        Bind2 in *; computes_to_inv.
      repeat apply_in_hyp @unfold_computes.
      destruct_ex; split_and; simpl in *.
      injections; simpl in *.
      computes_to_econstructor.
      apply unfold_computes.
      eexists; split; try reflexivity.
      Focus 2.
      computes_to_econstructor; eauto.
      apply unfold_computes; eauto.
      eauto.
  Admitted.

            End SequenceFormat.

            Notation "x ++ y" := (sequence_Format x y) : format_scope .
