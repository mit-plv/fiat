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
        (f : S -> S' -> Prop)
        (format1' : FormatM (S' * T) T)
        (format1 format2 : FormatM S T)
        (decode1 : DecodeM (S' * T) T)
        (decode2 : S' -> DecodeM S T)
        (format1_overlap : forall s env tenv',
            format1 s env ∋ tenv' -> exists s',
              forall t, format1' (s', t) env ∋ (mappend (fst tenv') t, snd tenv') /\ f s s')
        (format1'_overlap : forall s' t env tenv',
            format1' (s', t) env ∋ tenv'
            -> forall s,
              f s s'
              -> exists t', format1 s env ∋ (t', snd tenv') /\ fst tenv' = mappend t' t)
        (decode1_correct : CorrectDecoder_simpl format1' decode1)
        (decode2_correct : forall (s' : S'), CorrectDecoder_simpl (Restrict_Format (fun s => f s s') format2) (decode2 s'))
    : CorrectDecoder_simpl (format1 ++ format2)
                           (sequence_Decode decode1 decode2).
  Proof.
    unfold CorrectDecoder_simpl, Projection_Format,
    sequence_Decode, sequence_Format, FMap_Format; split; intros.
    - unfold Bind2 in H0; computes_to_inv; subst.
      eapply format1_overlap in H0; destruct_ex; split_and.
      rewrite @unfold_computes in H0'.
      destruct v; destruct v0; simpl in *; injections.
      destruct decode1_correct as [? _].
      destruct (decode2_correct x) as [? _].
      destruct (H0 env env' c (x, t0) (mappend t t0)) as (xenv', (decode1_eq, Equiv_xenv));
        eauto.
      rewrite decode1_eq; eauto.
      eapply H3; eauto.
      unfold Restrict_Format, FMap_Format; apply unfold_computes.
      setoid_rewrite unfold_computes; eexists; intuition eauto.
    - destruct (decode1 bin env') as [ [ [s' t'] xenv'']  | ] eqn: ?; try discriminate.
      destruct decode1_correct as [decode1_correct' decode1_correct].
      specialize (decode2_correct s'); destruct decode2_correct as [_ decode2_correct].
      generalize Heqo; intro Heqo'.
      eapply decode1_correct in Heqo; eauto.
      destruct_ex; split_and.
      eapply decode2_correct in H0; eauto.
      destruct_ex; split_and.
      eexists; intuition eauto.
      unfold Restrict_Format, FMap_Format, LaxTerminal_Format, sequence_Format,
        Bind2 in *; computes_to_inv.
      rewrite @unfold_computes in H1.
      destruct_ex; split_and; simpl in *; subst.
      eapply format1'_overlap in H2; destruct_ex; split_and; subst; eauto.
  Qed.

  Corollary CorrectDecoder_sequence_Projection
        {S S' : Type}
        (f : S -> S')
        (format1 : FormatM S' T)
        (format2 : FormatM S T)
        (decode1 : DecodeM (S' * T) T)
        (decode2 : S' -> DecodeM S T)
        (decode1_correct : CorrectDecoder_simpl (Projection_Format fst format1 ++ ?* ) decode1)
        (decode2_correct : forall (s' : S'), CorrectDecoder_simpl (Restrict_Format (fun s => f s = s') format2) (decode2 s'))
    : CorrectDecoder_simpl (Projection_Format f format1 ++ format2)
                           (sequence_Decode decode1 decode2).
  Proof.
    unfold Projection_Format.
    eapply (CorrectDecoder_sequence (fun s s' => f s = s')); eauto; intros;
      unfold Projection_Format, FMap_Format, sequence_Format, Bind2, LaxTerminal_Format in *.
    - rewrite @unfold_computes in H.
      destruct_ex; split_and; subst.
      eexists; intros; intuition.
      destruct tenv'; simpl; computes_to_econstructor.
      rewrite unfold_computes; eauto.
      simpl; computes_to_econstructor; eauto.
    - computes_to_inv; subst.
      apply_in_hyp @unfold_computes; destruct_ex; split_and; subst.
      eexists; simpl; intuition eauto.
      destruct v; apply unfold_computes; eauto.
  Qed.

End SequenceFormat.

Notation "x ++ y" := (sequence_Format x y) : format_scope .
