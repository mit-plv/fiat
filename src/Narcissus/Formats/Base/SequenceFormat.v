Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt
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
    := (fun s => compose _ (format1 s) (format2 s))%comp.

  Definition sequence_Decode
             {S S' T : Type}
             {cache : Cache}
             (decode1 : DecodeM (S' * T) T)
             (decode2 : S' -> DecodeM (S * T) T)
    : DecodeM (S * T) T :=
    fun t env =>
      `(s', t', env') <- decode1 t env;
        decode2 s' t' env'.

  Definition sequence_Decode'
             {S S' : Type}
             (decode1 : DecodeM (S' * T) T)
             (decode2 : S' -> DecodeM (S * T) T)
    : DecodeM (S' * S * T) T :=
      fun t env =>
      `(s', t', env') <- decode1 t env;
      `(s, t', env'') <- decode2 s' t' env';
      Some ((s', s), t', env'').

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
    unfold CorrectEncoder, sequence_Encode, sequence_Format, compose,
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
       destruct x0; exfalso; eauto.
  Qed.

  Lemma Sequence_decode_correct
        {S V1 V2 : Type}
        {P : CacheDecode -> Prop}
        {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
        (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
        (view1 : S -> V1 -> Prop)
        (view2 : V1 -> S -> V2 -> Prop)
        (Source_Predicate : S -> Prop)
        (View_Predicate2 : V1 -> V2 -> Prop)
        (View_Predicate1 : V1 -> Prop)
        (consistency_predicate : V1 -> S -> Prop)
        (format1 format2 : FormatM S T )
        (decode1 : DecodeM (V1 * T) T)
        (view_format1 : FormatM V1 T)
      (*consistency_predicate_refl :
         forall a, consistency_predicate (proj' a) (proj a))
      (proj_predicate_OK :
         forall s, predicate (proj s)
                   -> proj_predicate (proj' s) *)
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid Source_Predicate View_Predicate1 view1 format1 decode1 P view_format1)
      (*pred_pf : forall s, predicate s -> predicate' s *)
      (consistency_predicate_OK :
         forall s v1 t1 t2 env xenv xenv',
           computes_to (format1 s env) (t1, xenv)
           -> computes_to (view_format1 v1 env) (t2, xenv')
           -> view1 s v1
           -> consistency_predicate v1 s)

      (decode2 : V1 -> DecodeM (V2 * T) T)
      (view_format2 : V1 -> FormatM V2 T)
      (view_format3 : FormatM (V1 * V2) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectDecoder monoid (fun s => Source_Predicate s
                                          /\ consistency_predicate v1 s)
                         (View_Predicate2 v1) (view2 v1) format2 (decode2 v1) P (view_format2 v1))
      (view_format3_OK : forall v1 t1 env1 xenv1 v2 t2 xenv2,
          view_format1 v1 env1 (t1, xenv1)
          -> view_format2 v1 v2 xenv1 (t2, xenv2)
          -> View_Predicate1 v1
          -> view_format3 (v1, v2) env1 (mappend t1 t2, xenv2))
    : CorrectDecoder
      monoid
      Source_Predicate
      (fun v1v2 => View_Predicate1 (fst v1v2) /\ View_Predicate2 (fst v1v2) (snd v1v2))
      (fun s v1v2 => view1 s (fst v1v2) /\ view2 (fst v1v2) s (snd v1v2))
      (format1 ++ format2)
      (sequence_Decode' decode1 decode2) P
      view_format3.
Proof.
  unfold cache_inv_Property, sequence_Decode, sequence_Format, compose in *;
    split.
  { intros env env' xenv s t ext ? env_pm pred_pm com_pf.
    unfold compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend t1 ext) env_OK env_pm H com_pf); eauto; destruct_ex; split_and; simpl in *; injections; eauto.
    unfold sequence_Decode', DecodeBindOpt2, BindOpt.
    setoid_rewrite <- mappend_assoc; rewrite H0.
    pose proof (proj2 (decode1_pf H3) _ _ _ _ _ _ env_pm env_OK H0);
      split_and; destruct_ex; split_and.
    destruct (fun H => proj1 (decode2_pf x H5 H9)
                             _ _ _ _ _ ext H4 H2 H com_pf').
    split; try eassumption.
    eauto.
    destruct_ex; split_and.
    simpl.
    rewrite H12; eexists _, _; simpl; intuition eauto.
    apply unfold_computes.
    rewrite unfold_computes in H1.
    eapply view_format3_OK; eauto.
  }
  { intros ? ? ? ? t; intros.
    unfold sequence_Decode', DecodeBindOpt2, BindOpt in H1.
    destruct (decode1 t env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    generalize Heqo; intros Heqo'.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
    split_and; destruct_ex; split_and.
    subst.
    destruct (decode2 v0 t0 c) as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate; injections.
    eapply (proj2 (decode2_pf _ H5 H7)) in Heqo; eauto.
    destruct Heqo as [? ?]; destruct_ex; split_and; subst.
    setoid_rewrite mappend_assoc.
    split; eauto.
    eexists _, _; repeat split; eauto.
    apply unfold_computes.
    eapply view_format3_OK; try eassumption.
    apply unfold_computes; eassumption.
    apply unfold_computes; eassumption.
  }
Qed.

End SequenceFormat.

Notation "x ++ y" := (sequence_Format x y) : format_scope .
