Require Import
        Coq.omega.Omega
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Computation.Refinements.General
        Fiat.Narcissus.BaseFormats.

Definition sequence_Decode
           {S S' T : Type}
           {cache : Cache}
           (decode1 : DecodeM (S' * T) T)
           (decode2 : S' -> DecodeM (S * T) T)
  : DecodeM (S * T) T :=
  fun t env =>
    `(s', t', env') <- decode1 t env;
      decode2 s' t' env'.

(* An alias so that our automation can identify facts about the
projection of the source value learned during decoding *)  
Definition IsProj {S S'}
           (f : S -> S')
           (s : S)
           (s' : S') :=
  f s = s'.

Lemma format_sequence_correct
      {S S' T}
      {cache : Cache}
      {Q  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property Q (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (f : S -> S')
      (P : S -> Prop)
      (P' : S' -> Prop)
      (format1 : FormatM S' T)
      (format2 : FormatM S T)
      (decode1 : DecodeM (S' * T) T)
      (decode1_pf :
         cache_inv_Property Q P_inv1
         -> CorrectDecoder
              monoid P'
              (fun _ _ => True)
              format1 decode1 Q)
      (pred_pf : forall s, P s -> P' (f s))
      (decode2 : S' -> DecodeM (S * T) T)
      (decode2_pf : forall s',
          P' s' ->
          cache_inv_Property Q P_inv2 ->
          CorrectDecoder monoid (fun s => P s /\ IsProj f s s')
                         (fun _ _ => True)
                         format2
                         (decode2 s') Q)
  : CorrectDecoder
      monoid
      (fun a => P a)
      (fun _ _ => True)
      (format1 ◦ f ++ format2)
      (sequence_Decode decode1 decode2) Q.
Proof.
  unfold IsProj.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold sequence_Format, Projection_Format, Compose_Format, ComposeOpt.compose, Bind2 in com_pf; computes_to_inv. destruct v;
      destruct v0.
    apply (proj1 (unfold_computes _ _)) in com_pf;
      simpl in com_pf; destruct com_pf as [? [com_pf ?] ]; subst.
    destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend t0 ext) env_OK env_pm (pred_pf _ pred_pm) H' com_pf); intuition; simpl in *; injections; eauto.
    unfold sequence_Decode.
    setoid_rewrite <- mappend_assoc; rewrite H2.
    destruct (fun H'' => proj1 (decode2_pf (f _) (pred_pf _ pred_pm) H1)
                               _ _ _ _ _ ext H4 H (conj pred_pm (eq_refl _)) H'' com_pf');
      intuition; simpl in *; injections.
    eauto. }
  { intros.
    unfold sequence_Decode in *.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
    destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ].
    eapply (proj2 (decode2_pf s H5 (proj2 P_inv_pf))) in H2; eauto.
    destruct H2 as [? ?]; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    unfold sequence_Format, ComposeOpt.compose, Projection_Format, Compose_Format.
    repeat computes_to_econstructor; eauto.
    apply unfold_computes; eexists; eauto.
    eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

Lemma format_const_sequence_correct
      {S S' T}
      {cache : Cache}
      {Q  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      {S'_eq_dec : DecideableEnsembles.Query_eq S'}
      (P_inv_pf : cache_inv_Property Q (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (s' : S')
      (P : S -> Prop)
      (P' : S' -> Prop)
      (format1 : FormatM S' T)
      (format2 : FormatM S T)
      (decode1 : DecodeM (S' * T) T)
      (decode1_pf :
         cache_inv_Property Q P_inv1
         -> CorrectDecoder
              monoid P'
              (fun _ _ => True)
              format1 decode1 Q)
      (s'_OK : P' s')
      (decode2 : DecodeM (S * T) T)
      (decode2_pf :
         cache_inv_Property Q P_inv2 ->
         CorrectDecoder monoid P
                        (fun _ _ => True)
                        format2
                        (decode2 ) Q)
  : CorrectDecoder
      monoid
      (fun a => P a)
      (fun _ _ => True)
      (format1 ◦ (fun _ => s') ++ format2)
      (sequence_Decode decode1
                       (fun s rest env' =>
                          (if DecideableEnsembles.A_eq_dec s s' then decode2 rest env' else None)))
      Q.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold sequence_Format, Projection_Format, Compose_Format, ComposeOpt.compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    apply (proj1 (unfold_computes _ _)) in com_pf;
      simpl in com_pf; destruct com_pf as [? [com_pf ?] ]; subst.
    destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend t0 ext) env_OK env_pm s'_OK H' com_pf); intuition; simpl in *; injections; eauto.
    unfold sequence_Decode.
    setoid_rewrite <- mappend_assoc; rewrite H2.
    destruct (fun H'' => proj1 H5 _ _ _ _ _ ext H4 H pred_pm H'' com_pf');
      intuition; simpl in *; injections.
    find_if_inside; eauto.
    congruence. }
  { intros.
    unfold sequence_Decode in *.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
    destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ].
    find_if_inside; try discriminate.
    subst.
    eapply (proj2 (decode2_pf (proj2 P_inv_pf))) in H2; eauto.
    destruct H2 as [? ?]; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    unfold sequence_Format, compose, Projection_Format, Compose_Format.
    repeat computes_to_econstructor; eauto.
    apply unfold_computes; eexists; eauto.
    eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.

Lemma format_unused_sequence_correct
      {S S' T}
      {cache : Cache}
      {Q  : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      {S'_eq_dec : DecideableEnsembles.Query_eq S'}
      (P_inv_pf : cache_inv_Property Q (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (P' : S' -> Prop)
      (P : S -> Prop)
      (format1 : FormatM S' T)
      (format2 : FormatM S T)
      (decode1 : DecodeM (S' * T) T)
      (decode1_pf :
         cache_inv_Property Q P_inv1
         -> CorrectDecoder
              monoid P'
              (fun _ _ => True)
              format1 decode1 Q)
      (s'_OK : forall s', P' s')
      (decode2 : DecodeM (S * T) T)
      (decode2_pf :
         cache_inv_Property Q P_inv2 ->
         CorrectDecoder monoid P
                        (fun _ _ => True)
                        format2
                        (decode2 ) Q)
  : CorrectDecoder
      monoid
      (fun a => P a)
      (fun _ _ => True)
      (Compose_Format format1 (fun _ _ => True) ++ format2)
      (sequence_Decode decode1
                       (fun _ rest env' => decode2 rest env'))
      Q.
Proof.
  unfold cache_inv_Property in *; split.
  { intros env env' xenv data bin ext ? env_pm pred_pm pred_pm_rest com_pf.
    unfold sequence_Format, Projection_Format, Compose_Format, ComposeOpt.compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    apply (proj1 (unfold_computes _ _)) in com_pf;
      simpl in com_pf; destruct com_pf as [? [com_pf ?] ]; subst.
    destruct (fun H' => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend t0 ext) env_OK env_pm (s'_OK _) H' com_pf); intuition; simpl in *; injections; eauto.
    unfold sequence_Decode.
    setoid_rewrite <- mappend_assoc; rewrite H3.
    destruct (fun H'' => proj1 H6 _ _ _ _ _ ext H5 H0 pred_pm H'' com_pf');
      intuition; simpl in *; injections; eauto. }
  { intros.
    unfold sequence_Decode in *.
    destruct (decode1 bin env') as [ [ [? ?] ? ] | ] eqn : ? ;
      simpl in *; try discriminate.
    eapply (proj2 (decode1_pf (proj1 P_inv_pf))) in Heqo; eauto.
    destruct Heqo as [? [? [? [? [? [? ?] ] ] ] ] ].
    subst.
    eapply (proj2 (decode2_pf (proj2 P_inv_pf))) in H2; eauto.
    destruct H2 as [? ?]; destruct_ex; intuition; subst.
    eexists; eexists; repeat split.
    unfold sequence_Format, compose, Projection_Format, Compose_Format.
    repeat computes_to_econstructor; eauto.
    apply unfold_computes; eexists; eauto.
    eauto.
    simpl; rewrite mappend_assoc; reflexivity.
    eassumption.
    eassumption.
  }
Qed.
