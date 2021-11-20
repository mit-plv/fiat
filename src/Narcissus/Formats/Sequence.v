Require Import
        Coq.ZArith.ZArith
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Computation.Refinements.General
        Fiat.Narcissus.BaseFormats.

(* An alias so that our automation can identify facts about the
projection of the source value learned during decoding *)
Definition IsProj {S S'}
           (f : S -> S')
           (s' : S')
           (s : S) :=
  f s = s'.

Lemma Sequence_refined_decoder_correct
        {S V1 V2 T : Type}
        {monoid : Monoid T}
        {cache : Cache}
        {P : CacheDecode -> Prop}
        {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
        (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
        (view1 : S -> V1 -> Prop)
        (view2 : V1 -> S -> V2 -> Prop)
        (Source_Predicate : S -> Prop)
        (View_Predicate2 : V1 -> V2 -> Prop)
        (View_Predicate1 : V1 -> Prop)
        (format1 format2 subformat : FormatM S T)
        (decode1 : DecodeM (V1 * T) T)
        (view_format1 : FormatM V1 T)
      (decode1_pf :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid Source_Predicate View_Predicate1 view1 format1 decode1 P view_format1)
      (decode2 : V1 -> DecodeM (V2 * T) T)
      (view_format2 : V1 -> FormatM V2 T)
      (view_format3 : FormatM (V1 * V2) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectRefinedDecoder monoid (fun s => Source_Predicate s
                                                 /\ view1 s v1)
                         (View_Predicate2 v1) (view2 v1) format2 subformat (decode2 v1) P (view_format2 v1))
      (view_format3_OK : forall v1 t1 env1 xenv1 v2 t2 xenv2,
          view_format1 v1 env1 (t1, xenv1)
          -> view_format2 v1 v2 xenv1 (t2, xenv2)
          -> View_Predicate1 v1
          -> view_format3 (v1, v2) env1 (mappend t1 t2, xenv2))
    : CorrectRefinedDecoder
      monoid
      Source_Predicate
      (fun v1v2 => View_Predicate1 (fst v1v2) /\ View_Predicate2 (fst v1v2) (snd v1v2))
      (fun s v1v2 => view1 s (fst v1v2) /\ view2 (fst v1v2) s (snd v1v2))
      (format1 ++ format2)
      (format1 ++ subformat)
      (sequence_Decode' decode1 decode2) P
      view_format3.
Proof.
  unfold cache_inv_Property, sequence_Decode, sequence_Format, compose in *;
    split.
  { intros env env' xenv s t ext ? env_pm pred_pm com_pf.
    unfold ComposeOpt.compose, Bind2 in com_pf; computes_to_inv; destruct v;
      destruct v0.
    destruct (fun H => proj1 (decode1_pf (proj1 P_inv_pf)) _ _ _ _ _ (mappend t1 ext) env_OK env_pm H com_pf); eauto; destruct_ex; split_and; simpl in *; injections; eauto.
    unfold sequence_Decode', DecodeBindOpt2, BindOpt.
    setoid_rewrite <- mappend_assoc; rewrite H0.
    pose proof (proj2 (decode1_pf H3) _ _ _ _ _ _ env_pm env_OK H0);
      split_and; destruct_ex; split_and.
    simpl.
    destruct (fun H => proj1 (decode2_pf x H5 H9)
                             _ _ _ _ _ ext H4 H2 H com_pf').
    split; try eassumption.
    eauto.
    destruct_ex; split_and.
    simpl.
    rewrite H12; eexists _, _; simpl; intuition eauto.
    apply unfold_computes.
    rewrite unfold_computes in H1.
    rewrite unfold_computes in H13; split_and.
    split.
    eapply view_format3_OK; eauto.
    intros.
    simpl.
    unfold ComposeOpt.compose, Bind2 in H19; computes_to_inv;
      simpl in *; injections; destruct v; destruct v0; simpl in *.
    eapply (proj1 H15) in H19.
    rewrite mappend_assoc in H0; rewrite <- H21 in H0.
    rewrite <- mappend_assoc in H0.
    rewrite H0 in H19; destruct_ex; split_and.
    injections; eauto.
    split; eauto.
    all: eauto.
    eapply decode2_pf in H19'; split_and; destruct_ex; split_and.
    rewrite <- H26 in H24.
    rewrite H12 in H24.
    injections; intuition eauto.
    all: eauto.
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
    generalize Heqo as Heqo''; intro.
    eapply (proj2 (decode2_pf _ H5 H7)) in Heqo; eauto.
    destruct Heqo as [? ?]; destruct_ex; split_and; subst.
    setoid_rewrite mappend_assoc.
    split; eauto.
    eexists _, _; split; eauto.
    apply unfold_computes; split.
    eapply view_format3_OK; try eassumption.
    apply unfold_computes; eassumption.
    rewrite unfold_computes in H8.
    apply unfold_computes; intuition eauto.
    intros;
    unfold ComposeOpt.compose, Bind2 in H11; computes_to_inv;
      simpl in *; injections; destruct v; destruct v2; simpl in *.
    eapply (proj1 (decode1_pf _)) in H11.
    rewrite mappend_assoc in Heqo'; rewrite <- H14 in Heqo'.
    rewrite <- mappend_assoc in Heqo'.
    rewrite Heqo' in H11; destruct_ex; split_and.
    injections; eauto.
    all: eauto.
    eapply decode2_pf in H11'; split_and; destruct_ex; split_and.
    rewrite H19 in Heqo''.
    rewrite Heqo'' in H17.
    injections; intuition eauto.
    all: eauto.
  }
  Unshelve.
  eauto.
Qed.

Lemma sequence_Compose_format_decode_refined_correct'
      {cache : Cache}
      {S V1 V2 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view : S -> V1 -> Prop)
      (view2 : S -> V2 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s v, Source_Predicate s ->
                                       view s v ->
                                       View_Predicate1 v)
      (decode2 : V1 -> DecodeM (V2 * T) T)
      (View_Predicate2 : V2 -> Prop)
      (subformat : FormatM S T)
      (view_format : FormatM V2 T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectRefinedDecoder monoid (fun s => Source_Predicate s /\ view s v1)
                                View_Predicate2
                                view2
                                format2
                                subformat
                                (decode2 v1) P view_format)
  : CorrectRefinedDecoder
      monoid
      Source_Predicate
      View_Predicate2
      view2
      (Compose_Format format1 view  ++ format2)%format
      (Compose_Format format1 view  ++ subformat)%format
      (sequence_Decode decode1 decode2)
      P
      (Compose_Format format1 (fun _ _ => True) ++ view_format)%format.
Proof.
  intros.
  eapply format_decode_correct_alt.
  6: apply EquivFormat_reflexive.
  6: {
  eapply injection_decode_correct.
  - eapply Sequence_refined_decoder_correct.
    + apply P_inv_pf.
    + intros; eapply Compose_decode_correct.
      intros; eapply decode_1_OK; eauto.
      intros; eapply View_Predicate_OK; eauto.
    + intros; eapply decode2_pf; eauto.
    + intros.
      instantiate (1 := (Projection_Format format1 fst ++ Projection_Format view_format snd)%format).
      unfold Projection_Format, Compose_Format, sequence_Format,
      ComposeOpt.compose, Bind2.
      apply unfold_computes; computes_to_econstructor.
      apply unfold_computes.
      simpl; eexists _; intuition eauto.
      apply unfold_computes; apply H.
      computes_to_econstructor.
      apply unfold_computes.
      simpl; eexists _; intuition eauto.
      apply unfold_computes; eauto.
      simpl; eauto.
  - simpl; intros; split_and; eauto.
  - simpl; intros; split_and; eauto.
  - simpl; intros.
    rewrite unfold_computes in H.
    split_and.
    split.
    + unfold Projection_Format, Compose_Format, sequence_Format,
      ComposeOpt.compose, Bind2 in *; apply unfold_computes in H0; computes_to_inv.
      rewrite unfold_computes in H0.
      rewrite unfold_computes in H0';
        destruct_ex; intuition; subst.
      apply unfold_computes.
      computes_to_econstructor.
      apply unfold_computes.
      eexists _; split; eauto.
      computes_to_econstructor; eauto.
    + eauto.
  }
  all: try unfold flip, pointwise_relation, impl;
    intuition eauto using EquivFormat_reflexive.
  unfold Compose_Decode, sequence_Decode, sequence_Decode'; simpl.
  destruct (decode1 a a0) as [ [ [? ?] ?] | ]; simpl; eauto.
  destruct (decode2 v t c)as [ [ [? ?] ?] | ]; simpl; eauto.
Qed.

Lemma format_sequence_refined_correct
            {cache : Cache}
      {S V1 V2 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (f : S -> V1)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (View_Predicate2 : V2 -> Prop)
      (format1 : FormatM V1 T)
      (format2 subformat : FormatM S T )
      (view_format : FormatM V2 T)
      (view : S -> V2 -> Prop)
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s, Source_Predicate s -> View_Predicate1 (f s))
      (decode2 : V1 -> DecodeM (V2 * T) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectRefinedDecoder monoid (fun s => Source_Predicate s
                                          /\ IsProj f v1 s)
                         View_Predicate2
                         view format2 subformat (decode2 v1) P view_format)
  : CorrectRefinedDecoder
      monoid
      Source_Predicate
      View_Predicate2
      view
      (format1 ◦ f ++ format2)
      (format1 ◦ f ++ subformat)
      (sequence_Decode decode1 decode2)
      P
      (Compose_Format format1 (fun _ _ => True) ++ view_format)%format.
Proof.
  eapply sequence_Compose_format_decode_refined_correct'; try eassumption.
  intros; subst; eauto.
Qed.

Lemma sequence_Compose_format_decode_correct'
      {cache : Cache}
      {S V1 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view : S -> V1 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s v, Source_Predicate s ->
                                       view s v ->
                                       View_Predicate1 v)
      (decode2 : V1 -> DecodeM (S * T) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectDecoder monoid (fun s => Source_Predicate s
                                          /\ view s v1)
                         (fun s => Source_Predicate s
                                          /\ view s v1)
                         eq format2 (decode2 v1) P format2)
  : CorrectDecoder
      monoid
      Source_Predicate
      (fun v1v2 => View_Predicate1 (fst v1v2) /\ (Source_Predicate (snd v1v2)
                                                  /\ view (snd v1v2) (fst v1v2)))
      (fun s v1v2 => view s (fst v1v2) /\ s = (snd v1v2))
      (Compose_Format format1 view  ++ format2)
      (sequence_Decode' decode1 decode2)
      P (fun v1s => ComposeOpt.compose monoid (format1 (fst v1s)) (format2 (snd v1s))).
Proof.
  eapply Sequence_decode_correct with (view1 := view)
                                      (view2 := fun _ => eq)
                                      (View_Predicate2 := fun v1 v2 => Source_Predicate v2 /\
                                                                       view v2 v1)
                                      (consistency_predicate := fun v1 s => view s v1);
    try eassumption; eauto.
  - intros; eapply Compose_decode_correct; try eassumption;
    intros; eauto.
  - instantiate (1 := fun _ => format2); eauto.
  - simpl; intros.
    unfold sequence_Format, ComposeOpt.compose, Bind2,
    Projection_Format, Compose_Format.
    apply unfold_computes.
    apply unfold_computes in H.
    apply unfold_computes in H0.
    eauto.
Qed.

(*Lemma sequence_Compose_format_decode_correct_view
            {cache : Cache}
      {S V1 V2 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view : S -> V1 -> Prop)
      (view2 : S -> V2 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s v, Source_Predicate s -> view s v -> View_Predicate1 v)
      (decode2 : V1 -> DecodeM (V2 * T) T)
      (View_Predicate2 : V2 -> Prop)
      (view_format : FormatM V2 T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectDecoder monoid (fun s => Source_Predicate s
                                          /\ view s v1)
                         View_Predicate2
                         view2 format2 (decode2 v1) P view_format)
  : CorrectDecoder
      monoid
      Source_Predicate
      View_Predicate2
      view2
      (Compose_Format format1 view ++ format2)
      (sequence_Decode decode1 decode2)
      P
      (Compose_Format (Compose_Format format1 view) (fun _ _ => True) ++ view_format)%format.
Proof.
  eapply format_decode_correct_alt'.
  7: { eapply injection_decode_correct.
       eapply sequence_Compose_format_decode_correct_view'; try eauto.
       - intros; eapply decode2_pf; eauto.
       - intros; simpl in H0; split_and; apply H2.
       - simpl; intros; split_and; apply H1.
       - intros.
         instantiate (1 := (Compose_Format (Compose_Format format1 view) (fun _ v => True) ++ view_format)%format).
         unfold sequence_Format, ComposeOpt.compose, Compose_Format, Bind2 in *;
           computes_to_inv; simpl in *; subst.
  }
  all: try unfold flip, pointwise_relation, impl;
    intuition eauto using EquivFormat_reflexive.
  unfold Compose_Decode, sequence_Decode, sequence_Decode'; simpl.
  destruct (decode1 a a0) as [ [ [? ?] ?] | ]; simpl; eauto.
  destruct (decode2 v t c)as [ [ [? ?] ?] | ]; simpl; eauto.
Qed. *)

Lemma sequence_Compose_format_decode_correct
            {cache : Cache}
      {S V1 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (view : S -> V1 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s v, Source_Predicate s -> view s v -> View_Predicate1 v)
      (decode2 : V1 -> DecodeM (S * T) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectDecoder monoid (fun s => Source_Predicate s
                                          /\ view s v1)
                         (fun s => Source_Predicate s
                                          /\ view s v1)
                         eq format2 (decode2 v1) P format2)
  : CorrectDecoder
      monoid
      Source_Predicate
      Source_Predicate
      eq
      (Compose_Format format1 view ++ format2)
      (sequence_Decode decode1 decode2)
      P
      (Compose_Format format1 view ++ format2).
Proof.
  assert (CorrectDecoder
      monoid
      Source_Predicate
      (fun v1v2 => View_Predicate1 (fst v1v2) /\ (Source_Predicate (snd v1v2)
                                                  /\ view (snd v1v2) (fst v1v2)))
      (fun s v1v2 => view s (fst v1v2) /\ s = (snd v1v2))
      (Compose_Format format1 view ++ format2)
      (sequence_Decode' decode1 decode2)
      P (fun v1s => ComposeOpt.compose monoid (format1 (fst v1s)) (format2 (snd v1s))))
    as Pair_Decode_OK; eauto using sequence_Compose_format_decode_correct';
    generalize Pair_Decode_OK; clear; intros.
  unfold CorrectDecoder; split_and; split; intros.
  - apply proj1 in Pair_Decode_OK.
    eapply Pair_Decode_OK with (ext := ext) in H1; eauto.
    destruct_ex; split_and.
    unfold sequence_Decode', sequence_Decode, DecodeBindOpt2, BindOpt in *.
    destruct (decode1 (mappend t ext) env') as [ [ [? ?] ?] | ]; simpl in *.
    destruct (decode2 v t0 c) as [ [ [? ?] ?] | ]; injections; simpl in *.
    unfold IsProj in *; eexists _, _; intuition eauto.
    unfold Compose_Format, sequence_Format, ComposeOpt.compose, Bind2 in *.
    computes_to_inv; computes_to_econstructor.
    apply unfold_computes; simpl; eauto.
    computes_to_econstructor; eauto.
    rewrite H3''; eauto.
    discriminate.
    discriminate.
  - apply proj2 in Pair_Decode_OK.
    unfold sequence_Decode', sequence_Decode, DecodeBindOpt2, BindOpt in *.
    destruct (decode1 t env') as [ [ [? ?] ?] | ] eqn: ?; try discriminate; simpl in *.
    assert (sequence_Decode' decode1 decode2 t env' = Some ((v0, v), t', xenv'))
      by (unfold sequence_Decode', DecodeBindOpt2, BindOpt; simpl;
          rewrite Heqo; simpl; rewrite H1; eauto).
    eapply Pair_Decode_OK in H2; eauto.
    intuition eauto.
    clear Pair_Decode_OK.
    destruct_ex; split_and; subst.
    eexists _, _; intuition eauto.
    unfold sequence_Format, Projection_Format, ComposeOpt.compose,
    Bind2, Compose_Format in *.
    computes_to_inv.
    destruct v1; destruct v2; simpl in *; computes_to_econstructor; eauto.
    apply unfold_computes; eauto.
    simpl; computes_to_econstructor; cbv beta; simpl; eauto.
    simpl; rewrite H4''; eauto.
Qed.

Lemma format_sequence_correct
            {cache : Cache}
      {S V1 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (f : S -> V1)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall s, Source_Predicate s -> View_Predicate1 (f s))
      (decode2 : V1 -> DecodeM (S * T) T)
      (decode2_pf : forall v1 : V1,
          cache_inv_Property P P_inv2 ->
          View_Predicate1 v1 ->
          CorrectDecoder monoid (fun s => Source_Predicate s
                                          /\ IsProj f v1 s)
                         (fun s => Source_Predicate s
                                          /\ IsProj f v1 s)
                         eq format2 (decode2 v1) P format2)
  : CorrectDecoder
      monoid
      Source_Predicate
      Source_Predicate
      eq
      (format1 ◦ f ++ format2)
      (sequence_Decode decode1 decode2)
      P
      (format1 ◦ f ++ format2).
Proof.
  eapply sequence_Compose_format_decode_correct; try eassumption.
  intros; subst; eauto.
Qed.

Lemma format_const_sequence_correct
      {cache : Cache}
      {S V1 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (v1 : V1)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (v1_OK : View_Predicate1 v1)
      (decode2 : DecodeM (S * T) T)
      (decode2_pf :
         forall v0,
           cache_inv_Property P P_inv2 ->
           View_Predicate1 v0 ->
           CorrectDecoder monoid (fun s : S => Source_Predicate s /\ v1 = v0) (fun s : S => Source_Predicate s /\ v1 = v0) eq format2
                          decode2 P format2)
  : CorrectDecoder
      monoid
      Source_Predicate
      Source_Predicate
      eq
      (format1 ◦ (fun _ => v1) ++ format2)
      (sequence_Decode decode1 (fun _ => decode2))
      P
      (format1 ◦ (fun _ => v1) ++ format2).
Proof.
  unfold IsProj in *.
  eapply format_sequence_correct; eauto.
Qed.

Lemma format_unused_sequence_correct
      {cache : Cache}
      {S V1 T : Type}
      {P : CacheDecode -> Prop}
      {P_inv1 P_inv2 : (CacheDecode -> Prop) -> Prop}
      (P_inv_pf : cache_inv_Property P (fun P => P_inv1 P /\ P_inv2 P))
      (monoid : Monoid T)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK :
         cache_inv_Property P P_inv1
         -> CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (View_Predicate_OK : forall v, View_Predicate1 v)
      (decode2 : DecodeM (S * T) T)
      (decode2_pf :
          cache_inv_Property P P_inv2 ->
          CorrectDecoder monoid Source_Predicate
                         Source_Predicate
                         eq format2 decode2 P format2)
  : CorrectDecoder
      monoid
      Source_Predicate
      Source_Predicate
      eq
      (Compose_Format format1 (fun _ _ => True) ++ format2)
      (sequence_Decode decode1 (fun _ => decode2))
      P
      (Compose_Format format1 (fun _ _ => True) ++ format2).
Proof.
  eapply sequence_Compose_format_decode_correct; intros; eauto.
  eauto.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
  - unfold flip, pointwise_relation; intuition.
  - unfold flip, pointwise_relation, impl; intuition.
  - unfold flip, EquivFormat; reflexivity.
  - unfold flip, EquivFormat; reflexivity.
Qed.

Lemma refine_sequence_Format
      {cache : Cache}
      {S T : Type}
      {monoid : Monoid T}
      (format1 format2 : FormatM S T)
  : forall s env,
    refineEquiv ((format1 ++ format2) s env)
                ((fun (s : S) => (ComposeOpt.compose _ (format1 s) (format2 s))) s env).
Proof.
  reflexivity.
Qed.
