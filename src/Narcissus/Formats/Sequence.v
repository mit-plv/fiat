Require Import
        Coq.omega.Omega
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
      (View_Predicate_OK : forall s v, Source_Predicate s ->
                                       view s v ->
                                       View_Predicate1 v)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK : CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
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
      (View_Predicate_OK : forall s v, Source_Predicate s -> view s v -> View_Predicate1 v)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK : CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
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
    unfold sequence_Decode' in H2.
    unfold sequence_Decode.
    destruct (decode1 (mappend t ext) env') as [ [ [? ?] ?] | ].
    destruct (decode2 v t0 c) as [ [ [? ?] ?] | ]; injections; simpl in *.
    unfold IsProj in *; eexists _, _; intuition eauto.
    discriminate.
    discriminate.
  - apply proj2 in Pair_Decode_OK.
    unfold sequence_Decode, sequence_Decode in *|-*.
    destruct (decode1 t env') as [ [ [? ?] ?] | ] eqn: ?; try discriminate.
    assert (sequence_Decode' decode1 decode2 t env' = Some ((v0, v), t', xenv'))
      by (unfold sequence_Decode'; rewrite Heqo, H1; eauto).
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
      (View_Predicate_OK : forall s, Source_Predicate s -> View_Predicate1 (f s))
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK : CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
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
      (f : S -> V1)
      (v1 : V1)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (v1_OK : View_Predicate1 v1)
      (View_Predicate_OK : forall s, Source_Predicate s -> View_Predicate1 (f s))
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK : CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
      (decode2 : DecodeM (S * T) T)
      (decode2_pf :
         forall v0 : V1,
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
      (view : S -> V1 -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate1  : V1 -> Prop)
      (View_Predicate_OK : forall v, View_Predicate1 v)
      (format1 : FormatM V1 T)
      (format2 : FormatM S T )
      (decode1 : DecodeM (V1 * T) T)
      (decode_1_OK : CorrectDecoder monoid View_Predicate1 View_Predicate1 eq format1 decode1 P format1)
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
  - unfold flip, pointwise_relation; intuition.
  - unfold flip, EquivFormat; reflexivity.
  - unfold flip, EquivFormat; reflexivity.
Qed.
