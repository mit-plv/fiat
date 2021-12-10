Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence.

Section EquivFormatFacts.

Open Scope format_scope.

Context {S T : Type}.
Context {store : Cache}.
Context {monoid : Monoid T}.

Lemma sequence_assoc
  : forall (format1 format2 format3 : FormatM S T),
    EquivFormat ((format1 ++ format2) ++ format3)%format
                (format1 ++ format2 ++ format3).
Proof.
  unfold sequence_Format, EquivFormat; intros.
  apply refineEquiv_compose_compose.
Qed.

Lemma sequence_mempty
  : forall (format : FormatM S T),
    EquivFormat (empty_Format ++ format) format.
Proof.
  unfold sequence_Format, EquivFormat; intros.
  apply refineEquiv_compose_Done.
Qed.

Lemma sequence_mempty'
  : forall (format : FormatM S T),
    EquivFormat (format ++ empty_Format) format.
Proof.
  unfold sequence_Format, EquivFormat, empty_Format; intros.
  split; unfold compose, Bind2; intros v Comp_v.
  - computes_to_econstructor; eauto. destruct_conjs; simpl.
    computes_to_econstructor; eauto. simpl.
    rewrite mempty_right; eauto.
  - computes_to_inv; subst; destruct_conjs. simpl.
    rewrite mempty_right; eauto.
Qed.

Lemma EquivFormat_ComposeIf
  : forall (formatT formatT' formatE formatE' : FormatM S T),
    EquivFormat formatT formatT'
    -> EquivFormat formatE formatE'
    -> EquivFormat (Either formatT Or formatE)
                   (Either formatT' Or formatE').
Proof.
  unfold EquivFormat; intros.
  eapply refineEquiv_ComposeIf; eauto.
Qed.

Lemma EquivFormat_UnderSequence
  : forall (format1 format2 format2' : FormatM S T),
    EquivFormat format2 format2'
    -> EquivFormat (format1 ++ format2)
                   (format1 ++ format2').
Proof.
  unfold EquivFormat; intros.
  eapply refineEquiv_under_compose; eauto.
Qed.

Lemma EquivFormat_If_Then_Else
  : forall b (formatT formatE format2 : FormatM S T),
    EquivFormat ((If b Then formatT Else formatE) ++ format2)
                (If b Then formatT ++ format2 Else formatE ++ format2).
Proof.
  unfold EquivFormat; intros.
  destruct b; simpl; reflexivity.
Qed.

Lemma EquivFormat_If_Then_Else_Proper
  : forall (c : bool), Proper (@EquivFormat S T _ ==> @EquivFormat S T _ ==> @EquivFormat S T _) (If_Then_Else c).
Proof.
  unfold Proper, EquivFormat, respectful; simpl; intros.
  destruct c; simpl; eauto.
Qed.

Lemma EquivFormat_Projection_Format_Empty_Format {S'}
  : forall (format : FormatM S' T) (f : S -> S'), EquivFormat (format ◦ f) ((format ◦ f) ++ empty_Format).
Proof.
  unfold EquivFormat, refineEquiv, sequence_Format, compose, Bind2, empty_Format; split;
    intros ? ?.
  - computes_to_inv; subst.
    destruct v0; simpl; rewrite mempty_right; assumption.
  - computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    simpl.
    destruct v; rewrite mempty_right; computes_to_econstructor.
Qed.

Lemma EquivFormat_trans
  : forall (FormatSpec FormatSpec' FormatSpec'' : FormatM S T),
    EquivFormat FormatSpec FormatSpec'
    -> EquivFormat FormatSpec' FormatSpec''
    -> EquivFormat FormatSpec FormatSpec''.
Proof.
  unfold EquivFormat; intros.
  etransitivity; eauto.
Qed.

Lemma EquivFormat_compose_id
  : forall (format : FormatM S T),
    EquivFormat format (format ◦ id).
Proof.
  intros.
  eapply EquivFormat_sym.
  eapply EquivFormat_trans.
  eapply EquivFormat_Projection_Format.
  unfold id.
  eapply EquivFormat_reflexive.
Qed.

Lemma EquivFormat_compose_map {S' S''}
      (format_S'' : FormatM S'' T)
      (f : S -> S')
      (g : S' -> S'')
  : EquivFormat (Projection_Format (Projection_Format format_S'' g) f)
                (Projection_Format format_S'' (Basics.compose g f)).
Proof.
  unfold EquivFormat, refineEquiv, Projection_Format, Compose_Format, compose, Bind2; split;
    intros ? ?.
  - rewrite unfold_computes in *.
    destruct_ex; split_and; eexists.
    rewrite unfold_computes;  eauto.
  - rewrite unfold_computes in *.
    destruct_ex; split_and; eexists; intuition eauto.
    rewrite unfold_computes in H0.
    destruct_ex.
    intuition eauto.
    subst.
    apply H0.
Qed.

Lemma EquivFormat_UnderSequence'
  : forall (format1 format1' format2 format2' : FormatM S T),
    EquivFormat format1 format1'
    -> EquivFormat format2 format2'
    -> EquivFormat (format1 ++ format2)
                   (format1' ++ format2').
Proof.
  unfold EquivFormat; intros.
  rewrite refine_sequence_Format.
  rewrite refine_sequence_Format.
  eapply refineEquiv_bind_Proper; eauto.
  unfold pointwise_relation; intros;
    eapply refineEquiv_bind_Proper; eauto.
  reflexivity.
Qed.

Lemma EquivFormat_Projection_Format_Empty_Format' {S' S''}
  : forall (format : FormatM S' T)
           (format' : FormatM S'' T)
           (f : S -> S')
           (g : S -> S''),
    EquivFormat (format ◦ f) (format' ◦ g)
    -> EquivFormat (format ◦ f) (format' ◦ g ++ empty_Format).
Proof.
  intros.
  eapply EquivFormat_trans; try eassumption.
  eapply EquivFormat_Projection_Format_Empty_Format.
Qed.

End EquivFormatFacts.

Add Parametric Morphism
    S T
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (decode : DecodeM (S * T) T)
    (decode_inv : CacheDecode -> Prop)
  : (fun format =>
       @CorrectDecoder S T cache S monoid Source_Predicate Source_Predicate
                       eq format decode decode_inv format)
    with signature (EquivFormat --> impl)
      as format_decode_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  eapply format_decode_correct_alt_Proper; eauto; try reflexivity.
Qed.
