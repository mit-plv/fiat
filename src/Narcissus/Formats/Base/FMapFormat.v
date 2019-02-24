Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.Narcissus.Common.Specs.

Section ComposeFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {S' : Type}. (* Transformed Type *)

  Definition Compose_Format
    (format : FormatM S' T)
      (f : S -> S' -> Prop) (* Transformation Relation *)
    : FormatM S T :=
    fun s env benv' =>
      exists s', format s' env ∋ benv' /\ f s s'.

  Definition Compose_Decode {S' : Type}
             (decode : DecodeM S' T)
             (g : S' -> S) (* Transformation Function *)
    : DecodeM S T  :=
    fun b env => `(s, env') <- decode b env; Some (g s, env').

  Definition Compose_Encode
             {S' : Type}
             (encode : EncodeM S' T)
             (f' : S -> option S')
    : EncodeM S T :=
    fun s => Ifopt f' s as s' Then encode s' Else fun _ => None.

  Lemma CorrectEncoder_Compose
        (format : FormatM S' T)
        (encode : EncodeM S' T)
        (f : S -> S' -> Prop)
        (f' : S -> option S')
        (f'_refines_f_1 :
           forall s s',
             f' s = Some s' ->
             f s s')
        (f'_refines_f_2 :
           forall s,
             f' s = None ->
             forall s', ~ f s s')
        (f'_sound_choice :
           forall s s',
             f' s = Some s' ->
             forall x env benv,
               format x env ∋ benv
               -> f s x
               -> format s' env ∋ benv)
    : CorrectEncoder format encode
      -> CorrectEncoder (Compose_Format format f) (Compose_Encode encode f').
  Proof.
    unfold CorrectEncoder, Compose_Encode, Compose_Format in *; split; intros.
    - apply unfold_computes.
      destruct (f' a) eqn: ?; simpl in *; try discriminate.
      eapply H in H0; eexists; intuition eauto.
    - rewrite unfold_computes; intro;  destruct_ex; split_and.
      destruct (f' a) eqn: ?; simpl in *; try discriminate.
      eapply H4; eauto.
      eapply f'_refines_f_2; eauto.
  Qed.

End ComposeFormat.

Section ComposeSpecializations.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {S' : Type}. (* Transformed Type *)

  Definition Restrict_Format
             (P : S -> Prop)
             (format : FormatM S T)
    : FormatM S T
    := Compose_Format format (fun s s' => s = s' /\ P s').

  Corollary CorrectEncoder_Restrict_Format
            (format : FormatM S T)
            (encode : EncodeM S T)
            (P : S -> Prop)
            (decideable_P : DecideableEnsemble P)
    : CorrectEncoder format encode
      -> CorrectEncoder (Restrict_Format P format) (fun s => if (DecideableEnsembles.dec s) then encode s else fun _ => None).
  Proof.
    intros; replace
              (fun s : S => if DecideableEnsembles.dec s then encode s else fun _ : CacheFormat => None)
              with (Compose_Encode encode (fun s => if DecideableEnsembles.dec s then Some s else None)).
    eapply CorrectEncoder_Compose; intros;
      try (destruct (DecideableEnsembles.dec s) eqn: ?; first [discriminate | injections]);
      intuition eauto.
    - eapply dec_decides_P; eauto.
    - eapply Decides_false; subst; eauto.
    - subst; eauto.
    - apply functional_extensionality; intros; unfold Compose_Encode;
        find_if_inside; reflexivity.
  Qed.

  Definition Projection_Format
             (format : FormatM S' T)
             (f : S -> S')
    : FormatM S T :=
    Compose_Format format (fun s s' => f s = s').

  Lemma EquivFormat_Projection_Format
        (format : FormatM S' T)
        (f : S -> S')
    : EquivFormat (Projection_Format format f)
                  (fun s => format (f s)).
  Proof.
    unfold EquivFormat, Projection_Format, Compose_Format; split; intros ? ?.
    apply unfold_computes.
    eexists; eauto.
    rewrite unfold_computes in H; destruct_ex; intuition; subst; eauto.
  Qed.

  Corollary CorrectEncoder_Projection_Format
            (format : FormatM S' T)
            (encode : EncodeM S' T)
            (g : S -> S')
    : CorrectEncoder format encode
      -> CorrectEncoder (Projection_Format format g) (compose encode g).
  Proof.
    intros; replace
              (compose encode g)
              with (Compose_Encode encode (fun s => Some (g s))).
    eapply CorrectEncoder_Compose; intros;
      try (destruct (DecideableEnsembles.dec s') eqn: ?; first [discriminate | injections]);
      intuition eauto.
    apply functional_extensionality; intros; reflexivity.
  Qed.

End ComposeSpecializations.

Lemma Projection_format_compose
      {S S' S'' T}
      {monoid : Monoid T}
      {cache : Cache}
  : forall (f : S -> S')
           (f' : S' -> S'')
           (formatS'' : FormatM S'' T)
           (formatS : FormatM S T),
    EquivFormat (Projection_Format (Projection_Format formatS'' f') f)
                (Projection_Format formatS'' (f' ∘ f)).
Proof.
  unfold EquivFormat, refineEquiv; intros.
  unfold Projection_Format, Compose_Format; split;
    intros ? ?.
  - apply unfold_computes.
    apply (proj1 (unfold_computes _ _)) in H; simpl in *.
    destruct_ex; eexists; intuition eauto.
    apply unfold_computes.
    eexists; intuition eauto.
  -  apply (proj2 (unfold_computes _ _)); simpl in *.
     apply (proj1 (unfold_computes _ _)) in H; simpl in *.
     destruct_ex; intuition.
     apply (proj1 (unfold_computes _ _)) in H0; simpl in *.
     destruct_ex; intuition eauto.
     eexists.
     split; eauto.
     unfold Basics.compose; congruence.
Qed.

Lemma Compose_decode_correct {S V T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (view : S -> V -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (View_Predicate_OK : forall s v, view s v -> Source_Predicate s -> View_Predicate v)
      (format : FormatM V T)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate eq format decode_V P
      view_format)
  : CorrectDecoder monoid Source_Predicate View_Predicate view
                   (Compose_Format format view) decode_V P view_format.
Proof.
  unfold CorrectDecoder, Projection_Format, Compose_Format; split; intros.
  { rewrite @unfold_computes in H1; destruct_ex; intuition.
    apply proj1 in decode_V_OK; eapply decode_V_OK with (ext := ext) in H2; eauto.
    destruct_ex; intuition; subst; eauto.
    eexists _, _; intuition eauto. }
  { apply proj2 in decode_V_OK; eapply decode_V_OK in H1;
      clear decode_V_OK; eauto. }
Qed.

Lemma projection_decode_correct {S V T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (project : S -> V)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (View_Predicate_OK : forall (s : S), Source_Predicate s -> View_Predicate (project s))
      (format : FormatM V T)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate eq format decode_V P view_format)
  : CorrectDecoder monoid Source_Predicate View_Predicate (fun s v => project s = v)
                   (Projection_Format format project) decode_V P view_format.
Proof.
  eapply Compose_decode_correct; intros; eauto.
  subst; eauto.
Qed.

Lemma injection_decode_correct {S V V' T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (inj : V -> V')
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (View'_Predicate : V' -> Prop)
      (format : FormatM S T)
      (view : S -> V -> Prop)
      (view' : S -> V' -> Prop)
      (view_format : FormatM V T)
      (view'_format : FormatM V' T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid Source_Predicate View_Predicate
                                    view format decode_V P view_format)
      (view'_OK : forall s v, Source_Predicate s -> view s v -> view' s (inj v))
      (View'_Predicate_OK : forall v, View_Predicate v
                                      -> View'_Predicate (inj v))
      (view'_format_OK : forall v env t,
          computes_to (view_format v env) t
          -> computes_to (view'_format (inj v) env) t)
  : CorrectDecoder monoid Source_Predicate View'_Predicate
                   view'
                   format (Compose_Decode decode_V (fun s => (inj (fst s), snd s)))
                   P view'_format.
Proof.
  unfold CorrectDecoder, Projection_Format, Compose_Decode; split; intros.
  { apply proj1 in decode_V_OK; eapply decode_V_OK with (ext := ext) in H1; eauto.
    destruct_ex; intuition; subst; eauto.
    eexists _, _; intuition eauto; rewrite H2; simpl; eauto.
  }
  { destruct (decode_V t env') as [ [ [? ?] ?] |] eqn: ? ;
      simpl in *; try discriminate; injections.
    apply proj2 in decode_V_OK;
      eapply decode_V_OK in Heqo; eauto.
    intuition; destruct_ex; split_and; eexists _, _; intuition eauto.
  }
Qed.

Lemma bijection_decode_correct {S V T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (proj : S -> V)
      (inj : V -> S)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate
                                    eq view_format decode_V P view_format)
      (view_OK : forall s, Source_Predicate s -> inj (proj s) = s)
      (view_OK' : forall v, proj (inj v) = v)
      (View_Predicate_OK : forall s, Source_Predicate s -> View_Predicate (proj s))
      (View_Predicate_OK' : forall v, View_Predicate v -> Source_Predicate (inj v))
  : CorrectDecoder monoid Source_Predicate Source_Predicate
                   eq
                   (Projection_Format view_format proj)
                   (Compose_Decode decode_V (fun s => (inj (fst s), snd s)))
                   P
                   (Projection_Format view_format proj).
Proof.
  eapply injection_decode_correct.
  - apply projection_decode_correct; eauto.
  - simpl; intros. subst. symmetry. eauto.
  - eauto.
  - intros. apply (EquivFormat_sym (EquivFormat_Projection_Format _ _)).
    rewrite view_OK'. auto.
Qed.

Notation "format ◦ f" := (Projection_Format format f) (at level 55) : format_scope.
Notation "P ∩ format" := (Restrict_Format P format) (at level 55) : format_scope.
