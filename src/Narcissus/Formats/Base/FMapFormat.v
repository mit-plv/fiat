Require Import
        Coq.ZArith.ZArith
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

  Definition Compose_Decode' {S' : Type}
             (decode : DecodeM S' T)
             (g : S' -> option S) (* Transformation Function *)
    : DecodeM S T  :=
    fun b env => `(s', env') <- decode b env; match g s' with Some s => Some (s, env') | None => None end.

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
      (format : FormatM V T)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate eq format decode_V P
                                    view_format)
      (View_Predicate_OK : forall s v, view s v -> Source_Predicate s -> View_Predicate v)
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
      (format : FormatM V T)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate eq format decode_V P view_format)
      (View_Predicate_OK : forall (s : S), Source_Predicate s -> View_Predicate (project s))
  : CorrectDecoder monoid Source_Predicate View_Predicate (fun s v => project s = v)
                   (Projection_Format format project) decode_V P view_format.
Proof.
  eapply Compose_decode_correct; intros; eauto.
  subst; eauto.
Qed.

Lemma constant_decode_correct {S V T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (view : S -> V -> Prop)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (format : FormatM V T)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (const_v : V)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate eq format decode_V P
                                    view_format)
      (const_v_OK : View_Predicate const_v)
  : CorrectDecoder monoid Source_Predicate View_Predicate (fun _ v' => const_v = v')
                   (Projection_Format format (constant const_v)) decode_V P view_format.
Proof.
  eapply projection_decode_correct; eauto.
Qed.

Lemma refine_Projection_Format
      {cache : Cache}
      {S S' T : Type}
      (f : S -> S')
      (format : FormatM S' T)
  : forall s env,
    refineEquiv (Projection_Format format f s env)
                (format (f s) env).
Proof.
  unfold Projection_Format, Compose_Format; intros; split.
  - intros v Comp_v.
    apply unfold_computes; eexists; intuition eauto.
  - intros v Comp_v.
    rewrite unfold_computes in Comp_v; destruct_ex; intuition eauto.
    subst; eauto.
Qed.

Lemma injection_decode_correct' {S V V' T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (inj : V -> option V')
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
      (view'_OK : forall s v, Source_Predicate s -> view s v -> exists v', inj v = Some v' /\ view' s v')
      (View'_Predicate_OK : forall v, View_Predicate v
                                 -> forall v', inj v = Some v' -> View'_Predicate v')
      (view'_format_OK : forall v env t,
          computes_to (view_format v env) t
          -> forall v', inj v = Some v' -> computes_to (view'_format v' env) t)
  : CorrectDecoder monoid Source_Predicate View'_Predicate
                   view'
                   format (Compose_Decode' decode_V (fun s => match inj (fst s) with
                                                           | Some s' => Some (s', snd s)
                                                           | None => None
                                                           end))
                   P view'_format.
Proof.
  unfold CorrectDecoder, Projection_Format, Compose_Decode'; split; intros.
  { apply proj1 in decode_V_OK; eapply decode_V_OK with (ext := ext) in H1; eauto.
    destruct_ex; intuition; subst; eauto.
    destruct (view'_OK s x); eauto. intuition.
    eexists _, _; intuition eauto; rewrite H2; simpl; eauto.
    rewrite H7; auto.
  }
  { destruct (decode_V t env') as [ [ [? ?] ?] |] eqn: ? ;
      simpl in *; try discriminate; destruct inj eqn:?; try discriminate; injections.
    apply proj2 in decode_V_OK;
      eapply decode_V_OK in Heqo; eauto.
    intuition; destruct_ex; split_and; eexists _, _; intuition eauto.
  }
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
  eapply (injection_decode_correct' (fun v => Some (inj v)));
    intuition eauto; injections; intuition eauto.
Qed.

Lemma bijection_decode_correct' {S V T}
      {cache : Cache}
      {P : CacheDecode -> Prop}
      {monoid : Monoid T}
      (proj : S -> V)
      (inj : V -> option S)
      (Source_Predicate : S -> Prop)
      (View_Predicate : V -> Prop)
      (view_format : FormatM V T)
      (decode_V : DecodeM (V * T) T)
      (decode_V_OK : CorrectDecoder monoid View_Predicate View_Predicate
                                    eq view_format decode_V P view_format)
      (view_OK : forall s, Source_Predicate s -> inj (proj s) = Some s)
      (view_OK' : forall v s, inj v = Some s -> proj s = v)
      (View_Predicate_OK : forall s, Source_Predicate s -> View_Predicate (proj s))
      (View_Predicate_OK' : forall v s, View_Predicate v -> inj v = Some s -> Source_Predicate s)
  : CorrectDecoder monoid Source_Predicate Source_Predicate
                   eq
                   (Projection_Format view_format proj)
                   (Compose_Decode' decode_V (fun s => match inj (fst s) with
                                                    | Some s' => Some (s', snd s)
                                                    | None => None
                                                    end))
                   P
                   (Projection_Format view_format proj).
Proof.
  eapply injection_decode_correct'.
  - apply projection_decode_correct; eauto.
  - simpl; intros. subst. eexists. intuition eauto.
  - eauto.
  - intros. apply (EquivFormat_sym (EquivFormat_Projection_Format _ _)).
    erewrite view_OK'; eauto.
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
  eapply (bijection_decode_correct' _ (fun v => Some (inj v)));
    intuition eauto; injections; f_equal; intuition eauto.
Qed.

(* Do we have something similar already? *)
Ltac derive_decoder_equiv :=
  unfold flip, pointwise_relation,
  Compose_Decode, Compose_Decode', DecodeBindOpt2, DecodeBindOpt, BindOpt;
  intros; try reflexivity;
  let tac x := (destruct x eqn:?; cbn; destruct_pairs; intuition eauto) in
  repeat match goal with
         | |- context[If_Opt_Then_Else ?x _ _] => tac x
         | |- context[If_Then_Else ?x _ _] => tac x
         | |- context[if ?x then _ else _] => tac x
         end.

Ltac _apply_bijection_rule tac :=
    match goal with
    | |- CorrectDecoder _ _ _ _ ?f ?d _ ?f =>
      try unfold f; try unfold d
    end;
    match goal with
    | |- CorrectDecoder _ _ _ _ ?f _ _ ?f =>
      match f with
      | Projection_Format _ _ => idtac
      | _ => eapply format_decode_correct_EquivFormatAndView;
            [solve [apply EquivFormat_sym; apply EquivFormat_Projection_Format] |]
      end;
        tac ||
            (eapply format_decode_correct_EquivDecoder;
             [| tac]; cycle 1)
    end.

Ltac apply_bijection_rule :=
  _apply_bijection_rule ltac:(eapply bijection_decode_correct).

Tactic Notation "apply_bijection_rule" "with" uconstr(t) :=
  _apply_bijection_rule ltac:(eapply bijection_decode_correct with (inj:=t)).

Ltac apply_bijection_rule' :=
  _apply_bijection_rule ltac:(eapply bijection_decode_correct').

Tactic Notation "apply_bijection_rule'" "with" uconstr(t) :=
  _apply_bijection_rule ltac:(eapply bijection_decode_correct' with (inj:=t)).

Notation "format ◦ f" := (Projection_Format format f) (at level 55) : format_scope.
Notation "P ∩ format" := (Restrict_Format P format) (at level 55) : format_scope.
