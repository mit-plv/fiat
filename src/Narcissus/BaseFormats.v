Require Import
        Fiat.Narcissus.Common.Specs.

Require Export
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.StrictTerminalFormat
        Fiat.Narcissus.Formats.Base.LaxTerminalFormat
        Fiat.Narcissus.Formats.Base.FixFormat
        Fiat.Narcissus.Formats.Base.EnqueueFormat
        Fiat.Narcissus.Formats.Base.UnionFormat.

(* Aliases of Correct Decoder for deriving partial views of data. *)
Definition CorrectRefinedDecoder
           {S T : Type}
           {store : Cache}
           {V : Type}
           (monoid : Monoid T)
           (Source_Predicate : S -> Prop)
           (View_Predicate : V -> Prop)
           (view : S -> V -> Prop)
           (format subformat : FormatM S T)
           (decode : T -> CacheDecode -> option (V * T * CacheDecode))
           (decode_inv : CacheDecode -> Prop)
           (view_format : V -> CacheFormat -> Comp (T * CacheFormat)) :=
  CorrectDecoder monoid Source_Predicate View_Predicate view
                 subformat decode decode_inv
                 (fun v env t =>
                    view_format v env t
                    /\ forall s,
                      Source_Predicate s ->
                        subformat s env ∋ t
                        -> view s v).
Definition Prefix_Format
           {S T : Type}
           {store : Cache}
           (monoid : Monoid T)
           (format subformat : FormatM S T)
  := forall s t env env',
    format s env ∋ (t, env') ->
    exists t1 t2 env'',
      t = mappend t1 t2
      /\ subformat s env ∋ (t1, env'').

(*Lemma  CorrectRefinedDecoder_decode_partial
       {S T : Type}
       {store : Cache}
       {V : Type}
       (monoid' : Monoid T)
       (Source_Predicate : S -> Prop)
       (View_Predicate : V -> Prop)
       (view : S -> V -> Prop)
       (format subformat : FormatM S T)
       (decode : T -> CacheDecode -> option (V * T * CacheDecode))
       (decode_inv : CacheDecode -> Prop)
       (view_format : V -> CacheFormat -> Comp (T * CacheFormat))
  : CorrectRefinedDecoder monoid' Source_Predicate View_Predicate view
                          format subformat decode decode_inv view_format
    -> forall s t env env',
      format s env ∋ (t, env') ->
      exists t1 t2 env'',
        t = mappend t1 t2 /\
        subformat s env ∋ (t1, env'').
Proof.
  intro.
  eapply H; eauto.
  (* apply proj2 in H. *)
  (* eapply H. *)
  (* eapply H in H0. *)

  (* intros [? [? ?] ] * ?. *)
  (* eapply H0 in H1. *)
  (* unfold sequence_Format, ComposeOpt.compose, Bind2 in H1. *)
  (* computes_to_inv; destruct v; destruct v0; simpl in *; eauto. *)
  (* injections. *)
  (* eexists _, _, _; intuition eauto. *)
Qed. *)

Lemma CorrectRefinedDecoder_decode_impl
       {S T : Type}
       {store : Cache}
       (monoid' : Monoid T)
       (Source_Predicate : S -> Prop)
       (format : FormatM S T)
       (decode : T -> CacheDecode -> option (S * T * CacheDecode))
       (decode_inv : CacheDecode -> Prop)
  : CorrectRefinedDecoder monoid' Source_Predicate Source_Predicate eq
                          format format decode decode_inv format
    -> CorrectDecoder monoid' Source_Predicate Source_Predicate eq
                      format decode decode_inv format.
Proof.
  intros.
  eapply weaken_view_pred.
  intros; subst; eauto.
  2: apply H.
  intros.
  simpl in H1; intuition eauto.
Qed.

Add Parametric Morphism
    S T V
    (cache : Cache)
    (monoid : Monoid T)
    (Source_Predicate : S -> Prop)
    (View_Predicate : V -> Prop)
    (view : S -> V -> Prop)
    (decode : DecodeM (V * T) T)
    (decode_inv : CacheDecode -> Prop)
    (subformat : FormatM S T)
    (view_format : FormatM V T)
  : (fun format =>
       @CorrectRefinedDecoder S T cache V monoid Source_Predicate View_Predicate
                       view format subformat decode decode_inv view_format)
    with signature (EquivFormat --> impl)
      as format_decode_refined_correct_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation; intros.
  - unfold CorrectRefinedDecoder in *.
    apply H0.
Qed.

Add Parametric Morphism
    {S T : Type}
    {cache : Cache}
    (monoid : Monoid T)
  : (fun format subformat =>
       @Prefix_Format S T cache monoid format subformat)
    with signature (EquivFormat --> EquivFormat --> impl)
      as prefix_format_refineEquiv.
Proof.
  unfold EquivFormat, impl, pointwise_relation; unfold Prefix_Format; intros.
  edestruct H1. apply H. eauto. destruct_conjs.
  eexists _, _, _. intuition eauto. apply H0. eauto.
Qed.