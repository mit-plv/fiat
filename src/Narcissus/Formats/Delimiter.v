Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence.

Section Delimiter.
  Context {A : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Context {cache_inv : CacheDecode -> Prop}.

  Variable format_open : FormatM unit T.
  Variable decode_open : DecodeM (unit * T) T.
  Context {open_cache_inv : (CacheDecode -> Prop) -> Prop}.

  Variable format_close : FormatM unit T.
  Variable decode_close : DecodeM (unit * T) T.
  Context {close_cache_inv : (CacheDecode -> Prop) -> Prop}.

  Variable format_A : FormatM A T.
  Variable decode_A : DecodeM (A * T) T.
  Variable A_predicate : A -> Prop.
  Context {A_cache_inv : (CacheDecode -> Prop) -> Prop}.

  Definition format_with_term : FormatM A T :=
    format_A ++ format_close ◦ (constant tt).

  Definition format_delimiter : FormatM A T :=
    format_open ◦ (constant tt) ++ format_with_term.

  Definition decode_delimiter
    (decode_with_term : DecodeM (A * T) T) :=
    sequence_Decode decode_open (fun _ => decode_with_term).

  Variable decode_open_OK :
    cache_inv_Property cache_inv open_cache_inv ->
    CorrectDecoder monoid (fun _ => True) (fun _ => True)
        eq format_open
        decode_open
        cache_inv
        format_open.

  Variable decode_close_OK :
    cache_inv_Property cache_inv close_cache_inv ->
    CorrectDecoder monoid (fun _ => True) (fun _ => True)
        eq format_close
        decode_close
        cache_inv
        format_close.

  Variable decode_A_OK :
    cache_inv_Property cache_inv A_cache_inv ->
    CorrectDecoder monoid
      A_predicate
      A_predicate
      eq format_A
      decode_A
      cache_inv
      format_A.

  (* Just a variant of [format_sequence_correct]. Some parts can be generalized,
  e.g., cache invariant. But this seems good enough for now. *)
  Definition delimiter_decode_correct
    {with_term_cache_inv : (CacheDecode -> Prop) -> Prop}
    (decode_with_term : DecodeM (A * T) T)
    (cache_inv_pf : cache_inv_Property cache_inv
                      (fun P => open_cache_inv P /\ with_term_cache_inv P))
    : (cache_inv_Property cache_inv with_term_cache_inv ->
       CorrectDecoder
         monoid A_predicate A_predicate eq
         format_with_term decode_with_term cache_inv
         format_with_term) ->
      CorrectDecoder
        monoid A_predicate A_predicate eq
        format_delimiter (decode_delimiter decode_with_term) cache_inv
        format_delimiter.
  Proof.
    intros H.
    eapply format_sequence_correct; intros; intuition eauto.
    destruct v1.
    eapply weaken_source_pred; cycle -1.
    eapply strengthen_view_pred; cycle -1.
    eauto.
    all : repeat (hnf; intros; intuition).
  Qed.

  (* If [format_A] can be decoded individually. *)
  Definition decode_with_term_simple (b : T) (cd : CacheDecode)
    : option (A * T * CacheDecode) :=
    `(a, b1, e1) <- decode_A b cd;
    `(_, b2, e2) <- decode_close b1 e1;
    Some (a, b2, e2).

  Lemma decode_with_term_simple_correct
    (cache_inv_pf : cache_inv_Property cache_inv
                      (fun P => A_cache_inv P /\ close_cache_inv P))
    : CorrectDecoder
        monoid A_predicate A_predicate eq
        format_with_term
        decode_with_term_simple
        cache_inv
        format_with_term.
  Proof.
    unfold format_with_term, decode_with_term_simple.
    eapply format_decode_correct_EquivDecoder_Proper; cycle 1.
    - eapply format_decode_correct_refineEquiv; unfold flip.

      apply EquivFormat_UnderSequence'.
      apply EquivFormat_compose_id.
      apply EquivFormat_sym.
      apply sequence_mempty'.

      eapply format_sequence_correct; cycle 1; intros; intuition eauto.
      eapply format_sequence_correct; intros; intuition eauto.
      eapply CorrectDecoderEmpty. intuition eauto.
      instantiate (1:=true).
      unfold IsProj. simpl. intuition eauto. destruct v0; eauto.

    - reflexivity.
  Qed.

  Definition decode_delimiter_simple :=
    decode_delimiter decode_with_term_simple.

  Corollary delimiter_decode_simple_correct
    (cache_inv_pf : cache_inv_Property cache_inv
                      (fun P => open_cache_inv P /\
                                A_cache_inv P /\
                                close_cache_inv P))
    : CorrectDecoder
        monoid
        A_predicate
        A_predicate
        eq
        format_delimiter
        decode_delimiter_simple cache_inv
        format_delimiter.
  Proof.
    intros.
    eapply delimiter_decode_correct.
    apply cache_inv_pf.
    intros.
    eapply decode_with_term_simple_correct; eauto.
  Qed.

End Delimiter.
