Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence.
Require Import
        Coq.Strings.String.

Section Delimiter.
  Context {A : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  (* [open] and [close] will probably be formats in the future to support XML
  tag with attributes and whitespaces. *)
  Variable open : string.
  Variable close : string.

  Variable format_A : A -> CacheFormat -> Comp (T * CacheFormat).
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_cache_OK : cache_inv_Property A_cache_inv
                                           (fun P => forall b cd, P cd -> P (addD cd b)).

  Definition format_with_term (close : string) : FormatM A T :=
    format_A ++ format_string ◦ (constant close).

  Definition format_delimiter : FormatM A T :=
    format_string ◦ (constant open) ++ format_with_term close.

  (* TODO: it is faster to take the size of [open]. *)
  Definition decode_delimiter
             (decode_with_term :
               string -> T -> CacheDecode -> option (A * T * CacheDecode))
             (b : T) (cd : CacheDecode)
    : option (A * T * CacheDecode) :=
    `(s, b1, e1) <- decode_string (length open) b cd;
    if String.eqb open s
    then decode_with_term close b1 e1
    else None.

  Theorem delimiter_decode_correct
          (decode_A_with_term
            : string -> T -> CacheDecode -> option (A * T * CacheDecode))
          (A_predicate : string -> A -> Prop)
    : CorrectDecoder monoid (A_predicate close) (A_predicate close)
                     eq (format_with_term close)
                     (decode_A_with_term close)
                     A_cache_inv
                     (format_with_term close) ->
      CorrectDecoder monoid
                     (A_predicate close)
                     (A_predicate close)
                     eq
                     format_delimiter
                     (decode_delimiter decode_A_with_term)
                     A_cache_inv
                     format_delimiter.
  Proof.
    intros decode_A_OK.
    eapply format_decode_correct_EquivDecoder_Proper; cycle 1.
    - unfold format_delimiter.
      eapply format_decode_correct_refineEquiv; unfold flip.

      apply EquivFormat_UnderSequence.
      eapply EquivFormat_trans.
      apply EquivFormat_compose_id.
      apply EquivFormat_sym.
      apply sequence_mempty'.

      eapply format_sequence_correct; cycle 1; intros; eauto.
      eapply String_decode_correct; eauto. simpl; reflexivity.
      eapply format_sequence_correct; intros; eauto. intuition eauto.

      eapply CorrectDecoderEmpty. intuition eauto.

      unfold IsProj.
      instantiate (1:=(String.eqb _ _)).
      match goal with
      | |- context [String.eqb ?s ?s'] => destruct (String.eqb_spec s s')
      end; simpl; solve [intuition eauto].

      repeat instantiate (1:=constant True); split; eauto.

    - intros t cd.
      unfold sequence_Decode.
      unfold decode_delimiter.
      eapply DecodeBindOpt2_under_bind.
      intros.
      destruct String.eqb; subst; simpl;
        destruct decode_A_with_term; destruct_conjs; reflexivity.
  Qed.


  Variable decode_A : T -> CacheDecode -> option (A * T * CacheDecode).
  Variable A_predicate : A -> Prop.
  Variable decode_A_OK : CorrectDecoder monoid A_predicate A_predicate
                                        eq format_A
                                        decode_A
                                        A_cache_inv
                                        format_A.

  (* TODO: again, we should take the size of [close]. *)
  Definition decode_with_term_simple (close : string)
             (b : T) (cd : CacheDecode)
    : option (A * T * CacheDecode) :=
    `(a, b1, e1) <- decode_A b cd;
    `(s, b2, e2) <- decode_string (length close) b1 e1;
    if String.eqb close s
    then Some (a, b2, e2)
    else None.

  Theorem decode_with_term_simple_correct
    : CorrectDecoder monoid A_predicate A_predicate
                     eq (format_with_term close)
                     (decode_with_term_simple close)
                     A_cache_inv
                     (format_with_term close).
  Proof.
    eapply format_decode_correct_EquivDecoder_Proper; cycle 1.
    - unfold format_with_term.
      eapply format_decode_correct_refineEquiv; unfold flip.

      apply EquivFormat_UnderSequence'.
      apply EquivFormat_compose_id.
      apply EquivFormat_sym.
      apply sequence_mempty'.

      eapply format_sequence_correct; cycle 1; intros; eauto.
      eapply format_sequence_correct; intros; eauto. intuition eauto.
      eapply String_decode_correct; eauto. simpl; reflexivity.

      eapply CorrectDecoderEmpty. intuition eauto.

      unfold IsProj.
      instantiate (1:=(String.eqb _ _)).
      match goal with
      | |- context [String.eqb ?s ?s'] => destruct (String.eqb_spec s s')
      end; simpl; solve [intuition eauto].

      repeat instantiate (1:=constant True); split; eauto.

    - intros t cd.
      unfold sequence_Decode.
      unfold decode_with_term_simple.
      eapply DecodeBindOpt2_under_bind. intros.
      eapply DecodeBindOpt2_under_bind. intros.
      destruct String.eqb; subst; simpl; reflexivity.
  Qed.

  Definition decode_delimiter_simple :=
    decode_delimiter decode_with_term_simple.

  Corollary delimiter_decode_simple_correct
    : CorrectDecoder monoid
                     A_predicate
                     A_predicate
                     eq
                     format_delimiter
                     decode_delimiter_simple A_cache_inv
                     format_delimiter.
  Proof.
    eapply delimiter_decode_correct with (A_predicate := (fun _ => A_predicate)).
    eapply decode_with_term_simple_correct.
  Qed.

End Delimiter.
