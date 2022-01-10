Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedEncodeMonad
        Fiat.Narcissus.BinLib.AlignedDecodeMonad
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedString.

Require Import Coq.Strings.String.

Section AlignedDelimter.

  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Variable addD_addD_plus :
    forall (cd : CacheDecode) (n m : nat), addD (addD cd n) m = addD cd (n + m).

  Variable addE_addE_plus :
    forall (ce : CacheFormat) (n m : nat), addE (addE ce n) m = addE ce (n + m).
  Variable addE_0 :
    forall (ce : CacheFormat), addE ce 0 = ce.

  Variable open : string.
  Variable close : string.

  Open Scope AlignedEncodeM_scope.

  Definition AlignedEncodeDelimiter {A}
             (encode_A : forall sz, AlignedEncodeM (S := A) sz)
             sz
    : AlignedEncodeM (S := A) sz :=
    (fun v idx _ => AlignedEncodeString sz v idx open) >> encode_A sz >>
    (fun v idx _ => AlignedEncodeString sz v idx close).

  Lemma CorrectAlignedEncoderForFormatDelimiter {A}
        format_A
        encode_A
        (encode_A_OK : CorrectAlignedEncoder format_A encode_A)
        (* These two side-conditions can be easily discharged when the cache is
        empty. *)
        (encode_A_OK1 :
           forall (a : A) (env : CacheFormat) (tenv' tenv'' : ByteString * CacheFormat),
            format_A a env ∋ tenv' ->
            Projection_Format format_string (constant close) a (snd tenv') ∋ tenv'' ->
            exists tenv3 tenv4 : _ * CacheFormat,
              projT1 encode_A_OK a env = Some tenv3
              /\ Projection_Format format_string (constant close) a (snd tenv3) ∋ tenv4)
        (encode_A_OK2 :
           forall (a : A) (env : CacheFormat) (tenv' tenv'' : ByteString * CacheFormat),
             (format_string ◦ constant open) a env ∋ tenv' ->
             format_with_term_string close format_A a (snd tenv') ∋ tenv'' ->
            exists tenv3 tenv4 : _ * CacheFormat,
              projT1 (CorrectAlignedEncoderForProjection_Format
                        (constant open) format_string
                        AlignedEncodeString
                        (CorrectAlignedEncoderForFormatString addE_addE_plus addE_0))
                     a env = Some tenv3
              /\ format_with_term_string close format_A a (snd tenv3) ∋ tenv4)
    : CorrectAlignedEncoder (format_delimiter (A:=A) open close format_A)
                            (AlignedEncodeDelimiter encode_A).
  Proof.
    repeat (eapply CorrectAlignedEncoderForThenC; [| unshelve instantiate (1:=_)]; eauto);
    eapply CorrectAlignedEncoderForProjection_Format; eapply CorrectAlignedEncoderForFormatString; eauto.
  Qed.

  Open Scope AlignedDecodeM_scope.

  Definition AlignedDecodeDelimiter {A}
             (decode_A_with_term : string -> forall {m}, AlignedDecodeM A m)
             {m}
    : AlignedDecodeM A m :=
    s <- AlignedDecodeString (length open);
    if String.eqb open s
    then decode_A_with_term close
    else ThrowAlignedDecodeM.

  Lemma AlignedDecodeDelimiterM {A C : Type}
        (decode_A_with_term : string -> DecodeM (A * _) ByteString)
        (decode_A_with_term_aligned : string -> forall {m}, AlignedDecodeM A m)
    : forall (t : A -> DecodeM (C * _) ByteString)
             (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      (forall s, DecodeMEquivAlignedDecodeM (decode_A_with_term s)
                                       (@decode_A_with_term_aligned s)) ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, bs, cd') <- decode_delimiter open close decode_A_with_term
                                                        v cd;
                          t a bs cd')
           (fun numBytes => a <- AlignedDecodeDelimiter decode_A_with_term_aligned;
                            t' a).
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    eapply AlignedDecodeStringM'.
    intros. eapply AlignedDecode_ifb; eauto.
  Qed.

  Definition AlignedDecodeWithTermStringSimple {A}
             (decode_A : forall {m}, AlignedDecodeM A m)
             (close : string)
             {m}
    : AlignedDecodeM A m :=
    a <- decode_A;
    s <- AlignedDecodeString (length close);
    if String.eqb close s
    then return a
    else ThrowAlignedDecodeM.

  Theorem AlignedDecodeWithTermStringSimpleM' {A : Type}
        (decode_A : DecodeM (A * _) ByteString)
        (decode_A_aligned : forall {m}, AlignedDecodeM A m)
    : DecodeMEquivAlignedDecodeM decode_A (@decode_A_aligned) ->
      forall close,
        DecodeMEquivAlignedDecodeM
          (decode_with_term_string_simple decode_A close)
          (fun numBytes => AlignedDecodeWithTermStringSimple
                           (@decode_A_aligned) close).
  Proof.
    intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; eauto.
    intros. eapply AlignedDecodeStringM.
    intros. eapply AlignedDecode_ifb.
    eapply Return_DecodeMEquivAlignedDecodeM.
  Qed.

  Theorem AlignedDecodeWithTermStringSimpleM {A C : Type}
        (decode_A : DecodeM (A * _) ByteString)
        (decode_A_aligned : forall {m}, AlignedDecodeM A m)
    : forall (t : A -> DecodeM (C * _) ByteString)
             (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      DecodeMEquivAlignedDecodeM decode_A (@decode_A_aligned) ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b)) ->
      forall close,
        DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, bs, cd') <- decode_with_term_string_simple
                                         decode_A close v cd;
                          t a bs cd')
           (fun numBytes => a <- AlignedDecodeWithTermStringSimple
                                 (@decode_A_aligned) close;
                            t' a).
  Proof.
    eauto using Bind_DecodeMEquivAlignedDecodeM, AlignedDecodeWithTermStringSimpleM'.
  Qed.

  Definition AlignedDecodeDelimiterSimple {A}
             (decode_A : forall {m}, AlignedDecodeM A m)
             {m}
    : AlignedDecodeM A m :=
    AlignedDecodeDelimiter (AlignedDecodeWithTermStringSimple (@decode_A)).

  Theorem AlignedDecodeDelimiterSimpleM {A C : Type}
        (decode_A : DecodeM (A * _) ByteString)
        (decode_A_aligned : forall {m}, AlignedDecodeM A m)
    : forall (t : A -> DecodeM (C * _) ByteString)
             (t' : A -> forall {numBytes}, AlignedDecodeM C numBytes),
      DecodeMEquivAlignedDecodeM decode_A (@decode_A_aligned) ->
      (forall b, DecodeMEquivAlignedDecodeM (t b) (@t' b))
      -> DecodeMEquivAlignedDecodeM
           (fun v cd => `(a, bs, cd') <- decode_delimiter_simple
                                         open close decode_A v cd;
                          t a bs cd')
           (fun numBytes => a <- AlignedDecodeDelimiterSimple
                                 (@decode_A_aligned);
                            t' a).
  Proof.
    eauto using AlignedDecodeDelimiterM, AlignedDecodeWithTermStringSimpleM'.
  Qed.

End AlignedDelimter.
