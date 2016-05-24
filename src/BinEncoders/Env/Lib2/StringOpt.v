Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.AsciiOpt.
Require Import
        Bedrock.Word
        Coq.Strings.Ascii
        Coq.Strings.String.

Section String.
  (* this has an exact idential structure to _FixList_ *)
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Fixpoint encode_string (xs : string) (ce : CacheEncode) : B * CacheEncode :=
    match xs with
    | EmptyString => (transform_id, ce)
    | String x xs' => let (b1, env1) := encode_ascii x ce in
                      let (b2, env2) := encode_string xs' env1 in
                          (transform b1 b2, env2)
    end.

  Fixpoint decode_string (s : nat) (b : B) (cd : CacheDecode) : option (string * B * CacheDecode) :=
    match s with
    | O => Some (EmptyString, b, cd)
    | S s' => `(x, b1, e1) <- decode_ascii b cd;
              `(xs, b2, e2) <- decode_string s' b1 e1;
              Some (String x xs, b2, e2)
    end.

  Local Opaque encode_ascii.
  Theorem String_decode_correct :
    forall sz,
      encode_decode_correct_f
        cache transformer
        (fun ls => length ls = sz)
        encode_string (decode_string sz).
  Proof.
    intros ? env env' xenv l l' ext Eeq Ppred Penc.
    subst.
    generalize dependent env.
    revert env' xenv l'.
    induction l.
    { intros.
      inversion Penc; subst; clear Penc.
      rewrite transform_id_left; eexists; intuition eauto.  }
    { intros.
      simpl in *.
      destruct (encode_ascii a env) eqn: ?.
      destruct (encode_string l c) eqn: ?.
      injection Penc; intros; subst.
      destruct (Ascii_decode_correct _ _ _ _ _ (transform b0 ext) Eeq I Heqp) as [? [? ?] ].
      rewrite <- transform_assoc, H; simpl.
      destruct (IHl _ _ _ _ H0 Heqp0) as [? [? ?] ].
      rewrite H1; simpl; eexists; eauto.
    }
  Qed.
End String.
