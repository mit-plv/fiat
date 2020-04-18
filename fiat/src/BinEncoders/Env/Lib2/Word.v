Require Import
        Fiat.BinEncoders.Env.Common.Specs.
Require Import
        Bedrock.Word.

Section Word.
  Context {sz : nat}.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnit transformer bool}.

  Fixpoint encode_word' (s : nat) (w : word s) : B :=
    match w with
    | WO => transform_id
    | WS b s' w' => transform_push b (encode_word' s' w')
    end.

  Definition encode_word (w : word sz) (ce : CacheEncode) : B * CacheEncode :=
    (encode_word' sz w, addE ce sz).

  Fixpoint decode_word' (s : nat) (b : B) : word s * B :=
    match s with
    | O => (WO, b)
    | S s' =>
      let (c, b') := transform_pop b in
      let (w, bx) := decode_word' s' b' in
          (WS c w, bx)
    end.

  Definition decode_word (b : B) (cd : CacheDecode) : word sz * B * CacheDecode :=
    (decode_word' sz b, addD cd sz).

  Theorem Word_decode_correct :
    encode_decode_correct cache transformer (fun _ => True) encode_word decode_word.
  Proof.
    unfold encode_decode_correct, encode_word, decode_word.
    intros env env' xenv xenv' w w' bin' ext ext' Eeq _ Penc Pdec.
    inversion Penc; subst; clear Penc; inversion Pdec; subst; clear Pdec.
    generalize dependent sz.
    induction w; simpl in *.
    { intuition; inversion H0; subst; clear H0;
      [ eapply add_correct | rewrite transform_id_left ]; eauto. }
    { rewrite transform_push_step.
      rewrite transform_push_pop.
      intro. destruct (shatter_word_S w') as [? [? ?]].
      rewrite H. specialize (IHw x0).
      destruct (decode_word' n (transform (encode_word' n w) ext)) eqn: ?.
      intro. inversion H0; subst; clear H0.
      apply Eqdep_dec.inj_pair2_eq_dec in H3. subst.
      intuition eauto. eapply add_correct. eauto. subst. eauto. eapply Peano_dec.eq_nat_dec. }
  Qed.
End Word.