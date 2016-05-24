Require Import
        Fiat.Common
        Fiat.Computation.Notations
        Fiat.BinEncoders.Env.Common.Specs.

Require Import
        Bedrock.Word.

Unset Implicit Arguments.
Section Word.
  Context {sz : nat}.

  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : TransformerUnitOpt transformer bool}.

  Fixpoint encode_word' (s : nat) (w : word s) : B :=
    match w with
    | WO => transform_id
    | WS b s' w' => transform_push_opt b (@encode_word' s' w')
    end.

  Definition encode_word (w : word sz) (ce : CacheEncode) : B * CacheEncode :=
    (encode_word' sz w, addE ce sz).

  Fixpoint decode_word' (s : nat) (b : B) : option (word s * B) :=
    match s with
    | O => Some (WO, b)
    | S s' =>
      `(c, b') <- transform_pop_opt b;
      `(w, bx) <- decode_word' s' b';
       Some (WS c w, bx)
    end.

  Definition decode_word (b : B) (cd : CacheDecode) : option (word sz * B * CacheDecode) :=
    Ifopt decode_word' sz b as decoded Then Some (decoded, addD cd sz) Else None.

  Theorem Word_decode_correct :
    encode_decode_correct_f cache transformer (fun _ => True) encode_word decode_word.
  Proof.
    unfold encode_decode_correct, encode_word, decode_word.
    intros env env' xenv w w' ext Eeq _ Penc.
    inversion Penc; subst; clear Penc.
    generalize dependent sz.
    induction w; simpl in *.
    { eexists; split; eauto; try rewrite !transform_id_left; 
      eauto using add_correct. }
    { rewrite transform_push_step_opt.
      rewrite transform_push_pop_opt.
      destruct_ex; intuition.
      destruct (decode_word' n (transform (encode_word' n w) ext)) as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections; eexists; split; eauto using add_correct.
      rewrite Heqo; simpl; f_equal.
    }
  Qed.
End Word.
