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

  Definition encode_word_Impl (w : word sz) (ce : CacheEncode) : B * CacheEncode := (encode_word' sz w, addE ce sz).

  Definition encode_word_Spec (w : word sz) (ce : CacheEncode) : Comp (B * CacheEncode) :=
    ret (encode_word' sz w, addE ce sz).

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
    encode_decode_correct_f cache transformer (fun _ => True) encode_word_Spec decode_word.
  Proof.
    unfold encode_decode_correct_f, encode_word_Spec, decode_word; split.
    - intros env env' xenv w w' ext Eeq _ Penc.
      computes_to_inv; injections.
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
    - intros.
      destruct (decode_word' sz bin)
        as [ [? ?] | ] eqn: ?; simpl in *; try discriminate.
      injections.
      generalize dependent bin.
      induction data; simpl in *.
      { intros; computes_to_inv; intros; injection Heqo; clear Heqo;
        intros; subst.
        repeat eexists. eauto; try rewrite !transform_id_left;
        eauto using add_correct.
        apply add_correct; eauto.
      }
      { intros.
        destruct (transform_pop_opt bin) as [ [? ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_word' n b1) as [ [? ? ] | ] eqn: ? ;
          simpl in *; try discriminate.
        injection Heqo; intros; subst.
        apply Eqdep_dec.inj_pair2_eq_dec in H1; subst.
        eapply IHdata in Heqo1.
        destruct_ex; intuition; subst.
        computes_to_inv; injections.
        eexists; eexists; repeat split.
        setoid_rewrite transform_push_step_opt.
        eapply transform_pop_opt_inj; eauto.
        rewrite transform_push_pop_opt; reflexivity.
        apply add_correct; eauto.
        eapply Peano_dec.eq_nat_dec.
      }
  Qed.
End Word.
