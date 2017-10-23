Require Import
        Fiat.BinEncoders.Env.Common.Specs
        Fiat.BinEncoders.Env.Lib2.AsciiOpt.
Require Import
        Bedrock.Word
        Coq.Strings.Ascii
        Coq.Strings.String.

Section String.
  (* this has an exact idential structure to _FixList_ *)
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {transformer : Transformer B}.
  Context {transformerUnit : QueueTransformerOpt transformer bool}.

  Fixpoint encode_string_Spec (xs : string) (ce : CacheEncode)
    : Comp (B * CacheEncode) :=
    match xs with
    | EmptyString => ret (transform_id, addE ce 0)
    | String x xs' => `(b1, env1) <- encode_ascii_Spec x ce;
                      `(b2, env2) <- encode_string_Spec xs' env1;
                      ret (transform b1 b2, env2)
    end%comp.

    Fixpoint encode_string_Impl (xs : string) (ce : CacheEncode) : B * CacheEncode :=
    match xs with
    | EmptyString => (transform_id, addE ce 0)
    | String x xs' => let (b1, env1) := encode_ascii_Impl x ce in
                      let (b2, env2) := encode_string_Impl xs' env1 in
                          (transform b1 b2, env2)
    end.

  Fixpoint decode_string (s : nat) (b : B) (cd : CacheDecode) : option (string * B * CacheDecode) :=
    match s with
    | O => Some (EmptyString, b, addD cd 0)
    | S s' => `(x, b1, e1) <- decode_ascii b cd;
              `(xs, b2, e2) <- decode_string s' b1 e1;
              Some (String x xs, b2, e2)
    end.

  Local Opaque encode_ascii_Spec.
  Local Opaque encode_ascii_Impl.

  Theorem String_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : forall b cd, P cd -> P (addD cd b))
    : forall sz,
      encode_decode_correct_f
        cache transformer
        (fun ls => length ls = sz)
        (fun _ _ => True)
        encode_string_Spec (decode_string sz) P.
  Proof.
    split.
    { intros env env' xenv l l' ext ? Eeq Ppred Ppred_rest Penc.
      subst.
      generalize dependent env.
      revert env' xenv l' env_OK.
      induction l.
      { intros.
        inversion Penc; subst; clear Penc.
        rewrite transform_id_left; eexists; intuition eauto.
        apply add_correct; eauto.
      }
      { intros.
        simpl in *.
        unfold Bind2 in *; computes_to_inv; subst.
        injection Penc''; intros; subst.
        destruct v; destruct v0.
        destruct (proj1 (Ascii_decode_correct P_OK) _ _ _ _ _ (transform b0 ext) env_OK Eeq I I Penc) as [? [? [? xenv_OK] ] ].
      simpl. rewrite <- transform_assoc, H; simpl.
      destruct (IHl _ _ _ xenv_OK _ H0 Penc') as [? [? ?] ].
      rewrite H1; simpl; eexists; eauto.
      }
    }
    { induction sz; simpl; intros.
      { injections; repeat eexists; eauto using transform_id_left.
        apply add_correct; eauto.
      }
      { destruct (decode_ascii bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_string sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 (Ascii_decode_correct P_OK)) in Heqo; eauto;
          destruct Heqo; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0;
              destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite transform_assoc; reflexivity.
      }
    }
  Qed.

  Theorem decode_string_lt
    : forall len (lt_len : lt 0 len)
             (b3 : B)
             (cd0 : CacheDecode)
             (a : string) (b' : B)
             (cd' : CacheDecode),
      decode_string len b3 cd0 = Some (a, b', cd') -> lt_B b' b3.
  Proof.
    induction len; simpl; intros; try omega.
    destruct (decode_ascii b3 cd0) as [ [ [? ?] ?] | ] eqn: ? ;
      simpl in *; try discriminate.
    eapply ascii_decode_lt in Heqo.
    destruct (decode_string len b c) as [ [ [? ?] ?] | ] eqn: ? ;
      simpl in *; try discriminate.
    injections.
    inversion lt_len; subst; simpl in *.
    - injections; eauto.
    - eapply IHlen in Heqo0; eauto; unfold lt_B in *; omega.
  Qed.

End String.
