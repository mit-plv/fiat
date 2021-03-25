Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.AsciiOpt.
Require Import
        Bedrock.Word
        Coq.ZArith.ZArith
        Coq.Strings.Ascii
        Coq.Strings.String.

Section String.
  (* this has an exact idential structure to _FixList_ *)
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Fixpoint format_string (xs : string) (ce : CacheFormat)
    : Comp (B * CacheFormat) :=
    match xs with
    | EmptyString => ret (mempty, addE ce 0)
    | String x xs' => `(b1, env1) <- format_ascii x ce;
                      `(b2, env2) <- format_string xs' env1;
                      ret (mappend b1 b2, env2)
    end%comp.

    Fixpoint encode_string (xs : string) (ce : CacheFormat) : B * CacheFormat :=
    match xs with
    | EmptyString => (mempty, addE ce 0)
    | String x xs' => let (b1, env1) := encode_ascii x ce in
                      let (b2, env2) := encode_string xs' env1 in
                          (mappend b1 b2, env2)
    end.

  Fixpoint decode_string (s : nat) (b : B) (cd : CacheDecode) : option (string * B * CacheDecode) :=
    match s with
    | O => Some (EmptyString, b, addD cd 0)
    | S s' => `(x, b1, e1) <- decode_ascii b cd;
              `(xs, b2, e2) <- decode_string s' b1 e1;
              Some (String x xs, b2, e2)
    end.

  Local Opaque format_ascii.
  Local Opaque encode_ascii.

  Theorem String_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : forall b cd, P cd -> P (addD cd b))
    : forall sz,
      CorrectDecoder
        monoid
        (fun ls => length ls = sz)
        (fun ls => length ls = sz)
        eq
        format_string (decode_string sz) P
        format_string.
  Proof.
    split.
    { intros env env' xenv l l' ext ? Eeq Ppred Penc.
      subst.
      generalize dependent env.
      revert env' xenv l' env_OK.
      induction l.
      { intros.
        inversion Penc; subst; clear Penc.
        rewrite mempty_left; eexists _, _; intuition eauto.
        simpl; eauto.
        apply add_correct; eauto.
      }
      { intros.
        simpl in *.
        unfold Bind2 in *; computes_to_inv; subst.
        injection Penc''; intros; subst.
        destruct v; destruct v0.
        destruct (proj1 (Ascii_decode_correct P_OK) _ _ _ _ _ (mappend b0 ext) env_OK Eeq I Penc) as [? [? [? xenv_OK] ] ].
      simpl. rewrite <- mappend_assoc, H; simpl; split_and; subst.
      destruct (IHl _ _ _ H4 _ H1 Penc') as [? [? ?] ].
      split_and; subst.
      setoid_rewrite H3; simpl; eexists _, _;
        intuition eauto.
      simpl; unfold Bind2; eauto.
      }
    }
    { induction sz; simpl; intros.
      { split; eauto;
          injections; repeat eexists; simpl; eauto using mempty_left.
        apply add_correct; eauto.
      }
      { destruct (decode_ascii t env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_string sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 (Ascii_decode_correct P_OK)) in Heqo; eauto;
          destruct Heqo; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0;
              destruct_ex; intuition; subst.
        simpl.
        eexists _, _; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite mappend_assoc; reflexivity.
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
