Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.AsciiOpt.
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
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Fixpoint format_string (xs : string) (ce : CacheFormat)
    : Comp (B * CacheFormat) :=
    match xs with
    | EmptyString => ret (mempty, ce)
    | String x xs' => `(b1, env1) <- format_ascii x ce;
                      `(b2, env2) <- format_string xs' env1;
                      ret (mappend b1 b2, env2)
    end%comp.

    Fixpoint encode_string (xs : string) (ce : CacheFormat) : B * CacheFormat :=
    match xs with
    | EmptyString => (mempty, ce)
    | String x xs' => let (b1, env1) := encode_ascii x ce in
                      let (b2, env2) := encode_string xs' env1 in
                          (mappend b1 b2, env2)
    end.

  Fixpoint decode_string (s : nat) (b : B) (cd : CacheDecode) : option (string * B * CacheDecode) :=
    match s with
    | O => Some (EmptyString, b, cd)
    | S s' => `(x, b1, e1) <- decode_ascii b cd;
              `(xs, b2, e2) <- decode_string s' b1 e1;
              Some (String x xs, b2, e2)
    end.

  Local Opaque format_ascii.
  Local Opaque encode_ascii.

  Theorem String_decode_correct
          {P : CacheDecode -> Prop}
    : forall sz
             (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
      CorrectDecoder
        monoid
        (fun ls => length ls = sz)
        (fun _ _ => True)
        format_string (decode_string sz) P.
  Proof.
    split.
    { intros env env' xenv l l' ext ? Eeq Ppred Ppred_rest Penc.
      subst.
      generalize dependent env.
      revert env' xenv l' env_OK.
      induction l.
      { intros.
        inversion Penc; subst; clear Penc.
        rewrite mempty_left; eexists; intuition eauto.  }
      { intros.
        simpl in *.
        unfold Bind2 in *; computes_to_inv; subst.
        injection Penc''; intros; subst.
        destruct v; destruct v0.
        destruct (proj1 (Ascii_decode_correct P_OK) _ _ _ _ _ (mappend b0 ext) env_OK Eeq I I Penc) as [? [? [? xenv_OK] ] ].
      simpl. rewrite <- mappend_assoc, H; simpl.
      destruct (IHl _ _ _ xenv_OK _ H0 Penc') as [? [? ?] ].
      rewrite H1; simpl; eexists; eauto.
      }
    }
    { induction sz; simpl; intros.
      { injections; repeat eexists; eauto using mempty_left. }
      { destruct (decode_ascii bin env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_string sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 (Ascii_decode_correct P_OK)) in Heqo; eauto;
          destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0 as [? [? ?] ];
              destruct_ex; intuition; subst.
        simpl.
        eexists; eexists; intuition eauto.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite mappend_assoc; reflexivity.
      }
    }
  Qed.
End String.
