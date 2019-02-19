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
        rewrite mempty_left; eexists _, _; intuition eauto.  }
      { intros.
        simpl in *.
        unfold Bind2 in *; computes_to_inv; subst.
        injection Penc''; intros; subst.
        destruct v; destruct v0.
        destruct (proj1 (Ascii_decode_correct P_OK) _ _ _ _ _ (mappend b0 ext) env_OK Eeq I Penc) as [? [? [? xenv_OK] ] ].
      simpl. rewrite <- mappend_assoc, H; simpl.
      split_and; subst.
      destruct (IHl _ _ _ H3 _ H2 Penc') as [? [? ?] ].
      split_and; unfold id in *.
      rewrite H1; simpl; eexists _, _;
        subst; intuition eauto.
      }
    }
    { induction sz; simpl; intros.
      { simpl; injections; repeat eexists; simpl; eauto using mempty_left. }
      { destruct (decode_ascii t env') as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate.
        destruct (decode_string sz b c) as [ [ [? ?] ?] | ] eqn: ? ;
          simpl in *; try discriminate; injections.
        eapply (proj2 (Ascii_decode_correct P_OK)) in Heqo; eauto;
          destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst;
            eapply IHsz in Heqo0; eauto; destruct Heqo0 as [? [? ?] ];
              destruct_ex; intuition; subst.
        unfold id in *; simpl.
        eexists _, _; simpl; intuition eauto.
        simpl; computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        rewrite mappend_assoc; reflexivity.
      }
    }
  Qed.

  Definition decode_string_with_term_char
           (term_char : Ascii.ascii)
           (b : B) (cd : CacheDecode)
    : option (string * B * CacheDecode).
    refine (Fix well_founded_lt_b
           (fun _ => CacheDecode -> option (string * B * CacheDecode))
      (fun b rec cd =>
         (`(a, b1, e1) <- Decode_w_Measure_lt decode_ascii b cd _;
      If ascii_dec a term_char Then
        Some (EmptyString, proj1_sig b1, e1)
      Else
      (`(xs, b2, e2) <- rec _ (proj2_sig b1) e1;
      Some (String a xs, b2, e2)))) b cd).
    exact ascii_decode_lt.
  Defined.

  Definition format_string_with_term_char
             (term_char : Ascii.ascii)
             (xs : string) (ce : CacheFormat)
    : Comp (B * CacheFormat) :=
    format_string (xs ++ (String term_char EmptyString)) ce.

  Theorem String_decode_with_term_char_correct
          {P : CacheDecode -> Prop}
    : forall term_char (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
      CorrectDecoder
        monoid
        (fun s => forall s1 s2, s <> s1 ++ String term_char s2)%string
        (fun s => forall s1 s2, s <> s1 ++ String term_char s2)%string
        eq
        (format_string_with_term_char term_char)
        (decode_string_with_term_char term_char) P
        (format_string_with_term_char term_char).
  Proof.
    split.
    { intros env env' xenv s s' ext ? Eeq Ppred Penc.
      subst.
      generalize dependent env.
      revert env' xenv s' env_OK.
      induction s.
      { unfold id in *; intros.
        unfold format_string_with_term_char in Penc.
        unfold decode_string_with_term_char.
        simpl in Penc; unfold Bind2 in *; computes_to_inv; subst; simpl in *.
        rewrite mempty_right in Penc''; inversion Penc''; subst.
        destruct v; simpl in *.
        eapply Ascii_decode_correct in Penc; eauto.
        unfold id in *.
        destruct_ex; split_and.
        eexists _, _; rewrite Init.Wf.Fix_eq.
        eapply Decode_w_Measure_lt_eq in H0; destruct_ex.
        rewrite H0; simpl.
        subst; destruct (ascii_dec x x); simpl; try congruence.
        eauto.
        intros.        
        repeat (apply functional_extensionality; intros; f_equal).
        rewrite H2.
        eauto.
      }
      { intros.
        unfold format_string_with_term_char in Penc;
          unfold decode_string_with_term_char.
        simpl in *.
        unfold Bind2 in *; computes_to_inv; subst.
        injection Penc''; intros; subst.
        destruct v; destruct v0.
        destruct (proj1 (Ascii_decode_correct P_OK) _ _ _ _ _ (mappend b0 ext) env_OK Eeq I Penc) as [? [? [? xenv_OK] ] ].
      simpl.
      unfold format_string_with_term_char in IHs.
      simpl in Penc'; eapply IHs in Penc'.
      destruct Penc'; intuition.
      subst.
      destruct_ex; split_and.
      eexists _, _; rewrite Init.Wf.Fix_eq.
      eapply Decode_w_Measure_lt_eq in H; destruct_ex.
      rewrite <- mappend_assoc, H; simpl.
      destruct (ascii_dec x term_char); simpl.
      - elimtype False.
        subst; eapply (Ppred "")%string; simpl; reflexivity.
      - intuition.
        unfold decode_string_with_term_char in H1.
        rewrite H1; simpl; subst; eauto.
        subst; eauto.
        eauto.
      - intros; repeat (apply functional_extensionality; intros; f_equal).
        rewrite H5; reflexivity.
      - unfold id in *; unfold not; intros; eapply (Ppred (String a s1) s2); simpl; congruence.
      - intuition eauto.
      - intuition eauto.
      }
    }
    { unfold decode_string_with_term_char, format_string_with_term_char;
        intros env env' xenv' data bin;
        revert env env' xenv' data.
      eapply (@well_founded_induction _ _ well_founded_lt_b) with
      (a := bin); intros.
      rewrite Coq.Init.Wf.Fix_eq in H2; auto; simpl.
      apply DecodeBindOpt2_inv in H2;
        destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
      destruct (decode_ascii x env') as [ [ [? ?] ?] | ] eqn: ? .
      - destruct (Decode_w_Measure_lt_eq _ _ _ ascii_decode_lt Heqo).
        rewrite H4 in H2; injections.
        destruct (ascii_dec x0 term_char) eqn: ?; simpl in H3.
        + injections.
          eapply (proj2 (Ascii_decode_correct P_OK)) in Heqo; eauto;
            destruct Heqo as [? [? ?] ]; destruct_ex; intuition; subst.
          simpl.
          eexists _, _; intuition.
          computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
          simpl; rewrite mempty_right; eauto.
          destruct s1; simpl in *; discriminate.
          eauto.
        + eapply (proj2 (Ascii_decode_correct P_OK)) in Heqo; eauto;
            destruct Heqo as [? [? ?] ]; destruct_ex.
          symmetry in H3; apply DecodeBindOpt2_inv in H3;
            destruct H3 as [? [? [? [? ?] ] ] ]; injections; subst.
          eapply H in H3; intuition.
          destruct_ex; intuition; subst; eauto.
          eexists _, _; intuition.
          simpl.
          computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
          simpl; rewrite mappend_assoc; eauto.
          unfold id in *; destruct s1; simpl in *; injections; intros; congruence.
          simpl; eauto.
          simpl; eauto.
      - eapply Decode_w_Measure_lt_eq' in Heqo; rewrite Heqo in H2;
          discriminate.
      - intros; repeat (apply functional_extensionality; intros; f_equal).
        rewrite H3; reflexivity.
    }
  Qed.

End String.
