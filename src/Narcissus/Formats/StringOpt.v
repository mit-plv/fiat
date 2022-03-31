Require Import
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Formats.AsciiOpt.
Require Import
        Bedrock.Word
        Coq.Arith.Arith
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
  Context {monoidfix : QueueMonoidOptFix monoidUnit}.

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
        rewrite mempty_left; eexists _, _; intuition eauto.
        simpl; eauto.
      }
      { intros.
        simpl in *.
        unfold Bind2 in *; computes_to_inv; subst.
        injection Penc''; intros; subst.
        destruct v; destruct v0.
        destruct (proj1 (Ascii_decode_correct P_OK) _ _ _ _ _ (mappend b0 ext) env_OK Eeq I Penc) as [? [? [? xenv_OK] ] ].
      simpl. rewrite <- mappend_assoc, H; simpl.
      split_and; subst.
      destruct (IHl _ _ _ H4 _ H1 Penc') as [? [? ?] ].
      split_and; unfold id in *.
      rewrite H3; simpl; eexists _, _;
        subst; intuition eauto.
      simpl; unfold Bind2; eauto.
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
    : option (string * B * CacheDecode) :=
    Nat.iter (bin_measure b / ascii_B_measure)
             (fun rec b cd =>
                `(a, b1, e1) <- decode_ascii b cd;
                If ascii_dec a term_char Then
                  Some (EmptyString, b1, e1)
                Else
                  (`(xs, b2, e2) <- rec b1 e1;
                   Some (String a xs, b2, e2)))
             (fun _ _ => None)
             b cd.

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
        pose proof H1.
        apply format_ascii_measure in H1.
        rewrite mappend_measure, H1.
        rewrite ascii_B_measure_div_add.
        eexists _, _. simpl.
        rewrite H0; simpl.
        subst; destruct (ascii_dec x x); simpl; try congruence.
        intuition eauto.
        unfold format_string_with_term_char; simpl; unfold Bind2;
          repeat computes_to_econstructor; eauto.
        simpl;rewrite mempty_right; eauto.
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
      pose proof H3.
      apply format_ascii_measure in H3.
      rewrite <- mappend_assoc.
      rewrite mappend_measure. rewrite H3.
      rewrite ascii_B_measure_div_add.
      eexists _, _. simpl.
      rewrite H; simpl.
      destruct (ascii_dec x term_char); simpl.
      - elimtype False.
        subst; eapply (Ppred "")%string; simpl; reflexivity.
      - intuition.
        unfold decode_string_with_term_char in H1.
        rewrite H1; simpl; subst; eauto.
        unfold format_string_with_term_char; simpl; unfold Bind2;
          computes_to_econstructor; eauto.
        subst; computes_to_econstructor; eauto.
        subst; eauto.
        eauto.
      - unfold id in *; unfold not; intros; eapply (Ppred (String a s1) s2); simpl; congruence.
      - intuition eauto.
      - intuition eauto.
      }
    }
    { unfold decode_string_with_term_char, format_string_with_term_char;
        intros env env' xenv' data bin;
        revert env env' xenv' data.
      remember (bin_measure bin / ascii_B_measure).
      revert dependent bin.
      induction n; intros. easy.
      simpl in H1.
      apply DecodeBindOpt2_inv in H1;
        destruct H1 as [? [? [? [? ?] ] ] ]; injections; subst.
      eapply (proj2 (Ascii_decode_correct P_OK)) in H1; eauto;
        destruct H1 as [? [? ?] ]; destruct_ex; destruct_conjs.
      destruct (ascii_dec x term_char) eqn: ?; simpl in H2.
      + injections.
        intuition; subst.
        eexists _, _; intuition.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        simpl; rewrite mempty_right; eauto.
        destruct s1; simpl in *; discriminate.
        eauto.
      + symmetry in H2; apply DecodeBindOpt2_inv in H2;
          destruct H2 as [? [? [? [? ?] ] ] ]; injections; subst.
        eapply IHn in H2; intuition.
        destruct_ex; intuition; subst; eauto.
        eexists _, _; intuition eauto.
        simpl.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        simpl; rewrite mappend_assoc; eauto.
        unfold id in *; destruct s1; simpl in *; injections; intros; congruence.
        2: eauto.
        eapply format_ascii_measure in H3.
        rewrite mappend_measure in Heqn.
        rewrite H3 in Heqn.
        rewrite ascii_B_measure_div_add in Heqn.
        lia.
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
    induction len; simpl; intros; try lia.
    destruct (decode_ascii b3 cd0) as [ [ [? ?] ?] | ] eqn: ? ;
      simpl in *; try discriminate.
    eapply ascii_decode_lt in Heqo.
    destruct (decode_string len b c) as [ [ [? ?] ?] | ] eqn: ? ;
      simpl in *; try discriminate.
    injections.
    inversion lt_len; subst; simpl in *.
    - injections; eauto.
    - eapply IHlen in Heqo0; eauto; unfold lt_B in *; lia.
  Qed.

End String.
