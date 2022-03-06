Require Import
        Bedrock.Word
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.AsciiOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence.
Require Import
        Coq.Strings.Ascii
        Coq.Strings.String.


(* Copied from stdpp. *)
Definition is_space (x : Ascii.ascii) : bool :=
  match x with
  | "009" | "010" | "011" | "012" | "013" | " " => true
  | _ => false
  end%char.

Section Lexeme.
  Context {A : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid T}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  (* Some lemmas about cache noninterference of word and ascii decoders. Should
  we move them somewhere else? *)
  Lemma decode_word_cache_nonint sz t (w : word sz) t' cd1 cd1' cd2 :
    decode_word t cd1 = Some (w, t', cd1') ->
    exists cd2', decode_word t cd2 = Some (w, t', cd2').
  Proof.
    unfold decode_word. intros.
    destruct decode_word'; simpl in *; injections; eauto.
  Qed.

  Lemma decode_ascii_cache_nonint t a t' cd1 cd1' cd2 :
    decode_ascii t cd1 = Some (a, t', cd1') ->
    exists cd2', decode_ascii t cd2 = Some (a, t', cd2').
  Proof.
    unfold decode_ascii. intros.
    destruct decode_word as [ [[??]?] |] eqn:Hd; simpl in *; injections;
      try discriminate.
    eapply decode_word_cache_nonint in Hd.
    destruct Hd as [? Hd].
    rewrite Hd.
    simpl. eauto.
  Qed.


  Definition format_space : FormatM A T :=
    Compose_Format format_string
                   (fun _ => {s : string | Forall is_space
                                                (list_ascii_of_string s) })%comp.

  (* [decode_space] is NOT a correct decoder for [format_space]. In fact, no
  decoder can be its correct decoder. *)
  Definition decode_space : T -> CacheDecode -> T * CacheDecode :=
    Fix well_founded_lt_b _
        (fun b rec cd =>
           match Decode_w_Measure_lt decode_ascii b cd ascii_decode_lt with
           | Some (a, b1, e1) =>
               if is_space a
               then rec _ (proj2_sig b1) e1
               else (b, cd)
           | None => (b, cd)
           end).

  Variable format_A : FormatM A T.
  Variable decode_A : DecodeM (A * T) T.
  Variable A_predicate : A -> Prop.
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_cache_OK : cache_inv_Property A_cache_inv
                                           (fun P => forall b cd, P cd -> P (addD cd b)).
  Variable A_decode_pf : CorrectDecoder
                           monoid
                           A_predicate
                           A_predicate
                           eq format_A decode_A A_cache_inv format_A.


  (* Unlike lexeme in most parser combinator, we format whitespaces first. *)
  Definition format_lexeme (a : A) (ce : CacheFormat) : Comp (T * CacheFormat) :=
    `(b1, _) <- format_space a ce;
    `(b2, ce') <- format_A a ce;
    ret (mappend b1 b2, ce').

  Definition decode_lexeme (b : T) (cd : CacheDecode)
    : option (A * T * CacheDecode) :=
    let (b1, _) := decode_space b cd in decode_A b1 cd.

  Ltac t_Fix_eq :=
    let Hext := fresh in
    let cd := fresh in
    intros ??? Hext; extensionality cd;
    destruct Decode_w_Measure_lt; eauto;
    destruct_conjs; simpl; rewrite Hext; eauto.

  (* This statement is similar to [CorrectDecoder], but with restriction on
  [ext]. We can certainly generalize [CorrectDecoder] the same way to, say,
  [CorrectDecoderExt] if we have more use cases like this. In that case,
  [format_space] should be a format from [unit] to [T], and [decode_space]
  should trivially return [Some] of the current result and [tt]. *)
  Lemma space_decode_correct :
    (forall env env' xenv s t ext,
        Equiv env env' ->
        A_cache_inv env' ->
        format_space s env ∋ (t, xenv) ->
        (forall a b cd cd',
            decode_ascii ext cd = Some (a, b, cd') ->
            is_space a = false) ->
        exists xenv',
          decode_space (mappend t ext) env' = (ext, xenv')
          /\ Equiv xenv xenv' /\ A_cache_inv xenv') /\
    (forall env env' xenv' s t t',
        Equiv env env' ->
        A_cache_inv env' ->
        decode_space t env' = (t', xenv') ->
        A_cache_inv xenv' /\
        exists (t'' : T) (xenv : CacheFormat),
          format_space s env ∋ (t'', xenv)
          /\ t = mappend t'' t'
          /\ Equiv xenv xenv').
  Proof.
    unfold format_space.
    split. {
      intros env env' ?? t ext ?? [s [? H]].
      rewrite unfold_computes in H.
      revert dependent env'.
      revert dependent env.
      revert dependent t.
      induction s; intros. {
        simpl in *.
        computes_to_inv.
        injections.
        repeat esplit; eauto.
        unfold decode_space.
        rewrite Init.Wf.Fix_eq by t_Fix_eq.
        rewrite mempty_left.
        destruct (decode_ascii ext env') as [ [[??]?] |] eqn:Ha.
        - assert (is_space a = false) as Hs by eauto.
          eapply Decode_w_Measure_lt_eq in Ha.
          destruct Ha as [? Ha].
          rewrite Ha. rewrite Hs. eauto.
        - rewrite Decode_w_Measure_lt_eq'; eauto.
      } {
        simpl in *. unfold Bind2 in *. computes_to_inv.
        inversion H; subst.
        destruct_conjs. simpl in *. injections.
        match goal with
        | H : format_ascii _ _ ∋ _ |- _ =>
            eapply Ascii_decode_correct in H; eauto
        end.
        destruct_ex; split_and; subst.
        match goal with
        | H : format_string _ _ ∋ _ |- _ =>
            eapply IHs in H; eauto
        end.
        destruct_ex; split_and; subst.
        repeat esplit; eauto.
        unfold decode_space.
        rewrite Init.Wf.Fix_eq by t_Fix_eq.
        rewrite <- mappend_assoc.
        match goal with
        | H : decode_ascii _ _ = Some _ |- _ =>
            let H' := fresh in
            eapply Decode_w_Measure_lt_eq in H; destruct H as [? H'];
            rewrite H'
        end.
        match goal with
        | H : context [ is_space ] |- _ => rewrite H; eauto
        end.
      }
    } {
      intros env env' ?? t ?.
      revert dependent env'.
      revert dependent env.
      eapply (well_founded_induction well_founded_lt_b) with (a:=t).
      intros x IH. intros.
      match goal with
      | H : decode_space _ _ = _ |- _ =>
          rename H into Hs
      end.
      unfold decode_space in Hs.
      rewrite Init.Wf.Fix_eq in Hs by t_Fix_eq.
      destruct (decode_ascii x env') eqn:Ha. {
        destruct_conjs.
        pose proof Ha as Ha'.
        eapply Ascii_decode_correct in Ha; eauto.
        eapply Decode_w_Measure_lt_eq in Ha'.
        destruct_conjs. subst.
        match goal with
        | H : Decode_w_Measure_lt _ _ _ _ = _ |- _ =>
            rewrite H in Hs
        end.
        destruct is_space eqn:?.
        - simpl in Hs.
          eapply IH in Hs; eauto.
          destruct_conjs. subst.
          match goal with
          | H : context [ Compose_Format ] |- _ =>
              unfold Compose_Format in H;
              rewrite unfold_computes in H;
              destruct H as [? [? H]];
              rewrite unfold_computes in H
          end.
          split; eauto.
          eexists _, _. repeat split; eauto; rewrite ?mappend_assoc; eauto.
          match goal with
          | H : format_ascii ?a _ ∋ _, H' : format_string ?s _ ∋ _ |- _ =>
              exists (String a s)
          end. split.
          computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
          rewrite unfold_computes.
          eauto using Forall.
        - injections.
          split; eauto.
          eexists _, _. repeat split; eauto; rewrite ?mempty_left; eauto.
          exists ("")%string. split.
          computes_to_econstructor; eauto.
          rewrite unfold_computes.
          eauto using Forall.
      } {
        eapply Decode_w_Measure_lt_eq' in Ha.
        rewrite Ha in Hs. injections.
        split; eauto.
        eexists _, _. repeat split; eauto; rewrite ?mempty_left; eauto.
        exists ("")%string. split.
        computes_to_econstructor; eauto.
        rewrite unfold_computes.
        eauto using Forall.
      }
    }
  Qed.

  Definition no_head_space (t : T) :=
    forall a cd t' cd',
      decode_ascii t cd = Some (a, t', cd') ->
      is_space a = false.

  Lemma decode_space_no_head_space : forall t cd t' cd',
    decode_space t cd = (t', cd') ->
    no_head_space t'.
  Proof.
    intros t.
    eapply (well_founded_induction well_founded_lt_b) with (a:=t).
    intros x IH cd ?? Hs.
    unfold decode_space in Hs.
    rewrite Init.Wf.Fix_eq in Hs by t_Fix_eq.
    destruct (decode_ascii x cd) eqn:Ha. {
      destruct_conjs.
      pose proof Ha as Ha'.
      eapply Decode_w_Measure_lt_eq in Ha.
      destruct_conjs.
      match goal with
      | H : Decode_w_Measure_lt _ _ _ _ = _ |- _ =>
          rewrite H in Hs
      end.
      destruct is_space eqn:Hi.
      - simpl in Hs.
        eapply IH in Hs; eauto.
      - injections.
        hnf. intros.
        rewrite <- Hi. f_equal.
        match goal with
        | H : decode_ascii _ _ = _ |- _ =>
            eapply decode_ascii_cache_nonint in H;
            destruct H as [? H]; rewrite Ha' in H
        end.
        injections. eauto.
    } {
      pose proof Ha as Ha'.
      eapply Decode_w_Measure_lt_eq' in Ha.
      rewrite Ha in Hs. injections.
      hnf. intros.
      match goal with
      | H : decode_ascii _ _ = _ |- _ =>
          eapply decode_ascii_cache_nonint in H;
          destruct H as [? H]; rewrite Ha' in H
      end.
      discriminate.
    }
  Qed.

  (* A source [s] of [format_A] is compatible with the lexeme combinator if none
  of its target monoid starts with whitespace. *)
  Definition lexeme_source_compatible (s : A) :=
    forall env t xenv ext,
      format_A s env ∋ (t, xenv) ->
      no_head_space (mappend t ext).

  Definition lexeme_all_source_compatible :=
    forall s, lexeme_source_compatible s.

  (* [format_A] is compatible with the lexeme combinator if all its sources are
  compatible when some of their target monoids do not start with whitespace. In
  other words, no source produces some target monoids that start with
  whitespaces and some target monoids that do not. *)
  Definition lexeme_format_compatible :=
    forall s env t xenv ext,
      A_predicate s ->
      format_A s env ∋ (t, xenv) ->
      no_head_space (mappend t ext) ->
      lexeme_source_compatible s.

  Theorem lexeme_decode_correct :
    lexeme_format_compatible ->
    CorrectDecoder monoid
                   (fun s => A_predicate s /\ lexeme_source_compatible s)
                   (fun s => A_predicate s /\ lexeme_source_compatible s)
                   eq format_lexeme decode_lexeme A_cache_inv format_lexeme.
  Proof.
    intros Hc.
    unfold format_lexeme.
    rewrite <- CorrectDecoder_equiv_CorrectDecoder_id.
    split; intros. {
      unfold Bind2 in *.
      computes_to_inv.
      destruct_conjs. simpl in *.
      injections.
      unfold decode_lexeme.
      rewrite <- mappend_assoc.
      unfold lexeme_source_compatible, no_head_space in *.
      match goal with
      | H : format_space _ _ ∋ _ |- _ =>
          eapply space_decode_correct in H; eauto;
          let H' := fresh in
          destruct H as [? [H' [_ _]]]; rewrite H'
      end.
      match goal with
      | H : format_A _ _ ∋ _ |- _ =>
          eapply A_decode_pf in H; eauto;
          let H' := fresh in
          destruct H as [? [? [H' ?]]]; rewrite H'
      end.
      destruct_conjs. subst.
      eauto.
    } {
      unfold decode_lexeme in *.
      destruct decode_space eqn:?.
      match goal with
      | H : decode_space _ _ = (?t, _) |- _ =>
          assert (no_head_space t) by eauto using decode_space_no_head_space;
          eapply space_decode_correct in H; eauto;
          destruct H; destruct_ex; destruct_conjs; subst
      end.
      match goal with
      | H : decode_A _ _ = _ |- _ =>
          eapply A_decode_pf in H; eauto;
          destruct H; destruct_ex; destruct_conjs; subst
      end.
      split; eauto.
      eexists _, _. repeat split; eauto.
      computes_to_econstructor; eauto.
      computes_to_econstructor; eauto.
      simpl.
      rewrite mappend_assoc. eauto.
    }
  Qed.

  Lemma lexeme_all_source_compatible_format_compatible :
    lexeme_all_source_compatible ->
    lexeme_format_compatible.
  Proof.
    easy.
  Qed.

  Theorem lexeme_decode_correct_all :
    lexeme_all_source_compatible ->
    CorrectDecoder monoid
                   (fun s => A_predicate s)
                   (fun s => A_predicate s)
                   eq format_lexeme decode_lexeme A_cache_inv format_lexeme.
  Proof.
    intros.
    eapply weaken_source_pred; cycle -1.
    eapply strengthen_view_pred; cycle -1.
    apply lexeme_decode_correct.
    eauto using lexeme_all_source_compatible_format_compatible.
    all : repeat (hnf; intros); destruct_conjs; eauto.
  Qed.

End Lexeme.
