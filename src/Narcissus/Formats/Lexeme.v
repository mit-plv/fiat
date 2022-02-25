Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
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
  Variable A_decode_pf : CorrectDecoder monoid A_predicate A_predicate
                                        eq format_A decode_A A_cache_inv
                                        format_A.

  (* Unlike lexeme in most parser combinator, we format whitespaces first. *)
  Definition format_lexeme : FormatM A T :=
    format_space ++ format_A.

  Definition decode_lexeme (b : T) (cd : CacheDecode)
    : option (A * T * CacheDecode) :=
    let (b1, e1) := decode_space b cd in decode_A b1 e1.

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
        rewrite Init.Wf.Fix_eq by shelve.
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
        rewrite Init.Wf.Fix_eq by shelve.
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
      rewrite Init.Wf.Fix_eq in Hs by shelve.
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

    Unshelve.

    all:
      intros ??? Hext; extensionality cd;
      destruct Decode_w_Measure_lt; eauto;
      destruct_conjs; simpl; rewrite Hext; eauto.
  Qed.

  (* [format_A] needs to produce a string that does not start with a
  whitespace. *)
  Definition format_lexeme_compatible :=
    forall s env t xenv cd a t' cd' ext,
      A_predicate s ->
      format_A s env ∋ (t, xenv) ->
      decode_ascii (mappend t ext) cd = Some (a, t', cd') ->
      is_space a = false.

  Theorem lexeme_decode_correct :
    format_lexeme_compatible ->
    CorrectDecoder monoid A_predicate A_predicate eq
                   format_lexeme decode_lexeme A_cache_inv format_lexeme.
  Proof.
    intros Hc.
    unfold format_lexeme.
    rewrite <- CorrectDecoder_equiv_CorrectDecoder_id.
    split; intros. {
      unfold sequence_Format, ComposeOpt.compose, Bind2 in *.
      computes_to_inv.
      destruct_conjs. simpl in *.
      injections.
      unfold decode_lexeme.
      rewrite <- mappend_assoc.
      match goal with
      | H : format_space _ _ ∋ _ |- _ =>
          eapply space_decode_correct in H; eauto;
          let H' := fresh in
          destruct H as [? [H' [??]]]; rewrite H'
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
      destruct decode_space eqn:Hs.
      eapply space_decode_correct in Hs; eauto.
      destruct Hs; destruct_ex; destruct_conjs; subst.
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


End Lexeme.
