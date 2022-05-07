Require Import
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.EquivFormat
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.Empty
        Fiat.Narcissus.Formats.Sequence
        Fiat.Narcissus.Formats.Delimiter
        Fiat.Narcissus.Formats.WithTerm.String
        Fiat.Narcissus.Formats.Lexeme.
Require Import
        Coq.Strings.String.

(* TODO: *)
Require Import
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.Decision
        Fiat.Narcissus.Automation.NormalizeFormats
        Fiat.Narcissus.Automation.ExtractData
        Fiat.Narcissus.Automation.AlignedAutomation.

Require Import
        Fiat.Narcissus.Formats.AsciiOpt.

Open Scope string_scope.
Open Scope format_scope.

(* Combinators and lemmas for XML. *)
(* TODO: we do not handle attributes at the moment. *)

Section XML.

  Context {A : Type}.
  Context {T : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid T}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  (* Maybe I should move these lemmas somewhere else. *)
  Lemma format_string_lexeme_format_compat (P : string -> Prop) :
    (forall s, P s -> 0 < length s) ->
    lexeme_format_compatible format_string P.
  Proof.
    intros H.
    hnf. intros s ? t ? ext HP ? Hh.
    hnf. intros ? t' ? ext' **.
    destruct s.
    - exfalso. apply H in HP. simpl in HP. lia.
    - simpl in *.
      unfold Bind2 in *. computes_to_inv. destruct_conjs. simpl in *. injections.
      match goal with
      | H : format_ascii _ _ ∋ (?t, _), H' : format_ascii _ _ ∋ (?t', _) |- _ =>
          assert (t = t') by eauto using format_ascii_det; subst
      end.
      match goal with
      | H : format_string _ _ ∋ (?t, _), H' : format_string _ _ ∋ (?t', _) |- _ =>
          assert (t = t') by eauto using format_string_det; subst
      end.
      rewrite <- mappend_assoc in *.
      unfold no_head_space in *.
      intros * Ha.
      match goal with
      | H : format_ascii _ _ ∋ _ |- _ =>
          eapply decode_format_ascii in H; destruct H; rewrite H in Ha
      end.
      injections.
      match goal with
      | H : format_ascii _ _ ∋ _ |- _ =>
          eapply decode_format_ascii in H; destruct H
      end.
      eauto.
      Unshelve. eauto.
  Qed.

  Definition string_lexeme_compat s :=
    exists a s', s = String a s' /\ is_space a = false.

  Lemma format_string_lexeme_source_compat s :
    string_lexeme_compat s ->
    lexeme_source_compatible format_string s.
  Proof.
    unfold string_lexeme_compat.
    intros (?&?&->&Hs).
    hnf. simpl. unfold Bind2. intros.
    computes_to_inv. destruct_conjs. simpl in *. injections.
    hnf. intros.
    match goal with
    | H : format_ascii _ _ ∋ _, H' : decode_ascii _ _ = _ |- _ =>
        eapply decode_format_ascii in H; destruct H;
        rewrite <- mappend_assoc, H in H'
    end.
    injections.
    eauto.
  Qed.

  Variable tag : string.
  Variable format_A : FormatM A T.
  Variable A_predicate : A -> Prop.

  Definition format_start_tag : FormatM unit T :=
    format_lexeme format_string ◦ (constant "<") ++
    format_lexeme format_string ◦ (constant tag) ++
    format_lexeme format_string ◦ (constant ">").

  Definition format_end_tag : FormatM unit T :=
    format_lexeme format_string ◦ (constant "</") ++
    format_lexeme format_string ◦ (constant tag) ++
    format_lexeme format_string ◦ (constant ">").

  Definition format_element : FormatM A T :=
    format_delimiter format_start_tag format_end_tag format_A.

  (* Definition element_decode_correct' (tag : string) : *)
  (*   string_lexeme_compat tag -> *)
  (*   CorrectDecoderFor A_predicate (format_element tag). *)
  (* Proof. *)

End XML.

#[export]
Hint Extern 4 (lexeme_source_compatible format_string _) =>
  eapply format_string_lexeme_source_compat;
  unfold string_lexeme_compat; intuition eauto
    : data_inv_hints.

#[export]
Hint Extern 4 (lexeme_format_compatible format_string _) =>
  simpl; eapply format_string_lexeme_format_compat; lia
    : lexeme_compatible_hints.
