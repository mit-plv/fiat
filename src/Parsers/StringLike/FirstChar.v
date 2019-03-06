(** * Mapping predicates over [StringLike] things *)

Require Import Coq.omega.Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section for_first_char.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition for_first_char (str : String) (P : Char -> Prop)
    := forall ch,
         take 1 str ~= [ ch ]
         -> P ch.

  Global Instance for_first_char_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) for_first_char.
  Proof.
    unfold pointwise_relation, respectful, for_first_char, impl.
    intros ?? H' ?? H'' H''' ? H.
    rewrite <- H' in H.
    eauto using is_char_Proper.
  Qed.

  Global Instance for_first_char_Proper_flip
  : Proper (beq ==> pointwise_relation _ (flip impl) ==> flip impl) for_first_char.
  Proof.
    unfold pointwise_relation, respectful, for_first_char, flip, impl.
    intros ?? H' ?? H'' H''' ? H.
    rewrite H' in H.
    eauto using is_char_Proper.
  Qed.

  Global Instance for_first_char_Proper_iff
  : Proper (beq ==> pointwise_relation _ iff ==> iff) for_first_char.
  Proof.
    unfold pointwise_relation, respectful.
    repeat intro; split;
    apply for_first_char_Proper; try assumption; repeat intro;
    match goal with
      | [ H : _ |- _ ] => apply H; assumption
    end.
  Qed.

  Lemma for_first_char_nil (str : String) P
  : length str = 0 -> for_first_char str P.
  Proof.
    intros H ch H'.
    apply length_singleton in H'.
    rewrite ?take_length, ?drop_length, H in H'.
    simpl in H'; omega.
  Qed.

  Lemma helper
        (P : nat -> nat -> Type)
        n
        (H0 : forall n0, P (min 1 (n - n0)) n0)
        (H1 : forall n0, P 1 (n0 + n))
        {n0}
  : P 1 n0.
  Proof.
    destruct (Compare_dec.le_dec n n0) as [H'|H'].
    { specialize (H1 (n0 - n)).
      rewrite Nat.sub_add in H1 by assumption; assumption. }
    { apply Compare_dec.not_le in H'.
      specialize (H0 n0).
      destruct (n - n0) as [|[|]] eqn:?; simpl in *; trivial; omega. }
  Defined.

  Lemma for_first_char__take n (str : String) P
  : for_first_char str P
    <-> for_first_char (take (S n) str) P.
  Proof.
    unfold for_first_char; repeat (split || intro);
    repeat match goal with
                         | [ H : _ |- _ ] => setoid_rewrite drop_length in H
                         | [ H : _ |- _ ] => setoid_rewrite take_length in H
                         | [ H : _ |- _ ] => setoid_rewrite drop_take in H
                         | [ H : _ |- _ ] => setoid_rewrite take_take in H
                         | [ H : _ |- _ ] => setoid_rewrite drop_drop in H
                         | [ H : _ /\ _ |- _ ] => destruct H
                         | [ H : context[min 1 ?x] |- _ ] => destruct x eqn:?; simpl in H
                         | [ H : is_true (take 0 _ ~= [ _ ]) |- _ ] => exfalso; apply length_singleton in H
                         | _ => omega
                         | _ => progress simpl in *; omega
                         | _ => solve [ eauto ]
                         | _ => solve [ eapply (@helper (fun a b => take a (drop b str) ~= [ ch ] -> P ch)); eauto ]
                       end.
  Qed.

  Lemma for_first_char_singleton (str : String) P ch
  : str ~= [ ch ] -> (P ch <-> for_first_char str P).
  Proof.
    intro H.
    pose proof (length_singleton _ _ H).
    unfold for_first_char.
    split; intro H'; repeat intro.
    { repeat match goal with
               | _ => intro
               | _ => omega
               | [ H : _ |- _ ] => rewrite drop_0 in H
               | [ H : _, H' : _ |- _ ] => rewrite (singleton_take H') in H
               | [ H : _ |- False ] => apply length_singleton in H
               | [ H : _ |- _ ] => rewrite take_length in H
               | [ H : _ |- _ ] => rewrite drop_length in H
               | [ H : ?x = 1, H' : context[?x] |- _ ] => rewrite H in H'
               | _ => erewrite singleton_unique; eassumption
               | [ H : context[min] |- _ ] => revert H; apply Min.min_case_strong
             end. }
    { match goal with
        | [ H : _ |- _ ] => apply H
      end.
      rewrite take_long; trivial; omega. }
  Qed.

  Lemma for_first_char_singleton_length (str : String) P (H : length str = 1)
  : for_first_char str P <-> (forall ch, str ~= [ ch ] -> P ch).
  Proof.
    split.
    { intro H''.
      intros ch' H'''.
      apply (for_first_char_singleton _ _ _ H'''); assumption. }
    { destruct (singleton_exists _ H) as [ch H'].
      intro H''.
      apply (for_first_char_singleton _ P ch H'); eauto. }
  Qed.

  Global Opaque for_first_char.

  Lemma for_first_char_exists (str : String) P (H : length str >= 1)
  : for_first_char str P <-> (exists ch, take 1 str ~= [ ch ] /\ P ch).
  Proof.
    rewrite (for_first_char__take 0).
    assert (H' : length (take 1 str) = 1)
      by (rewrite take_length; apply Min.min_case_strong; omega).
    destruct (singleton_exists _ H') as [ch H''].
    rewrite for_first_char_singleton_length by exact H'.
    split; intros.
    { exists ch; split; eauto. }
    { destruct_head ex.
      destruct_head and.
      repeat match goal with
               | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
                 => assert (ch = ch') by (eapply singleton_unique; eassumption);
                   clear H'
             end.
      subst; assumption. }
  Qed.

  Lemma for_first_char_False (str : String) P
  : (forall ch, ~P ch) -> for_first_char str P -> length str = 0.
  Proof.
    intros H' H.
    case_eq (length str); trivial.
    pose proof (singleton_exists (take 1 str)) as H''.
    rewrite take_length in H''.
    intros n H'''.
    rewrite H''' in *.
    specialize (H'' eq_refl).
    destruct H'' as [ch H''].
    apply (for_first_char__take 0) in H.
    apply (for_first_char_singleton _ _ _ H'') in H.
    specialize (H' ch).
    exfalso; eauto.
  Qed.

  Lemma for_first_char_combine (str : String) (P P' : Char -> Prop) (T : Prop) (H : forall ch, P ch -> P' ch -> T)
        (H0 : for_first_char str P)
        (H1 : for_first_char str P')
  : length str = 0 \/ T.
  Proof.
    case_eq (length str).
    { left; reflexivity. }
    { intros n H'; right.
      pose proof (singleton_exists (take 1 str)) as H''.
      rewrite take_length, H' in H''.
      specialize (H'' eq_refl).
      destruct H'' as [ch H''].
      specialize (H ch).
      apply (for_first_char__take 0) in H0.
      apply (for_first_char__take 0) in H1.
      apply (for_first_char_singleton _ _ _ H'') in H0.
      apply (for_first_char_singleton _ _ _ H'') in H1.
      eauto. }
  Qed.


  Definition first_char_in (str : String) (ls : list Char)
    := for_first_char str (fun ch => List.In ch ls).

  Definition for_first_char__impl__first_char_in {str ls} {P : _ -> Prop}
             (H : forall ch, P ch -> List.In ch ls)
  : impl (for_first_char str P) (first_char_in str ls).
  Proof.
    unfold first_char_in.
    apply for_first_char_Proper; trivial; reflexivity.
  Qed.

  Definition first_char_in__impl__for_first_char {str ls} {P : _ -> Prop}
             (H : forall ch, List.In ch ls -> P ch)
  : impl (first_char_in str ls) (for_first_char str P).
  Proof.
    unfold first_char_in.
    apply for_first_char_Proper; trivial; reflexivity.
  Qed.

  Global Instance first_char_in__Proper
  : Proper (beq ==> eq ==> impl) first_char_in.
  Proof.
    unfold pointwise_relation, respectful, first_char_in, impl.
    repeat intro; subst.
    match goal with
      | [ H : _ |- _ ] => rewrite <- H; assumption
    end.
  Qed.

  Global Instance first_char_in__Proper_iff
  : Proper (beq ==> eq ==> iff) first_char_in.
  Proof.
    unfold pointwise_relation, respectful, first_char_in, impl.
    repeat intro; subst.
    match goal with
      | [ H : _ |- _ ] => rewrite <- H; reflexivity
    end.
  Qed.

  Lemma first_char_in__take n (str : String) ls
  : first_char_in str ls
    <-> first_char_in (take (S n) str) ls.
  Proof.
    unfold first_char_in; apply for_first_char__take.
  Qed.

  Lemma first_char_in_nil (str : String)
  : first_char_in str nil <-> length str = 0.
  Proof.
    unfold first_char_in.
    split.
    { eapply for_first_char_False; simpl; eauto. }
    { apply for_first_char_nil. }
  Qed.

  Lemma first_char_in_empty (str : String) (H : length str = 0) ls
  : first_char_in str ls.
  Proof.
    unfold first_char_in.
    apply for_first_char_nil; assumption.
  Qed.

  Lemma first_char_in_singleton_str (str : String) ls ch (H : str ~= [ ch ])
  : first_char_in str ls <-> List.In ch ls.
  Proof.
    unfold first_char_in.
    rewrite <- for_first_char_singleton; try eassumption; reflexivity.
  Qed.

  Lemma first_char_in__app_or_iff (str : String) (ls1 ls2 : list Char)
  : first_char_in str (ls1 ++ ls2)
    <-> (first_char_in str ls1 \/ first_char_in str ls2).
  Proof.
    unfold first_char_in.
    setoid_rewrite List.in_app_iff.
    rewrite !(for_first_char__take 0 str).
    generalize (singleton_exists (take 1 str)).
    rewrite take_length.
    case_eq (length str).
    { intros H _.
      split; intro H0;
      [ left; apply first_char_in_empty
      | apply for_first_char_nil ];
      rewrite take_length, H; reflexivity. }
    { intros ? ? H.
      specialize (H eq_refl).
      destruct H as [ch H].
      rewrite <- !for_first_char_singleton by eassumption; tauto. }
  Qed.

  Lemma first_char_in__or_app (str : String) (ls1 ls2 : list Char)
  : first_char_in str ls1 \/ first_char_in str ls2 -> first_char_in str (ls1 ++ ls2).
  Proof.
    unfold first_char_in.
    intros [?|?]; repeat intro;
    (eapply for_first_char_Proper; [ .. | eassumption ]; [ reflexivity | ]; intros ??);
    apply List.in_or_app; eauto.
  Qed.

  Global Opaque first_char_in.

  Definition first_char_in__iff__for_first_char' {str ls} {P : _ -> Prop}
             (H : forall ch, P ch <-> List.In ch ls)
  : first_char_in str ls <-> for_first_char str P.
  Proof.
    split_iff.
    split; first [ apply for_first_char__impl__first_char_in | apply first_char_in__impl__for_first_char ];
    assumption.
  Qed.

  Definition first_char_in__iff__for_first_char {str ls}
  : first_char_in str ls <-> for_first_char str (fun ch => List.In ch ls).
  Proof.
    apply first_char_in__iff__for_first_char'; reflexivity.
  Qed.

  Lemma first_char_in_exists (str : String) ls (H : length str >= 1)
  : first_char_in str ls <-> (exists ch, take 1 str ~= [ ch ] /\ List.In ch ls).
  Proof.
    erewrite first_char_in__iff__for_first_char, for_first_char_exists by assumption.
    reflexivity.
  Qed.

  Lemma forall_chars__impl__for_first_char (str : String) P (H : forall_chars str P)
  : for_first_char str P.
  Proof.
    case_eq (length str).
    { apply for_first_char_nil. }
    { intros n H'.
      eapply forall_chars_take in H.
      apply (for_first_char__take 0).
      apply for_first_char_singleton_length.
      { rewrite take_length, H'; reflexivity. }
      { apply forall_chars_singleton_length.
        { rewrite take_length, H'; reflexivity. }
        { eassumption. } } }
  Qed.

  Lemma for_first_char__for_first_char__iff_short (str : String) P (H : length str <= 1)
  : forall_chars str P <-> for_first_char str P.
  Proof.
    case_eq (length str).
    { intro H'.
      split; intro.
      { apply for_first_char_nil; assumption. }
      { apply forall_chars_nil; assumption. } }
    { intros [|] H'; [ | exfalso; omega ].
      rewrite forall_chars_singleton_length by assumption.
      rewrite for_first_char_singleton_length by assumption.
      reflexivity. }
  Qed.

  Lemma for_first_char__split (str : String) P n
  : for_first_char str P
    <-> ((n = 0 /\ for_first_char (drop n str) P)
         \/ (n <> 0 /\ for_first_char (take n str) P)).
  Proof.
    destruct n; [ rewrite drop_0 | rewrite <- for_first_char__take ];
      intuition.
  Qed.

  Lemma for_first_char_True (str : String) (P : _ -> Prop) (p : forall ch, P ch)
  : for_first_char str P.
  Proof.
    destruct (length str) eqn:H.
    { apply for_first_char_nil; assumption. }
    { rewrite for_first_char_exists by omega.
      destruct (get 0 (take 1 str)) as [ch|] eqn:Heq.
      { exists ch; split; auto.
        rewrite is_char_parts.
        rewrite take_length; split; [ apply Min.min_case_strong; omega | assumption ]. }
      { apply no_first_char_empty in Heq.
        rewrite take_length, H in Heq.
        simpl in *; omega. } }
  Qed.
End for_first_char.
