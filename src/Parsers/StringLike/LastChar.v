(** * Mapping predicates over [StringLike] things *)
Require Import Coq.omega.Omega.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Local Arguments minus !_ !_.

Section for_last_char.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition for_last_char (str : String) (P : Char -> Prop)
    := forall ch,
         drop (pred (length str)) str ~= [ ch ]
         -> P ch.

  Global Instance for_last_char_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) for_last_char.
  Proof.
    unfold pointwise_relation, respectful, for_last_char, impl.
    intros ?? H' ?? H'' H''' ? H.
    rewrite <- H' in H.
    eauto using is_char_Proper.
  Qed.

  Global Instance for_last_char_Proper_flip
  : Proper (beq ==> pointwise_relation _ (flip impl) ==> flip impl) for_last_char.
  Proof.
    unfold pointwise_relation, respectful, for_last_char, flip, impl.
    intros ?? H' ?? H'' H''' ? H.
    rewrite H' in H.
    eauto using is_char_Proper.
  Qed.

  Global Instance for_last_char_Proper_iff
  : Proper (beq ==> pointwise_relation _ iff ==> iff) for_last_char.
  Proof.
    unfold pointwise_relation, respectful.
    repeat intro; split;
    apply for_last_char_Proper; try assumption; repeat intro;
    match goal with
      | [ H : _ |- _ ] => apply H; assumption
    end.
  Qed.

  Lemma for_last_char_nil (str : String) P
  : length str = 0 -> for_last_char str P.
  Proof.
    intros H ch H'.
    apply length_singleton in H'.
    rewrite ?take_length, ?drop_length, H in H'.
    simpl in H'; omega.
  Qed.

  Lemma for_last_char__drop n (str : String) (H : n < length str) P
  : for_last_char str P
    <-> for_last_char (drop n str) P.
  Proof.
    unfold for_last_char; repeat (split || intro);
    repeat match goal with
                         | [ H : _ |- _ ] => setoid_rewrite drop_length in H
                         | [ H : _ |- _ ] => setoid_rewrite take_length in H
                         | [ H : _ |- _ ] => setoid_rewrite drop_take in H
                         | [ H : _ |- _ ] => setoid_rewrite take_take in H
                         | [ H : _ |- _ ] => setoid_rewrite drop_drop in H
                         | [ H : _ /\ _ |- _ ] => destruct H
                         | [ H : context[min 1 ?x] |- _ ] => destruct x eqn:?; simpl in H
                         | [ H : is_true (take 0 _ ~= [ _ ]) |- _ ] => exfalso; apply length_singleton in H
                         | [ H : ?x < ?y, H' : context[pred (?y - ?x)] |- _ ]
                           => replace (pred (y - x)) with (pred y - x) in H' by omega
                         | [ H : context[(?x - ?y + ?y)%nat] |- _ ] => rewrite Nat.sub_add in H by omega
                         | _ => omega
                         | _ => progress simpl in *; omega
                         | _ => solve [ eauto ]
                       end.
  Qed.

  Lemma for_last_char__add_drop n (str : String) P
  : for_last_char str P
    -> for_last_char (drop n str) P.
  Proof.
    unfold for_last_char;
      repeat match goal with
             | [ |- (forall x, _) -> (forall y, _) ]
               => let x' := fresh in
                  let H := fresh in
                  intros H x'; specialize (H x'); revert H
             | [ |- (_ -> ?T) -> (_ -> ?T) ]
               => let x' := fresh in
                  let H := fresh in
                  intros H x'; apply H; revert x'
             | [ H : _ /\ _ |- _ ] => destruct H
             | _ => setoid_rewrite drop_length
             | _ => setoid_rewrite drop_drop
             | _ => setoid_rewrite is_char_parts
             | _ => intro
             | [ H : context[min 1 ?x] |- _ ] => destruct x eqn:?; simpl in H
             | [ H : is_true (take 0 _ ~= [ _ ]) |- _ ] => exfalso; apply length_singleton in H
             | [ H : ?x < ?y, H' : context[pred (?y - ?x)] |- _ ]
               => replace (pred (y - x)) with (pred y - x) in H' by omega
             | [ H' : context[(pred (?y - ?x) + ?x)%nat] |- _ ]
               => replace (pred (y - x) + x) with (pred y) in H' by omega
             | [ H : context[(?x - ?y + ?y)%nat] |- _ ] => rewrite Nat.sub_add in H by omega
             | [ |- _ /\ _ ] => split
             | _ => omega
             | _ => progress simpl in *; omega
             | _ => solve [ eauto ]
             end.
  Qed.

  Global Arguments for_last_char__drop : clear implicits.

  Lemma for_last_char_singleton (str : String) P ch
  : str ~= [ ch ] -> (P ch <-> for_last_char str P).
  Proof.
    intro H.
    pose proof (length_singleton _ _ H).
    unfold for_last_char.
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
      repeat match goal with
             | [ H : ?x = 1 |- _ ] => rewrite H
             | _ => progress simpl
             end.
      rewrite drop_0; assumption. }
  Qed.

  Lemma for_last_char_singleton_length (str : String) P (H : length str = 1)
  : for_last_char str P <-> (forall ch, str ~= [ ch ] -> P ch).
  Proof.
    split.
    { intro H''.
      intros ch' H'''.
      apply (for_last_char_singleton _ _ _ H'''); assumption. }
    { destruct (singleton_exists _ H) as [ch H'].
      intro H''.
      apply (for_last_char_singleton _ P ch H'); eauto. }
  Qed.

  Global Opaque for_last_char.

  Lemma for_last_char_exists (str : String) P (H : length str >= 1)
  : for_last_char str P <-> (exists ch, drop (pred (length str)) str ~= [ ch ] /\ P ch).
  Proof.
    rewrite (for_last_char__drop (pred (length str)) str) by omega.
    assert (H' : length (drop (pred (length str)) str) = 1)
      by (rewrite drop_length; omega).
    destruct (singleton_exists _ H') as [ch H''].
    rewrite for_last_char_singleton_length by exact H'.
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

  Lemma for_last_char_False (str : String) P
  : (forall ch, ~P ch) -> for_last_char str P -> length str = 0.
  Proof.
    intros H' H.
    case_eq (length str); trivial.
    pose proof (singleton_exists (drop (pred (length str)) str)) as H''.
    rewrite drop_length in H''.
    intros n H'''.
    rewrite H''' in *.
    simpl in *.
    specialize_by omega.
    destruct H'' as [ch H''].
    apply (for_last_char__drop n) in H; [ | omega ].
    apply (for_last_char_singleton _ _ _ H'') in H.
    specialize (H' ch).
    exfalso; eauto.
  Qed.

  Lemma for_last_char_combine (str : String) (P P' : Char -> Prop) (T : Prop) (H : forall ch, P ch -> P' ch -> T)
        (H0 : for_last_char str P)
        (H1 : for_last_char str P')
  : length str = 0 \/ T.
  Proof.
    case_eq (length str).
    { left; reflexivity. }
    { intros n H'; right.
      pose proof (singleton_exists (drop (pred (length str)) str)) as H''.
      rewrite drop_length, H' in H''.
      simpl in *.
      specialize_by omega.
      destruct H'' as [ch H''].
      specialize (H ch).
      apply (for_last_char__drop n) in H0; [ | omega ].
      apply (for_last_char__drop n) in H1; [ | omega ].
      apply (for_last_char_singleton _ _ _ H'') in H0.
      apply (for_last_char_singleton _ _ _ H'') in H1.
      eauto. }
  Qed.


  Definition last_char_in (str : String) (ls : list Char)
    := for_last_char str (fun ch => List.In ch ls).

  Definition for_last_char__impl__last_char_in {str ls} {P : _ -> Prop}
             (H : forall ch, P ch -> List.In ch ls)
  : impl (for_last_char str P) (last_char_in str ls).
  Proof.
    unfold last_char_in.
    apply for_last_char_Proper; trivial; reflexivity.
  Qed.

  Definition last_char_in__impl__for_last_char {str ls} {P : _ -> Prop}
             (H : forall ch, List.In ch ls -> P ch)
  : impl (last_char_in str ls) (for_last_char str P).
  Proof.
    unfold last_char_in.
    apply for_last_char_Proper; trivial; reflexivity.
  Qed.

  Global Instance last_char_in__Proper
  : Proper (beq ==> eq ==> impl) last_char_in.
  Proof.
    unfold pointwise_relation, respectful, last_char_in, impl.
    repeat intro; subst.
    match goal with
      | [ H : _ |- _ ] => rewrite <- H; assumption
    end.
  Qed.

  Global Instance last_char_in__Proper_iff
  : Proper (beq ==> eq ==> iff) last_char_in.
  Proof.
    unfold pointwise_relation, respectful, last_char_in, impl.
    repeat intro; subst.
    match goal with
      | [ H : _ |- _ ] => rewrite <- H; reflexivity
    end.
  Qed.

  Lemma last_char_in__drop n (str : String) (H : n < length str) ls
  : last_char_in str ls
    <-> last_char_in (drop n str) ls.
  Proof.
    unfold last_char_in; apply for_last_char__drop; assumption.
  Qed.

  Global Arguments last_char_in__drop : clear implicits.

  Lemma last_char_in_nil (str : String)
  : last_char_in str nil <-> length str = 0.
  Proof.
    unfold last_char_in.
    split.
    { eapply for_last_char_False; simpl; eauto. }
    { apply for_last_char_nil. }
  Qed.

  Lemma last_char_in_empty (str : String) (H : length str = 0) ls
  : last_char_in str ls.
  Proof.
    unfold last_char_in.
    apply for_last_char_nil; assumption.
  Qed.

  Lemma last_char_in_singleton_str (str : String) ls ch (H : str ~= [ ch ])
  : last_char_in str ls <-> List.In ch ls.
  Proof.
    unfold last_char_in.
    rewrite <- for_last_char_singleton; try eassumption; reflexivity.
  Qed.

  Lemma last_char_in__app_or_iff (str : String) (ls1 ls2 : list Char)
  : last_char_in str (ls1 ++ ls2)
    <-> (last_char_in str ls1 \/ last_char_in str ls2).
  Proof.
    unfold last_char_in.
    setoid_rewrite List.in_app_iff.
    generalize (singleton_exists (drop (pred (length str)) str)).
    rewrite drop_length.
    case_eq (length str).
    { intros H _.
      split; intro H0;
      [ left; apply last_char_in_empty
      | apply for_last_char_nil ];
      assumption. }
    { intros ? ? H.
      simpl in *.
      specialize_by omega.
      destruct H as [ch H].
      rewrite !(for_last_char__drop n str) by omega.
      rewrite <- !for_last_char_singleton by eassumption; tauto. }
  Qed.

  Lemma last_char_in__or_app (str : String) (ls1 ls2 : list Char)
  : last_char_in str ls1 \/ last_char_in str ls2 -> last_char_in str (ls1 ++ ls2).
  Proof.
    unfold last_char_in.
    intros [?|?]; repeat intro;
    (eapply for_last_char_Proper; [ .. | eassumption ]; [ reflexivity | ]; intros ??);
    apply List.in_or_app; eauto.
  Qed.

  Global Opaque last_char_in.

  Definition last_char_in__iff__for_last_char' {str ls} {P : _ -> Prop}
             (H : forall ch, P ch <-> List.In ch ls)
  : last_char_in str ls <-> for_last_char str P.
  Proof.
    split_iff.
    split; first [ apply for_last_char__impl__last_char_in | apply last_char_in__impl__for_last_char ];
    assumption.
  Qed.

  Definition last_char_in__iff__for_last_char {str ls}
  : last_char_in str ls <-> for_last_char str (fun ch => List.In ch ls).
  Proof.
    apply last_char_in__iff__for_last_char'; reflexivity.
  Qed.

  Lemma last_char_in_exists (str : String) ls (H : length str >= 1)
  : last_char_in str ls <-> (exists ch, drop (pred (length str)) str ~= [ ch ] /\ List.In ch ls).
  Proof.
    erewrite last_char_in__iff__for_last_char, for_last_char_exists by assumption.
    reflexivity.
  Qed.

  Lemma forall_chars__impl__for_last_char (str : String) P (H : forall_chars str P)
  : for_last_char str P.
  Proof.
    case_eq (length str).
    { apply for_last_char_nil. }
    { intros n H'.
      eapply forall_chars_drop in H.
      apply (for_last_char__drop n); [ omega | ].
      apply for_last_char_singleton_length.
      { rewrite drop_length, H'; omega. }
      { apply forall_chars_singleton_length.
        { rewrite drop_length, H'; omega. }
        { eassumption. } } }
  Qed.

  Lemma for_last_char__for_last_char__iff_short (str : String) P (H : length str <= 1)
  : forall_chars str P <-> for_last_char str P.
  Proof.
    case_eq (length str).
    { intro H'.
      split; intro.
      { apply for_last_char_nil; assumption. }
      { apply forall_chars_nil; assumption. } }
    { intros [|] H'; [ | exfalso; omega ].
      rewrite forall_chars_singleton_length by assumption.
      rewrite for_last_char_singleton_length by assumption.
      reflexivity. }
  Qed.

  Lemma forall_chars_for_last_char_overlap {P Q} {R : Prop} {str dn tn}
        (H0 : forall_chars (drop dn str) P)
        (H1 : for_last_char (take tn str) Q)
        (Hshort : dn < length str)
        (Hcompat : dn < tn)
        (HR : forall ch, P ch -> Q ch -> R)
    : R.
  Proof.
    apply forall_chars_take with (n := tn - dn - 1) in H0.
    rewrite take_drop in H0.
    replace (S (tn - dn - 1) + dn) with tn in H0 by omega.
    apply for_last_char__add_drop with (n := dn) in H1.
    apply forall_chars__impl__for_last_char in H0.
    destruct (for_last_char_combine HR H0 H1) as [H2|]; [ | assumption ].
    contradict H2.
    rewrite drop_length, take_length.
    apply Min.min_case_strong; omega.
  Qed.

  Lemma for_last_char_exists_get (str : String) P (H : length str >= 1)
  : for_last_char str P <-> (exists ch, get (pred (length str)) str = Some ch /\ P ch).
  Proof.
    rewrite for_last_char_exists by assumption.
    split; intros [ch [H0 H1]]; exists ch; (split; [ | assumption ]); revert H0;
    rewrite get_drop, <- get_0;
    rewrite take_long by (rewrite drop_length; omega);
    trivial.
  Qed.

  Lemma for_last_char__split (str : String) P n
  : for_last_char str P
    <-> ((n < length str /\ for_last_char (drop n str) P)
         \/ (n >= length str /\ for_last_char (take n str) P)).
  Proof.
    destruct (le_lt_dec (length str) n);
      [ rewrite take_long by assumption
      | rewrite <- for_last_char__drop by assumption ];
      intuition.
  Qed.

  Lemma for_last_char_True (str : String) (P : _ -> Prop) (p : forall ch, P ch)
  : for_last_char str P.
  Proof.
    destruct (length str) eqn:H.
    { apply for_last_char_nil; assumption. }
    { rewrite for_last_char_exists by omega.
      destruct (get 0 (drop (pred (length str)) str)) as [ch|] eqn:Heq.
      { exists ch; split; auto.
        rewrite is_char_parts.
        rewrite drop_length; split; [ omega | assumption ]. }
      { apply no_first_char_empty in Heq.
        rewrite drop_length, H in Heq.
        simpl in *; omega. } }
  Qed.
End for_last_char.
