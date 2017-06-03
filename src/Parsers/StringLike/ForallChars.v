(** * Mapping predicates over [StringLike] things *)

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section forall_chars.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition forall_chars (str : String) (P : Char -> Prop)
    := forall n ch,
         take 1 (drop n str) ~= [ ch ]
         -> P ch.

  Lemma forall_chars_from_get (str : String) (P : Char -> Prop)
  : (forall n ch, get n str = Some ch -> P ch) -> forall_chars str P.
  Proof.
    unfold forall_chars.
    intros H n ch Heq.
    apply (H n); clear H.
    rewrite get_drop, <- get_0; assumption.
  Qed.

  Global Instance forall_chars_Proper
  : Proper (beq ==> pointwise_relation _ impl ==> impl) forall_chars.
  Proof.
    unfold pointwise_relation, respectful, forall_chars, impl.
    intros ?? H' ?? H'' H''' ?? H.
    rewrite <- H' in H.
    eauto using is_char_Proper.
  Qed.

  Global Instance forall_chars_Proper_flip
  : Proper (beq ==> pointwise_relation _ (flip impl) ==> flip impl) forall_chars.
  Proof.
    unfold pointwise_relation, respectful, forall_chars, flip, impl.
    intros ?? H' ?? H'' H''' ?? H.
    rewrite H' in H.
    eauto using is_char_Proper.
  Qed.

  Global Instance forall_chars_Proper_iff
  : Proper (beq ==> pointwise_relation _ iff ==> iff) forall_chars.
  Proof.
    unfold pointwise_relation, respectful.
    repeat intro; split;
    apply forall_chars_Proper; try assumption; repeat intro;
    match goal with
      | [ H : _ |- _ ] => apply H; assumption
    end.
  Qed.

  Global Instance forall_chars_Proper_eq
  : Proper (beq ==> pointwise_relation _ eq ==> impl) forall_chars.
  Proof.
    unfold pointwise_relation, respectful, forall_chars, impl.
    intros ?? H' ?? H'' H''' ?? H.
    rewrite <- H' in H.
    rewrite <- H''; eauto.
  Qed.

  Global Instance forall_chars_Proper_eq_flip
  : Proper (beq ==> pointwise_relation _ eq ==> flip impl) forall_chars.
  Proof.
    unfold pointwise_relation, respectful, forall_chars, flip, impl.
    intros ?? H' ?? H'' H''' ?? H.
    rewrite H' in H.
    rewrite H''; eauto.
  Qed.

  Global Instance forall_chars_Proper_eq_iff
  : Proper (beq ==> pointwise_relation _ eq ==> iff) forall_chars.
  Proof.
    unfold pointwise_relation, respectful.
    repeat intro; split;
    apply forall_chars_Proper; try assumption; repeat intro;
      match goal with
      | [ H : _ |- _ ] => apply H; assumption
      | [ H : _ |- _ ] => rewrite H; assumption
      | [ H : _ |- _ ] => rewrite <- H; assumption
      end.
  Qed.

  Lemma forall_chars_nil (str : String) P
  : length str = 0 -> forall_chars str P.
  Proof.
    intros H n ch H'.
    apply length_singleton in H'.
    rewrite take_length, drop_length, H in H'.
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

  Lemma forall_chars__split (str : String) P n
  : forall_chars str P
    <-> (forall_chars (take n str) P /\ forall_chars (drop n str) P).
  Proof.
    unfold forall_chars; repeat (split || intro);
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

  Lemma forall_chars_singleton (str : String) P ch
  : str ~= [ ch ] -> (P ch <-> forall_chars str P).
  Proof.
    intro H.
    pose proof (length_singleton _ _ H).
    unfold forall_chars.
    split; intro H'; repeat intro.
    { match goal with
        | [ n : nat |- _ ] => destruct n; [ | exfalso ]
      end;
      repeat match goal with
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
        | [ H : _ |- _ ] => apply (H 0)
      end.
      rewrite drop_0.
      rewrite take_long; trivial; omega. }
  Qed.

  Lemma forall_chars_singleton_length (str : String) P (H : length str = 1)
  : forall_chars str P <-> (forall ch, str ~= [ ch ] -> P ch).
  Proof.
    split.
    { intro H''.
      intros ch' H'''.
      apply (forall_chars_singleton _ _ _ H'''); assumption. }
    { destruct (singleton_exists _ H) as [ch H'].
      intro H''.
      apply (forall_chars_singleton _ P ch H'); eauto. }
  Qed.

  Lemma forall_chars_False (str : String) P
  : (forall ch, ~P ch) -> forall_chars str P -> length str = 0.
  Proof.
    intros H' H.
    case_eq (length str); trivial.
    specialize (H (length str - 1)).
    pose proof (singleton_exists (drop (length str - 1) str)) as H''.
    rewrite drop_length in H''.
    intros n H'''.
    rewrite H''' in *.
    rewrite sub_plus in H'' by omega.
    rewrite Minus.minus_diag in *.
    specialize (H'' eq_refl).
    destruct H'' as [ch H''].
    exfalso; eapply H', H.
    rewrite take_long; try eassumption.
    apply length_singleton in H''; omega.
  Qed.

  Global Opaque forall_chars.

  Lemma forall_chars__split_forall (str : String) P
  : forall_chars str P
    <-> (forall n, forall_chars (take n str) P /\ forall_chars (drop n str) P).
  Proof.
    split.
    { intros H n.
      rewrite <- forall_chars__split; assumption. }
    { intro H.
      specialize (H 0).
      rewrite forall_chars__split; eassumption. }
  Qed.

  Lemma forall_chars_take (str : String) P
  : forall_chars str P <-> (forall n, forall_chars (take (S n) str) P).
  Proof.
    split.
    { intros H n.
      revert H; rewrite forall_chars__split; intro H; destruct H; eassumption. }
    { intro H.
      specialize (H (length str)).
      rewrite take_long in H by omega; assumption. }
  Qed.

  Lemma forall_chars_drop (str : String) P
  : forall_chars str P <-> (forall n, forall_chars (drop n str) P).
  Proof.
    split.
    { intros H n.
      revert H; rewrite forall_chars__split; intro H; destruct H; eassumption. }
    { intro H.
      specialize (H 0).
      rewrite drop_0 in H; assumption. }
  Qed.

  Lemma forall_chars_get (str : String) P
  : forall_chars str P <-> (forall n ch, get n str = Some ch -> P ch).
  Proof.
    split.
    { intros H n ch Heq.
      rewrite get_drop in Heq.
      apply get_0 in Heq.
      apply forall_chars__split with (n := n) in H.
      destruct H as [_ H].
      apply forall_chars__split with (n := 1) in H.
      destruct H as [H _].
      rewrite forall_chars_singleton_length in H.
      { auto. }
      { apply length_singleton in Heq; assumption. } }
    { apply forall_chars_from_get. }
  Qed.

  Definition forall_chars__char_in (str : String) (ls : list Char)
    := forall_chars str (fun ch => List.In ch ls).

  Definition forall_chars__impl__forall_chars__char_in {str ls} {P : _ -> Prop}
             (H : forall ch, P ch -> List.In ch ls)
  : impl (forall_chars str P) (forall_chars__char_in str ls).
  Proof.
    unfold forall_chars__char_in.
    apply forall_chars_Proper; trivial; reflexivity.
  Qed.

  Definition forall_chars__char_in__impl__forall_chars {str ls} {P : _ -> Prop}
             (H : forall ch, List.In ch ls -> P ch)
  : impl (forall_chars__char_in str ls) (forall_chars str P).
  Proof.
    unfold forall_chars__char_in.
    apply forall_chars_Proper; trivial; reflexivity.
  Qed.

  Global Instance forall_chars__char_in__Proper
  : Proper (beq ==> eq ==> impl) forall_chars__char_in.
  Proof.
    unfold pointwise_relation, respectful, forall_chars__char_in, impl.
    repeat intro; subst.
    match goal with
      | [ H : _ |- _ ] => rewrite <- H; assumption
    end.
  Qed.

  Global Instance forall_chars__char_in__Proper_iff
  : Proper (beq ==> eq ==> iff) forall_chars__char_in.
  Proof.
    unfold pointwise_relation, respectful, forall_chars__char_in, impl.
    repeat intro; subst.
    match goal with
      | [ H : _ |- _ ] => rewrite <- H; reflexivity
    end.
  Qed.

  Lemma forall_chars__char_in__split n (str : String) ls
  : forall_chars__char_in str ls
    <-> (forall_chars__char_in (take n str) ls /\ forall_chars__char_in (drop n str) ls).
  Proof.
    unfold forall_chars__char_in; apply forall_chars__split.
  Qed.

  Lemma forall_chars__char_in__app_or_iff (str : String) (ls1 ls2 : list Char)
  : forall_chars__char_in str (ls1 ++ ls2)
    <-> (forall_chars str (fun ch => List.In ch ls1 \/ List.In ch ls2)).
  Proof.
    unfold forall_chars__char_in; split; repeat intro.
    { eapply forall_chars_Proper; [ .. | eassumption ]; [ reflexivity | ].
      intro; hnf.
      apply List.in_app_or. }
    { eapply forall_chars_Proper; [ .. | eassumption ]; [ reflexivity | ].
      intro; hnf.
      apply List.in_or_app. }
  Qed.

  Lemma forall_chars__char_in__or_app (str : String) (ls1 ls2 : list Char)
  : forall_chars__char_in str ls1 \/ forall_chars__char_in str ls2 -> forall_chars__char_in str (ls1 ++ ls2).
  Proof.
    unfold forall_chars__char_in.
    intros [?|?]; repeat intro;
    (eapply forall_chars_Proper; [ .. | eassumption ]; [ reflexivity | ]; intros ??);
    apply List.in_or_app; eauto.
  Qed.

  Lemma forall_chars__char_in_nil (str : String)
  : forall_chars__char_in str nil <-> length str = 0.
  Proof.
    unfold forall_chars__char_in.
    split.
    { eapply forall_chars_False; simpl; eauto. }
    { apply forall_chars_nil. }
  Qed.

  Lemma forall_chars__char_in_empty (str : String) (H : length str = 0) ls
  : forall_chars__char_in str ls.
  Proof.
    unfold forall_chars__char_in.
    apply forall_chars_nil; assumption.
  Qed.

  Lemma forall_chars__char_in_singleton_str (str : String) ls ch (H : str ~= [ ch ])
  : forall_chars__char_in str ls <-> List.In ch ls.
  Proof.
    unfold forall_chars__char_in.
    rewrite <- forall_chars_singleton; try eassumption; reflexivity.
  Qed.

  Global Opaque forall_chars__char_in.
End forall_chars.
