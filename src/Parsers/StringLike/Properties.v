(** * Theorems about string-like types *)
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Program.Basics.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.StringLike.Core Fiat.Common.Le Fiat.Common.UIP.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Le.

Set Implicit Arguments.

Section String.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition bool_eq_refl {x : String} : x =s x.
  Proof.
    reflexivity.
  Defined.

  Definition bool_eq_sym {x y : String} : ((x =s y) = (y =s x) :> bool)%string_like.
  Proof.
    case_eq (y =s x)%string_like; intro H';
    [
    | case_eq (x =s y)%string_like; intro H'' ].
    { apply (symmetry (R := (fun x y => x =s y))) in H'; assumption. }
    { apply (symmetry (R := (fun x y => x =s y))) in H''; hnf in H''.
      etransitivity; [ exact (eq_sym H'') | exact H' ]. }
    { reflexivity. }
  Defined.

  Definition bool_eq_trans {x y z : String} : (x =s y) -> (y =s z) -> (x =s z).
  Proof.
    apply (transitivity (R := (fun x y => x =s y))).
  Defined.

  Global Instance str_le_Proper_iff : Proper (beq ==> beq ==> iff) str_le | 1000.
  Proof.
    repeat match goal with
             | _ => intro
             | _ => split
             | [ H : _ ≤s _ |- _ ] => destruct H
             | _ => left; assumption
             | _ => right; assumption
             | _ => right; symmetry; assumption
             | [ H : ?x =s _ |- _ ] => rewrite H in *; clear x H
             | [ H : _ =s ?x |- _ ] => rewrite <- H in *; clear x H
           end.
  Qed.

  Global Instance str_le_Proper : Proper (beq ==> beq ==> impl) str_le.
  Proof.
    intros x y H' x' y' H'' H'''.
    apply (@str_le_Proper_iff x y H' x' y' H''); assumption.
  Qed.

  Global Instance str_le_Proper' : Proper (beq ==> beq ==> Basics.flip impl) str_le.
  Proof.
    intros x y H' x' y' H'' H'''.
    apply (@str_le_Proper_iff _ _ H' _ _ H''); assumption.
  Qed.

  Global Instance str_le_refl : Reflexive str_le.
  Proof.
    repeat intro; right; reflexivity.
  Qed.

  Global Instance str_le_antisym : @Antisymmetric _ beq _ str_le.
  Proof.
    intros ? ? [H'|H']; repeat subst; intros [H1|H1]; repeat subst; try reflexivity;
    solve [ reflexivity
          | exfalso; omega
          | assumption
          | symmetry; assumption ].
  Qed.

  Global Instance str_le_trans : Transitive str_le.
  Proof.
    intros ? ? ? [H'|H']; repeat subst; intros [H1|H1]; repeat subst;
    try (rewrite H1 in *; clear H1);
    try (rewrite H' in *; clear H');
    first [ reflexivity
          | left; assumption
          | left; etransitivity; eassumption ].
  Qed.

  Local Open Scope string_like_scope.

  Global Instance str_le_length_le_Proper : Proper (str_le ==> le) length.
  Proof.
    intros x y [H'|H']; auto with arith.
    rewrite H'; reflexivity.
  Qed.

  Global Instance str_le_length_le_Proper' : Proper (Basics.flip str_le ==> Basics.flip le) length.
  Proof.
    intros x y [H'|H']; unfold Basics.flip in *; auto with arith.
    rewrite H'; reflexivity.
  Qed.

  Lemma str_le_take {str n}
  : take n str ≤s str.
  Proof.
    destruct (le_gt_dec (length str) n).
    { right; apply take_long; assumption. }
    { left; rewrite take_short_length; omega. }
  Qed.

  Lemma str_le_drop {str n}
  : drop n str ≤s str.
  Proof.
    destruct n.
    { rewrite drop_0; reflexivity. }
    { hnf; rewrite drop_length.
      case_eq (length str); intro H'.
      { right; apply bool_eq_empty.
        { rewrite drop_length, H'; reflexivity. }
        { assumption. } }
      { intro; left; omega. } }
  Qed.

  Lemma take_length {str n}
  : length (take n str) = min n (length str).
  Proof.
    destruct (le_ge_dec (length str) n).
    { rewrite take_long by assumption.
      rewrite Min.min_r by assumption.
      reflexivity. }
    { rewrite take_short_length by assumption.
      rewrite Min.min_l by assumption.
      reflexivity. }
  Qed.

  Lemma length_le_trans
        {a b c : String} (H0' : length a < length b) (H1' : b ≤s c)
  : length a < length c.
  Proof.
    destruct H1'; setoid_subst.
    { etransitivity; eassumption. }
    { assumption. }
  Qed.

  Lemma strle_to_sumbool
        (s1 s2 : String) (f : String -> nat)
        (H' : f s1 < f s2 \/ s1 =s s2)
  : {f s1 < f s2} + {s1 =s s2}.
  Proof.
    unfold beq in *.
    case_eq (s1 =s s2).
    { intro H''; right; reflexivity. }
    { intro H''; left.
      destruct H' as [H' | H']; trivial.
      hnf in *.
      abstract congruence. }
  Defined.

  Section strle_choose.
    Context (s1 s2 : String) (f : String -> nat)
            (f_Proper : Proper (beq ==> eq) f)
            (H0' : f s1 < f s2 \/ s1 =s s2).

    Definition strle_left (H' : f s1 < f s2)
    : H0' = or_introl H'.
    Proof.
      destruct H0' as [H''|H'']; try clear H0'; [ apply f_equal | exfalso ].
      { apply le_proof_irrelevance. }
      { setoid_subst s1.
        eapply lt_irrefl; eassumption. }
    Qed.

    Definition strle_right (H' : s1 =s s2)
    : H0' = or_intror H'.
    Proof.
      destruct H0' as [H''|H'']; try clear H0'; [ exfalso | apply f_equal ].
      { setoid_subst s1; eapply lt_irrefl; eassumption. }
      { apply dec_eq_uip.
        decide equality. }
    Qed.
  End strle_choose.

  Lemma str_seq_lt_false
        {a b : String}
        (H0' : length a < length b)
        (H' : a =s b)
  : False.
  Proof.
    rewrite H' in H0'.
    eapply lt_irrefl; eassumption.
  Qed.

  Lemma singleton_exists_unique : forall s, length s = 1 -> exists !ch, s ~= [ ch ].
  Proof.
    intros s H'.
    destruct (singleton_exists s H') as [ch H''].
    exists ch.
    split; [ apply H'' | ].
    intro; apply singleton_unique; assumption.
  Qed.

  Lemma singleton_take {str ch} (H' : str ~= [ ch ]) n
  : take (S n) str =s str.
  Proof.
    eapply bool_eq_char; try eassumption.
    rewrite take_long; try assumption.
    apply length_singleton in H'; omega.
  Qed.

  Lemma drop_empty {str n} (H' : length str = 0) : drop n str =s str.
  Proof.
    apply bool_eq_empty; rewrite ?drop_length, ?take_length; omega.
  Qed.

  Lemma take_empty {str n} (H' : length str = 0) : take n str =s str.
  Proof.
    apply bool_eq_empty; rewrite ?drop_length, ?take_length; trivial.
    apply Min.min_case_strong; omega.
  Qed.

  Definition get_first_char_nonempty' str (H' : length str <> 0) : Char.
  Proof.
    refine (match get 0 str as ch return get 0 str = ch -> Char with
              | Some ch => fun _ => ch
              | None => fun H'' => match _ : False with end
            end eq_refl).
    abstract (
        pose proof (singleton_exists (take 1 str)) as H''';
        rewrite take_length in H'''; destruct (length str); try omega;
        specialize (H''' eq_refl);
        destruct H''' as [ch H'''];
        apply get_0 in H'''; congruence
      ).
  Defined.

  Definition get_first_char_nonempty str n (H' : length str = S n) : Char.
  Proof.
    apply (get_first_char_nonempty' str);
    generalize dependent (length str); clear; intros; abstract omega.
  Defined.

  Lemma no_first_char_empty str (H' : get 0 str = None) : length str = 0.
  Proof.
    case_eq (length (take 1 str)); rewrite take_length.
    { destruct (length str); simpl; intros; omega. }
    { intros ? H''.
      pose proof (singleton_exists (take 1 str)) as H'''.
      rewrite take_length in H'''.
      destruct (length str); try omega; simpl in *.
      specialize (H''' eq_refl).
      destruct H''' as [ch H'''].
      apply get_0 in H'''.
      congruence. }
  Qed.

  Lemma has_first_char_nonempty str (H' : length str = 0) : get 0 str = None.
  Proof.
    case_eq (get 0 str); try reflexivity.
    intros ch H''.
    exfalso.
    apply get_0, length_singleton in H''.
    rewrite take_length, H' in H''.
    simpl in *; omega.
  Qed.

  Global Instance get_Proper {n}
  : Proper (beq ==> eq) (get n).
  Proof.
    induction n.
    { intros x y H'.
      case_eq (get 0 x).
      { intros ch H''.
        apply get_0 in H''.
        rewrite H' in H''.
        rewrite (proj1 (get_0 _ _) H'').
        reflexivity. }
      { intros H'''.
        case_eq (get 0 y).
        { intros ch' H''.
          apply get_0 in H''.
          rewrite <- H' in H''.
          rewrite (proj1 (get_0 _ _) H'') in H'''.
          congruence. }
        { reflexivity. } } }
    { intros x y H'.
      rewrite !get_S.
      apply IHn.
      rewrite H'; reflexivity. }
  Qed.

  Lemma get_drop {n str} : get n str = get 0 (drop n str).
  Proof.
    revert str; induction n; intros.
    { rewrite drop_0; reflexivity. }
    { rewrite !get_S, IHn.
      rewrite drop_drop.
      repeat (f_equal; []).
      omega. }
  Qed.

  Lemma get_drop' {n m str} : get m (drop n str) = get (m + n) str.
  Proof.
    revert str n; induction m; intros.
    { rewrite <- get_drop; reflexivity. }
    { rewrite !get_S, !drop_drop, IHm.
      repeat (f_equal; []).
      omega. }
  Qed.

  Lemma fold'_nil
        {A} (f : Char -> A -> A) (init : A) (str : String)
  : fold' f init str 0 = init.
  Proof.
    reflexivity.
  Qed.

  Lemma fold'_cons
        {A} (f : Char -> A -> A) (init : A) (str : String) len
  : fold' f init str (S len)
    = match get (length str - S len) str with
        | Some ch => f ch (fold' f init str len)
        | None => init
      end.
  Proof.
    reflexivity.
  Qed.

  Global Instance fold'_Proper
         {A} (f : Char -> A -> A) (init : A)
  : Proper (beq ==> eq ==> eq) (fold' f init).
  Proof.
    intros ?? H' ? x ?; subst.
    induction x.
    { rewrite !fold'_nil; reflexivity. }
    { rewrite !fold'_cons.
      repeat match goal with
               | _ => reflexivity
               | _ => rewrite IHx
               | _ => rewrite H' at 1
               | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
             end. }
  Qed.

  Lemma fold'_drop
        {A} (f : Char -> A -> A) (init : A) (str : String) len m
        (H' : m + len <= length str)
  : fold' f init str len = fold' f init (drop m str) len.
  Proof.
    revert str m H'.
    induction len; simpl.
    { intros; reflexivity. }
    { intros.
      rewrite !(@get_drop (length _ - _)).
      rewrite drop_length, drop_drop.
      rewrite <- Nat.sub_add_distr, (plus_comm m), Nat.sub_add_distr, Nat.sub_add by omega.
      match goal with
        | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
      end.
      { rewrite <- IHlen by omega; reflexivity. }
      { reflexivity. } }
  Qed.

  Definition fold_nil
             {A} (f : Char -> A -> A) (init : A) (str : String)
             (H' : length str = 0)
  : fold f init str = init.
  Proof.
    unfold fold; rewrite H'; apply fold'_nil.
  Qed.

  Lemma fold_recr
        {A} (f : Char -> A -> A) (init : A) (str : String)
  : fold f init str
    = match get 0 str with
        | Some ch => f ch (fold f init (drop 1 str))
        | None => init
      end.
  Proof.
    case_eq (get 0 str).
    { intros ch H'.
      unfold fold.
      case_eq (length str).
      { intro H''.
        apply has_first_char_nonempty in H''.
        congruence. }
      { intros ? H''.
        rewrite fold'_cons.
        rewrite !H'', minus_diag, H'.
        rewrite drop_length, H''; simpl.
        rewrite <- minus_n_O.
        apply f_equal.
        rewrite <- fold'_drop by omega; reflexivity. } }
    { intro H'.
      apply fold_nil, no_first_char_empty; assumption. }
  Qed.

  Global Instance fold_Proper
         {A} (f : Char -> A -> A) (init : A)
  : Proper (beq ==> eq) (fold f init).
  Proof.
    repeat intro; apply fold'_Proper; trivial.
    setoid_subst_rel beq; reflexivity.
  Qed.

  Lemma take_n_1_singleton (str : String) n ch (H : take n str ~= [ ch ])
  : take 1 str ~= [ ch ].
  Proof.
    assert (H' : take 1 (take n str) ~= [ ch ])
      by (rewrite take_long; [ assumption | ];
          apply length_singleton in H; rewrite H; reflexivity).
    rewrite (take_take str 1 n) in H'.
    destruct n; simpl min in H'.
    { apply length_singleton in H'; rewrite take_length in H'.
      simpl in H'; congruence. }
    { exact H'. }
  Qed.

  Lemma get_take_lt (str : String) n m (Hle : n < m)
  : get n (take m str) = get n str.
  Proof.
    repeat match goal with
             | _ => progress simpl in *
             | _ => congruence
             | _ => omega
             | _ => progress rewrite ?drop_take
             | [ |- context[get ?n _] ] => not constr_eq n 0; rewrite !(get_drop (n := n))
             | [ |- context[get 0 ?str] ] => destruct (get 0 str) eqn:?
             | [ H : get 0 _ = Some _ |- _ ] => apply get_0 in H
             | [ H : get 0 _ = None |- _ ] => apply no_first_char_empty in H
             | [ H : _ |- _ ] => progress rewrite ?take_take, ?take_length in H
             | [ H : is_true (take ?n _ ~= [ _ ]) |- _ ] => progress apply take_n_1_singleton in H
             | [ |- Some _ = Some _ ] => apply f_equal
             | _ => eapply singleton_unique; eassumption
             | [ H : length ?str = 0, H' : is_true (take _ ?str ~= [ _ ]) |- _ ]
               => apply length_singleton in H'
             | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : context[min _ _] |- _ ] => revert H; apply Min.min_case_strong; intros
           end.
  Qed.
End String.
