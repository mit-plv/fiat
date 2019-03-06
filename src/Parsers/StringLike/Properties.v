(** * Theorems about string-like types *)

Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Fiat.Common.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Le.
Require Import Fiat.Common.Tactics.SetoidSubst.
Require Import Fiat.Common.Tactics.IsClosed.
Require Import Fiat.Parsers.StringLike.Core Fiat.Common.UIP.

Local Open Scope list_scope.

Set Implicit Arguments.

Section String.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  (** For use with [induction str using String_rect] *)
  Definition String_rect (P : String -> Type)
    : (forall str, length str = 0 -> P str)
      -> (forall n str (Hlen : length str = S n)
                 (IHstr : forall str', length str' = n -> P str'),
             P str)
      -> forall str, P str.
  Proof.
    intros Zcase Scase str.
    pose (length str) as len.
    pose proof (eq_refl : length str = len) as Hlen.
    clearbody len.
    revert str Hlen.
    induction len; intros.
    { eapply Zcase; assumption. }
    { eapply Scase; eassumption. }
  Defined.

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
    let ret := constr:(get 0 str) in
    refine (match get 0 str as ch return ret = ch -> Char with
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

  Global Instance get_Proper'
    : Proper (eq ==> beq ==> eq) get.
  Proof.
    intros ???; subst; apply get_Proper.
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
    { rewrite !get_S at 1; rewrite !drop_drop, IHm; simpl.
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

  Lemma fold_lookahead'_nil
        {A} (f : Char -> option Char -> A -> A) (init : A) (str : String)
  : fold_lookahead' f init str 0 = init.
  Proof.
    reflexivity.
  Qed.

  Lemma fold_lookahead'_cons
        {A} (f : Char -> option Char -> A -> A) (init : A) (str : String) len
  : fold_lookahead' f init str (S len)
    = match get (length str - S len) str with
        | Some ch => f ch (get (length str - len) str) (fold_lookahead' f init str len)
        | None => init
      end.
  Proof.
    reflexivity.
  Qed.

  Global Instance fold_lookahead'_Proper
         {A} (f : Char -> option Char -> A -> A) (init : A)
  : Proper (beq ==> eq ==> eq) (fold_lookahead' f init).
  Proof.
    intros ?? H' ? x ?; subst.
    induction x.
    { rewrite !fold_lookahead'_nil; reflexivity. }
    { rewrite !fold_lookahead'_cons.
      repeat match goal with
               | _ => reflexivity
               | _ => rewrite IHx
               | _ => rewrite H' at 1
               | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
             end. }
  Qed.

  Lemma fold_lookahead'_drop
        {A} (f : Char -> option Char -> A -> A) (init : A) (str : String) len m
        (H' : m + len <= length str)
  : fold_lookahead' f init str len = fold_lookahead' f init (drop m str) len.
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
      { rewrite drop_drop;
        rewrite <- Nat.sub_add_distr, (plus_comm m), Nat.sub_add_distr, Nat.sub_add by omega;
        rewrite <- IHlen by omega; reflexivity. }
      { reflexivity. } }
  Qed.

  Definition fold_lookahead_nil
             {A} (f : Char -> option Char -> A -> A) (init : A) (str : String)
             (H' : length str = 0)
  : fold_lookahead f init str = init.
  Proof.
    unfold fold_lookahead; rewrite H'; apply fold_lookahead'_nil.
  Qed.

  Lemma fold_lookahead_recr
        {A} (f : Char -> option Char -> A -> A) (init : A) (str : String)
  : fold_lookahead f init str
    = match get 0 str with
        | Some ch => f ch (get 1 str) (fold_lookahead f init (drop 1 str))
        | None => init
      end.
  Proof.
    case_eq (get 0 str).
    { intros ch H'.
      unfold fold_lookahead.
      case_eq (length str).
      { intro H''.
        apply has_first_char_nonempty in H''.
        congruence. }
      { intros n H''.
        rewrite fold_lookahead'_cons.
        rewrite !H'', minus_diag, H'.
        replace (S n - n) with 1 by omega.
        rewrite drop_length, H''; simpl.
        rewrite <- minus_n_O.
        apply f_equal.
        rewrite <- fold_lookahead'_drop by omega; reflexivity. } }
    { intro H'.
      apply fold_lookahead_nil, no_first_char_empty; assumption. }
  Qed.

  Global Instance fold_lookahead_Proper
         {A} (f : Char -> option Char -> A -> A) (init : A)
  : Proper (beq ==> eq) (fold_lookahead f init).
  Proof.
    repeat intro; apply fold_lookahead'_Proper; trivial.
    setoid_subst_rel beq; reflexivity.
  Qed.

  Lemma add_take_1_singleton (str : String) ch (H : str ~= [ ch ])
  : take 1 str ~= [ ch ].
  Proof.
    rewrite take_long; [ assumption | ].
    apply length_singleton in H; rewrite H; reflexivity.
  Qed.

  Lemma take_n_1_singleton (str : String) n ch (H : take n str ~= [ ch ])
  : take 1 str ~= [ ch ].
  Proof.
    apply add_take_1_singleton in H.
    rewrite (take_take str 1 n) in H.
    destruct n; simpl min in H.
    { apply length_singleton in H; rewrite take_length in H.
      simpl in H; congruence. }
    { exact H. }
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

  Lemma take_min_length (str : String) n
  : take n str =s take (min (length str) n) str.
  Proof.
    apply Min.min_case_strong; [ | reflexivity ].
    intro H.
    rewrite !take_long by (assumption || reflexivity).
    reflexivity.
  Qed.

  Lemma drop_min_length (str : String) n
  : drop n str =s drop (min (length str) n) str.
  Proof.
    apply Min.min_case_strong; [ | reflexivity ].
    intro H.
    apply bool_eq_empty; rewrite drop_length; omega.
  Qed.

  Lemma not_is_char_options str ch
  : (is_char str ch = false) <-> (length str <> 1 \/ get 0 str <> Some ch).
  Proof.
    destruct (is_char str ch) eqn:H;
    (split; intro H'; try solve [ inversion H' | exact eq_refl ]).
    { pose proof H as H0.
      apply add_take_1_singleton, get_0 in H.
      apply length_singleton in H0.
      rewrite H, H0 in H'.
      destruct H'; congruence. }
    { destruct (Nat.eq_dec (length str) 1); [ right | left; assumption ].
      intro H''.
      apply get_0 in H''.
      rewrite take_long in H'' by omega.
      congruence. }
  Qed.

  Lemma is_char_parts str ch
  : (is_true (is_char str ch)) <-> (length str = 1 /\ get 0 str = Some ch).
  Proof.
    destruct (is_char str ch) eqn:H;
    (split; intro H'; try solve [ inversion H' | reflexivity ]).
    { split.
      { apply length_singleton in H; assumption. }
      { apply get_0, add_take_1_singleton, H. } }
    { apply not_is_char_options in H; tauto. }
  Qed.

  Local Ltac induction_to_string str IHlen :=
    let H := fresh "H" in
    let len := fresh "len" in
    unfold fold;
      generalize dependent str; intro str;
      remember (length str) as len eqn:H;
      revert str H;
      induction len as [|len IHlen]; simpl; intros;
      [
      | specialize (IHlen (drop 1 str));
        rewrite drop_length in IHlen;
        specialize_by omega;
        try rewrite <- !H, !minus_diag;
        try rewrite <- fold'_drop in IHlen by omega ].

  Lemma to_string_length str
  : List.length (to_string str) = length str.
  Proof.
    induction_to_string str IHlen; trivial.
    destruct (get 0 str) eqn:H'; simpl; [ rewrite IHlen; reflexivity | ].
    apply no_first_char_empty in H'; omega.
  Qed.

  Local Ltac take_drop_to_string_t0 :=
    repeat match goal with
             | _ => progress specialize_by omega
             | _ => reflexivity
             | _ => omega
             | _ => progress subst
             | [ H : context[S _ - S _] |- _ ] => rewrite Nat.sub_succ in H
             | [ H : context[S ?x - ?x] |- _ ] => replace (S x - x) with 1 in H by omega
             | [ H : cons _ _ = cons _ _ |- _ ] => inversion H; clear H
             | _ => discriminate
             | [ H : context[_ + 1] |- _ ] => rewrite Nat.add_1_r in H
             | [ |- context[match get 0 ?s with _ => _ end] ] => destruct (get 0 s) eqn:?
             | [ H : get 0 ?str = None |- _ ] => apply no_first_char_empty in H
             | [ H : _ = ?x |- _ = ?x ] => rewrite <- H; clear H
             | [ H : ?x = _ |- ?x = _ ] => rewrite H; clear H
             | [ H : context[length (drop _ _)] |- _ ] => rewrite drop_length in H
             | [ |- context[length (drop _ _)] ] => rewrite drop_length
             | [ H : context[length (take _ _)] |- _ ] => rewrite take_length in H
             | [ |- context[length (take _ _)] ] => rewrite take_length
             | [ |- context[_ - 0] ] => rewrite Nat.sub_0_r
             | [ H : context[_ - 0] |- _ ] => rewrite Nat.sub_0_r in H
             | [ |- context[fold' _ _ (drop _ _) _] ] => rewrite <- fold'_drop by (rewrite ?take_length; try apply Min.min_case_strong; omega)
             | [ H : context[fold' _ _ (drop _ _) _] |- _ ] => rewrite <- fold'_drop in H by omega
             | [ H : ?x = ?y |- context[?x - ?y] ] => replace (x - y) with 0 by omega
             | [ H : ?y = ?x |- context[?x - ?y] ] => replace (x - y) with 0 by omega
             | [ |- cons _ _ = cons _ _ ] => apply f_equal2
             | [ H : context[get _ (drop 0 ?str)] |- _ ] => rewrite (drop_0 str) in H
             | [ H : ?x = Some ?c, H' : ?y = Some ?c' |- _ ]
               => not constr_eq c c'; is_var c; is_var c';
                  assert (c = c') by congruence; subst
             | _ => progress simpl in *
             | [ |- context[fold' _ _ (drop _ (drop _ _)) _] ] => rewrite drop_drop
             | [ |- context[?x + 1] ] => rewrite Nat.add_1_r
             | [ H : S _ = ?x |- context[match ?x with _ => _ end] ] => rewrite <- H
             | [ H : S _ = ?x, H' : context[match ?x with _ => _ end] |- _ ] => rewrite <- H in H'
             | [ H : context[?x - ?x] |- _ ] => rewrite minus_diag in H
             | [ |- context[?x - ?x] ] => rewrite minus_diag
             | [ H : context[get _ (take _ _)] |- _ ] => rewrite get_take_lt in H by omega
             | [ H : context[min (pred ?x) ?x] |- _ ] => rewrite (Min.min_l (pred x) x) in H by omega
             | [ |- context[take _ (drop _ _)] ] => rewrite take_drop
             | [ |- context[min ?x ?y] ] => rewrite (Min.min_l x y) by omega
             | [ |- context[get _ (drop 0 ?s)] ] => rewrite (drop_0 s)
             | [ |- context[get _ (drop _ (drop _ _))] ] => rewrite drop_drop
             | [ H : S ?x = ?y, H' : S ?z = ?y |- _ ]
               => is_var x; not constr_eq x z; assert (x = z) by omega; subst
             | [ H : S ?x = ?y, H' : ?y = S ?z |- _ ]
               => is_var x; not constr_eq x z; assert (x = z) by omega; subst
             | [ H : get ?n ?s = None |- _ ] => not constr_eq n 0; rewrite get_drop in H
           end.

  Local Ltac take_drop_to_string_t s n :=
    unfold fold; rewrite ?drop_length, ?take_length;
    revert n;
    let IHlen := fresh "IHlen" in
    induction_to_string s IHlen;
      destruct n as [|n];
      try specialize (IHlen n);
      take_drop_to_string_t0.

  Lemma drop_to_string s n
  : List.drop n (to_string s) = to_string (drop n s).
  Proof.
    take_drop_to_string_t s n.
  Qed.

  Lemma take_to_string s n
  : List.take n (to_string s) = to_string (take n s).
  Proof.
    destruct (le_lt_dec (length s) n) as [H|H].
    { rewrite take_long by assumption.
      rewrite take_all by (rewrite to_string_length; assumption).
      reflexivity. }
    { revert H.
      take_drop_to_string_t s n. }
  Qed.

  Lemma nth_to_string s n
  : List.nth_error (to_string s) n = get n s.
  Proof.
    rewrite get_drop.
    symmetry.
    take_drop_to_string_t s n;
      try solve [ apply has_first_char_nonempty; rewrite ?drop_length; omega ].
  Qed.

  Lemma beq_to_string {s s'}
  : to_string s = to_string s' <-> s =s s'.
  Proof.
    split.
    { intro H; apply bool_eq_from_get; intro n.
      rewrite <- !nth_to_string, H; reflexivity. }
    { intro; setoid_subst_rel beq.
      reflexivity. }
  Qed.

  Lemma is_char_to_string s ch
  : is_char s ch <-> to_string s = (ch::nil)%list.
  Proof.
    induction_to_string s IHlen.
    { split; intro H'; exfalso; try congruence.
      apply length_singleton in H'; omega. }
    { clear IHlen.
      take_drop_to_string_t0.
      split; intro H'.
      { pose proof (add_take_1_singleton _ _ H') as H''.
        apply length_singleton in H'.
        apply get_0 in H''.
        take_drop_to_string_t0. }
      { take_drop_to_string_t0.
        rewrite <- take_long by reflexivity.
        match goal with
          | [ H : S ?len = length ?s |- _ ] => is_var len; destruct len; rewrite <- H
        end.
        { apply get_0; assumption. }
        { take_drop_to_string_t0.
          match goal with
            | [ H : context[match get ?n ?s with _ => _ end] |- _ ] => destruct (get n s) eqn:?
          end;
          take_drop_to_string_t0. } } }
  Qed.

  Section substring.
    Local Ltac substring_t' :=
      idtac;
      match goal with
        | [ |- beq _ _ ] => reflexivity
        | [ |- _ = _ ] => reflexivity
        | _ => assumption
        | [ H : length ?s = 0 |- beq _ ?s ] => apply bool_eq_empty
        | [ H : length ?s = 0 |- beq ?s _ ] => apply bool_eq_empty
        | _ => progress rewrite ?drop_0, ?take_long, ?take_length, ?drop_length by trivial
        | _ => progress rewrite <- ?Nat.sub_min_distr_r, ?Nat.add_sub by trivial
        | _ => rewrite !take_long by (rewrite drop_length; omega)
        | [ |- context[min ?x ?y] ]
          => match goal with
               | [ |- context[min y x] ]
                 => rewrite (Min.min_comm x y)
             end
        | _ => repeat apply Min.min_case_strong; omega
      end.

    Local Ltac substring_t := repeat substring_t'.

    Lemma substring_correct3 {s : String} m (H : length s <= m)
    : substring 0 m s =s s.
    Proof. substring_t. Qed.

    Lemma substring_correct3' {s : String}
    : substring 0 (length s) s =s s.
    Proof. substring_t. Qed.

    Lemma substring_length {s n m}
    : length (substring n m s) = (min (length s) (m + n)) - n.
    Proof. substring_t. Qed.

    Lemma substring_correct0_length {s : String} {n}
    : length (substring n 0 s) = 0.
    Proof. substring_t. Qed.

    Lemma substring_correct0 {s s' : String} {n} (H : length s' = 0)
    : substring n 0 s =s s'.
    Proof. substring_t. Qed.

    Lemma substring_correct0'_length {s : String} {n m} (H : length s <= n)
    : length (substring n m s) = 0.
    Proof. substring_t. Qed.

    Lemma substring_correct0' {s s' : String} {n m} (H : length s <= n) (H' : length s' = 0)
    : substring n m s =s s'.
    Proof. substring_t. Qed.

    Lemma substring_correct4 {s : String} {n m m'}
          (H : length s <= n + m) (H' : length s <= n + m')
    : substring n m s =s substring n m' s.
    Proof. substring_t. Qed.

    Lemma substring_substring {s n m n' m'}
    : substring n m (substring n' m' s) =s substring (n + n') (min m (m' - n)) s.
    Proof.
      rewrite !drop_take, !take_take, !drop_drop; reflexivity.
    Qed.

    Lemma substring_min {x x' y y' z str} (H : substring x y str =s substring x' y' str)
    : substring x (min y z) str =s substring x' (min y' z) str.
    Proof.
      pose proof (fun y x => @substring_substring str 0 z x y) as H'; simpl in *.
      setoid_rewrite Nat.sub_0_r in H'.
      setoid_rewrite Min.min_comm in H'.
      rewrite <- !H', H; reflexivity.
    Qed.

    Lemma substring_min_length str x y
    : substring x (min y (length str)) str =s substring x y str.
    Proof.
      apply Min.min_case_strong; try reflexivity.
      intro H.
      apply substring_correct4; omega.
    Qed.

    Lemma substring_length_no_min {offset len s} (Hshort : len = 0 \/ offset + len <= length s)
    : length (substring offset len s) = len.
    Proof.
      rewrite substring_length; destruct Hshort as [Hshort|Hshort];
      try rewrite Min.min_r by (clear -Hshort; omega);
      subst; simpl;
      rewrite <- ?NPeano.Nat.sub_min_distr_r, ?NPeano.Nat.add_sub, ?minus_diag, ?Min.min_0_r;
      reflexivity.
    Qed.
  End substring.

  Lemma char_at_matches_is_char_no_ex offset len str P
        (Hlen : offset + len <= length str)
  : (EqNat.beq_nat len 1 && char_at_matches offset str P)%bool = true
    <-> match get offset str with
          | Some ch => (P ch /\ substring offset len str ~= [ch])%string_like
          | None => False
        end.
  Proof.
    destruct (get offset str) as [ch|] eqn:Heq.
    { split; intro H.
      { apply Bool.andb_true_iff in H.
        destruct H as [H0 H1].
        apply EqNat.beq_nat_true in H0; subst.
        erewrite char_at_matches_correct in H1 by eassumption.
        split; try assumption.
        rewrite get_drop in Heq.
        generalize dependent (drop offset str); clear Hlen offset str; intro str.
        intro H.
        apply get_0; assumption. }
      { destruct H as [H0 H1].
        erewrite char_at_matches_correct by eassumption.
        apply Bool.andb_true_iff; split; [ | eassumption ].
        apply length_singleton in H1.
        rewrite substring_length, <- Nat.sub_min_distr_r, Nat.add_sub in H1.
        apply EqNat.beq_nat_true_iff.
        revert H1.
        apply Min.min_case_strong; intros; omega. } }
    { split; [ intro H | intros [] ].
      rewrite get_drop in Heq.
      apply no_first_char_empty in Heq.
      rewrite drop_length in Heq.
      apply Bool.andb_true_iff in H.
      destruct H as [H0 H1].
      apply EqNat.beq_nat_true in H0; subst.
      omega. }
  Qed.

  Lemma char_at_matches_is_char offset len str P
        (Hlen : offset + len <= length str)
  : (EqNat.beq_nat len 1 && char_at_matches offset str P)%bool = true
    <-> (exists ch, P ch /\ substring offset len str ~= [ch])%string_like.
  Proof.
    rewrite char_at_matches_is_char_no_ex by assumption.
    destruct (get offset str) as [ch|] eqn:Heq.
    { split; intro H; [ exists ch; assumption | ].
      destruct H as [ch' H].
      assert (ch = ch');
        [
        | subst; assumption ].
      destruct H as [H0 H1].
      apply take_n_1_singleton in H1.
      apply get_0 in H1.
      rewrite get_drop in Heq.
      congruence. }
    { split; [ intros [] | intros [ch [H0 H1]] ].
      rewrite get_drop in Heq.
      apply no_first_char_empty in Heq.
      rewrite drop_length in Heq.
      apply length_singleton in H1.
      assert (len = 0) by omega; subst.
      rewrite substring_length, <- Nat.sub_min_distr_r, Nat.add_sub, Min.min_0_r in H1.
      omega. }
  Qed.

  Lemma not_all_lengths n : ~ forall str, length str = n.
  Proof.
    destruct n; intro H;
      [ destruct (strings_nontrivial 1) as [? H']
      | destruct (strings_nontrivial 0) as [? H'] ];
      rewrite H in H';
      congruence.
  Qed.

  Lemma not_not_string : ~ (String -> False).
  Proof.
    destruct (strings_nontrivial 0) as [str ?].
    eauto.
  Qed.

  Global Instance beq_subrelation_pointwise_iff {A} {R : relation A}
    : subrelation (beq ==> R)%signature (pointwise_relation String R).
  Proof.
    intros f g H x.
    specialize (H x x (reflexivity _)); assumption.
  Qed.
End String.

Section Iso.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSI : StringIso Char}
          {HSLP : StringLikeProperties Char} {HSIP : StringIsoProperties Char}.

  Lemma length_of_string_nil
  : length (of_string nil) = 0.
  Proof.
    apply no_first_char_empty.
    rewrite get_of_string; reflexivity.
  Qed.

  Lemma drop_of_string (n : nat) str
  : drop n (of_string str) =s of_string (List.drop n str).
  Proof.
    apply bool_eq_from_get.
    intro n'; rewrite get_drop', !get_of_string, nth_error_drop.
    reflexivity.
  Qed.

  Lemma take_of_string (n : nat) str
  : take n (of_string str) =s of_string (List.take n str).
  Proof.
    revert str; induction n; intros; simpl.
    { apply bool_eq_empty; rewrite ?take_length, ?drop_length; trivial.
      apply length_of_string_nil. }
    { apply bool_eq_from_get.
      intros_destruct.
      { destruct str as [|ch str]; simpl;
        repeat match goal with
                 | _ => progress simpl
                 | _ => reflexivity
                 | _ => progress rewrite ?get_take_lt, ?get_of_string, ?take_length, ?length_of_string_nil
                       by (reflexivity || omega)
               end. }
      { intro n'; rewrite !get_S.
        rewrite drop_take, !drop_of_string; simpl.
        rewrite NPeano.Nat.sub_0_r.
        destruct str; simpl;
        rewrite !IHn; simpl; trivial.
        destruct n; reflexivity. } }
  Qed.

  Lemma of_string_length str
  : length (of_string str) = List.length str.
  Proof.
    induction str as [|ch str IHstr].
    { apply no_first_char_empty.
      rewrite get_of_string; reflexivity. }
    { simpl; rewrite <- IHstr; clear IHstr.
      assert (H : of_string str =s drop 1 (of_string (ch :: str))) by (rewrite drop_of_string; reflexivity).
      rewrite H, drop_length.
      destruct (length (of_string (ch::str))) eqn:H'.
      { apply has_first_char_nonempty in H'.
        rewrite get_of_string in H'; simpl in H'.
        inversion H'. }
      { omega. } }
  Qed.

  Lemma is_char_of_string str ch
  : is_true (is_char (of_string str) ch) <-> str = (ch::nil).
  Proof.
    split; intro H;
    [ pose proof (length_singleton _ _ H) as H';
      rewrite of_string_length in H'
    | ];
    (destruct str as [|ch' [|ch'' str]];
     simpl in *; try discriminate);
    change (ch' :: nil) with (List.take 1 (ch'::nil)) in *;
    repeat match goal with
             | [ H : _ |- _ ] => progress rewrite <- ?take_of_string, ?get_of_string in H
             | _ => progress rewrite <- ?take_of_string, ?get_of_string
             | _ => progress simpl in *
             | [ H : is_true (is_char _ _) |- _ ] => apply get_0 in H
             | [ |- is_true (is_char _ _) ] => apply get_0
             | _ => progress unfold value in *
             | [ H : Some _ = Some _ |- _ ] => inversion_clear H
             | [ H : _::_ = _::_ |- _ ] => inversion_clear H
             | _ => reflexivity
           end.
  Qed.

  Lemma substring_of_string {n m str}
  : substring n m (of_string str) =s of_string (List.take m (List.drop n str)).
  Proof.
    rewrite <- take_of_string, <- drop_of_string; reflexivity.
  Qed.

  Lemma to_of_string str
  : to_string (of_string str) = str.
  Proof.
    induction str.
    { unfold fold, fold'.
      rewrite of_string_length; simpl.
      reflexivity. }
    { rewrite fold_recr.
      rewrite get_of_string; simpl.
      rewrite drop_of_string; simpl.
      rewrite IHstr.
      reflexivity. }
  Qed.

  Lemma of_to_string str
  : of_string (to_string str) =s str.
  Proof.
    remember (length str) as n eqn:H.
    revert str H; induction n; intros.
    { unfold fold.
      apply bool_eq_empty; rewrite <- H, ?of_string_length; reflexivity. }
    { rewrite fold_recr.
      apply bool_eq_from_get.
      intros [|n'].
      { destruct (get 0 str) eqn:H'.
        { rewrite get_of_string; reflexivity. }
        { apply no_first_char_empty in H'; congruence. } }
      { rewrite !get_S.
        rewrite <- (IHn (drop 1 str)) by (rewrite drop_length; omega).
        rewrite drop_of_string.
        destruct (get 0 str) eqn:H'; simpl.
        { reflexivity. }
        { apply no_first_char_empty in H'; congruence. } } }
  Qed.

  Lemma beq_of_string {s s'}
  : of_string s =s of_string s' <-> s = s'.
  Proof.
    rewrite <- beq_to_string, !to_of_string.
    reflexivity.
  Qed.
End Iso.

Ltac pose_string_like_for_lengths :=
  match goal with
  | [ H : context[length _ = ?n] |- _ ]
    => lazymatch n with
       | length _ => fail
       | _ => idtac
       end;
       lazymatch goal with
       | [ H' : length _ = n |- _ ] => fail
       | _ => destruct (strings_nontrivial n)
       end
  | [ H : @String ?Char ?HSLM -> ?T |- _ ]
    => is_closed T;
       lazymatch goal with
       | [ s : @String Char HSLM |- _ ] => fail
       | _ => destruct (@strings_nontrivial Char HSLM _ _ 0)
       end
  end.

Ltac simpl_string_like_no_setoid_step :=
  match goal with
  | [ H : length ?str = _, H' : context[length ?str] |- _ ] => rewrite H in H'
  | [ H : length ?str = _ |- context[length ?str] ] => rewrite H
  | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
  | _ => progress pose_string_like_for_lengths
  | [ H : forall str, length str = ?n -> ?T, H' : length ?str' = ?n |- _ ]
    => is_closed T; specialize (H str' H')
  | [ H : String -> ?T, H' : String |- _ ]
    => is_closed T; specialize (H H')
  | [ H : False |- _ ] => solve [ induction H | case H ]
  | [ H : forall str, length str = ?n |- _ ] => apply not_all_lengths in H
  | [ H : @length ?Char ?HSLM ?str = @length ?Char ?HSLM ?str' |- _ ]
    => first [ generalize dependent (@length Char HSLM str'); intros; subst; clear str'
             | generalize dependent (@length Char HSLM str); intros; subst; clear str ]
  | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length, ?Min.min_0_r, ?Min.min_0_l, ?Nat.sub_0_l in H
  | _ => progress rewrite ?take_length, ?drop_length, ?Min.min_0_r, ?Min.min_0_l, ?Nat.sub_0_l
  end.
Ltac simpl_string_like_step :=
  first [ progress simpl_string_like_no_setoid_step
        | progress setoid_subst_rel (@beq _ _ _) ].
Ltac simpl_string_like_no_setoid := repeat simpl_string_like_no_setoid_step.
Ltac simpl_string_like := repeat simpl_string_like_step.
