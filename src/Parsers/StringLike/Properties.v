(** * Theorems about string-like types *)
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Program.Basics.
Require Import Coq.Arith.Lt.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import ADTSynthesis.Parsers.StringLike.Core ADTSynthesis.Common.Le ADTSynthesis.Common.UIP.
Require Import ADTSynthesis.Common.Equality.
Require Import ADTSynthesis.Common.
Require Import ADTSynthesis.Common.Le.

Set Implicit Arguments.

Section String.
  Context {string} `{StringLikeProperties string}.

  (*Definition stringlike_dec (s1 s2 : String)
  : { s1 = s2 } + { s1 <> s2 }.
  Proof.
    case_eq (bool_eq s1 s2); intro H; [ left | right ].
    { apply bool_eq_correct; exact H. }
    { intro H'; apply bool_eq_correct in H'.
      generalize dependent (s1 =s s2)%string_like; clear; intros.
      abstract congruence. }
  Defined.

  Lemma stringlike_uip {s1 s2 : String}
        (p q : s1 = s2)
  : p = q.
  Proof.
    apply dec_eq_uip.
    apply stringlike_dec.
  Qed.*)

  Definition bool_eq_refl `{StringLikeProperties string} {x : String} : x =s x.
  Proof.
    reflexivity.
  Defined.

  Definition bool_eq_sym `{StringLikeProperties string} {x y : String} : ((x =s y) = (y =s x) :> bool)%string_like.
  Proof.
    case_eq (y =s x)%string_like; intro H';
    [
    | case_eq (x =s y)%string_like; intro H'' ].
    { apply (symmetry (R := (fun x y => x =s y))) in H'; assumption. }
    { apply (symmetry (R := (fun x y => x =s y))) in H''; hnf in H''.
      etransitivity; [ exact (eq_sym H'') | exact H' ]. }
    { reflexivity. }
  Defined.

  Definition bool_eq_trans `{StringLikeProperties string} {x y z : String} : (x =s y) -> (y =s z) -> (x =s z).
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

  (*Lemma NonEmpty_length
        (a : String)
        (H : a <> Empty _)
  : length a > 0.
  Proof.
    case_eq (length a); intro H'; try omega.
    apply Empty_length in H'; subst.
    destruct (H eq_refl).
  Qed.

  Local Ltac lt_nonempty_t :=
    repeat match goal with
             | [ H : _ ≤s _ |- _ ] => destruct H
             | [ H : _ |- _ ] => progress rewrite ?plus_O_n, <- ?length_correct in H
             | _ => progress rewrite ?plus_O_n, <- ?length_correct
             | _ => assumption
             | _ => intro
             | _ => progress subst
             | _ => omega
             | [ H : _ <> Empty _ |- _ ] => apply NonEmpty_length in H
           end.

  Lemma strle_to_lt_nonempty_r
        {a b c : String}
        (H : a <> Empty _)
        (H' : a ++ b ≤s c)
  : length b < length c.
  Proof. lt_nonempty_t. Qed.

  Lemma strle_to_lt_nonempty_l
        {a b c : String}
        (H : b <> Empty _)
        (H' : a ++ b ≤s c)
  : length a < length c.
  Proof. lt_nonempty_t. Qed.*)

  Lemma str_seq_lt_false
        {a b : String}
        (H0' : length a < length b)
        (H' : a =s b)
  : False.
  Proof.
    rewrite H' in H0'.
    eapply lt_irrefl; eassumption.
  Qed.

  (*Lemma neq_some_none_state_val {P}
        {s1 s2 : StringWithSplitState String (fun x => option (P x))}
        (H : s1 = s2)
  : match state_val s1, state_val s2 with
      | None, Some _ => False
      | Some _, None => False
      | _, _ => True
    end.
  Proof.
    destruct H.
    destruct (state_val s1); exact I.
  Qed.

  Definition string_val_path {CharType String A}
             {s0 s1 : @StringWithSplitState CharType String A}
             (H : s0 = s1)
  : string_val s0 = string_val s1
    := f_equal (@string_val _ _ _) H.

  Definition state_val_path {A}
             {s0 s1 : @StringWithSplitState CharType String A}
             (H : s0 = s1)
  : eq_rect _ _ (state_val s0) _ (string_val_path H) = state_val s1.
  Proof.
    destruct H; reflexivity.
  Defined.

  (** This proof would be so much easier to read if we were using HoTT conventions, tactics, and lemmas. *)
  Lemma lift_StringWithSplitState_injective {A B}
        (s0 s1 : @StringWithSplitState CharType String A)
        (lift : forall s, A s -> B s)
        (lift_injective : forall s a1 a2, lift s a1 = lift s a2 -> a1 = a2)
        (H : lift_StringWithSplitState s0 (lift _) = lift_StringWithSplitState s1 (lift _))
  : s0 = s1.
  Proof.
    pose proof (state_val_path H) as H'.
    generalize dependent (string_val_path H); clear H.
    destruct s0, s1; simpl in *.
    intro H'.
    destruct H'; simpl.
    intro H'.
    apply lift_injective in H'.
    destruct H'.
    reflexivity.
  Qed.

  Lemma lift_StringWithSplitState_pair_injective {A A' B B'}
        (s0 s1 : @StringWithSplitState CharType String A * @StringWithSplitState CharType String A')
        (lift : forall s, A s -> B s)
        (lift' : forall s, A' s -> B' s)
        (lift_injective : forall s a1 a2, lift s a1 = lift s a2 -> a1 = a2)
        (lift'_injective : forall s a1 a2, lift' s a1 = lift' s a2 -> a1 = a2)
        (H : (lift_StringWithSplitState (fst s0) (lift _),
              lift_StringWithSplitState (snd s0) (lift' _))
             =
             (lift_StringWithSplitState (fst s1) (lift _),
              lift_StringWithSplitState (snd s1) (lift' _)))
  : s0 = s1.
  Proof.
    pose proof (f_equal (@fst _ _) H) as H0.
    pose proof (f_equal (@snd _ _) H) as H1.
    clear H; simpl in *.
    apply lift_StringWithSplitState_injective in H0; [ | assumption.. ].
    apply lift_StringWithSplitState_injective in H1; [ | assumption.. ].
    apply injective_projections; assumption.
  Qed.

  Lemma in_lift_pair_StringWithSplitState_iff_injective {A A' B B'}
        {s0s1 : @StringWithSplitState CharType String A * @StringWithSplitState CharType String A'}
        {lift : forall s, A s -> B s}
        {lift' : forall s, A' s -> B' s}
        {lift_injective : forall s a1 a2, lift s a1 = lift s a2 -> a1 = a2}
        {lift'_injective : forall s a1 a2, lift' s a1 = lift' s a2 -> a1 = a2}
        {ls : list (StringWithSplitState String A * StringWithSplitState String A')}
        (H : List.In (lift_StringWithSplitState (fst s0s1) (lift _),
                      lift_StringWithSplitState (snd s0s1) (lift' _))
                     (List.map (fun s0s1 =>
                                  (lift_StringWithSplitState (fst s0s1) (lift _),
                                   lift_StringWithSplitState (snd s0s1) (lift' _)))
                               ls))
  : List.In s0s1 ls.
  Proof.
    eapply in_map_iff_injective; [ | exact H ].
    simpl; intro.
    apply lift_StringWithSplitState_pair_injective; assumption.
  Qed.*)

  (*Lemma SplitAt0 (s : String) : SplitAt 0 s = (Empty _, s).
  Proof.
    rewrite <- SplitAt_concat_correct.
    rewrite length_Empty.
    rewrite LeftId.
    reflexivity.
  Qed.

  Lemma SplitAtPastEnd_length_fst {n} {s : String} (H : length s <= n) : length (fst (SplitAt n s)) = length s.
  Proof.
    rewrite SplitAtlength_correct.
    auto with arith.
  Qed.


  Lemma SplitAtPastEnd' {n} (s : String) (H : length s <= n) : snd (SplitAt n s) = Empty _.
  Proof.
    apply Empty_length.
    pose proof (f_equal (fun l => l + length (snd (SplitAt n s))) (SplitAtPastEnd_length_fst H)) as H0.
    simpl in *.
    rewrite length_correct in H0.
    rewrite SplitAt_correct in H0.
    omega.
  Qed.

  Lemma SplitAt_gives_Empty {n} {s : String}
  : snd (SplitAt n s) = Empty _ -> fst (SplitAt n s) = s.
  Proof.
    intro H.
    pose proof (SplitAt_correct String n s) as H'.
    rewrite H in H'; simpl in *.
    rewrite RightId in H'.
    assumption.
  Qed.

  Lemma SplitAtPastEnd {n} {s : String} (H : length s <= n) : SplitAt n s = (s, Empty _).
  Proof.
    apply injective_projections; simpl;
    [ apply SplitAt_gives_Empty | ];
    apply SplitAtPastEnd'; assumption.
  Qed.

  Lemma SplitAtEnd {s : String} : SplitAt (length s) s = (s, Empty _).
  Proof.
    apply SplitAtPastEnd.
    reflexivity.
  Qed.

  Lemma SplitAt_min_length {n} {s : String} : SplitAt (min (length s) n) s = SplitAt n s.
  Proof.
    apply Min.min_case_strong; intro H.
    { rewrite SplitAtEnd, (SplitAtPastEnd H); reflexivity. }
    { reflexivity. }
  Qed.

  Lemma SplitAtS {n} ch (s : String)
  : SplitAt (S n) ([[ ch ]] ++ s) = ([[ ch ]] ++ fst (SplitAt n s), snd (SplitAt n s)).
  Proof.
    rewrite <- SplitAt_concat_correct.
    rewrite <- length_correct.
    rewrite Singleton_length; simpl.
    rewrite SplitAtlength_correct.
    rewrite Associativity.
    rewrite SplitAt_correct.
    replace (S (min (length s) n)) with (min (length ([[ ch ]] ++ s)) (S n)).
    { rewrite SplitAt_min_length; reflexivity. }
    { rewrite <- length_correct, Singleton_length; reflexivity. }
  Qed.

  Lemma SplitAtEmpty {n} : SplitAt n (Empty String) = (Empty _, Empty _).
  Proof.
    rewrite SplitAtPastEnd; trivial.
    rewrite length_Empty; auto with arith.
  Qed.*)
End String.
