(** * Build a table for the next binop at a given level *)
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Common.
Require Import Fiat.Common.OptionFacts.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.

Set Implicit Arguments.

Section make_table.
  Context {Char} {HSL : StringLike Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  (** We build a table to tell us where to split.
      For each character, we store an [option nat], and keep a
      transient [list nat].

      We store where the next '+' at the current level of
      parenthetization is.  The transient list stores where the
      next '+' is for higher levels. *)

  Definition list_of_next_bin_ops'_step'
    := (fun ch table_higher_ops =>
          let next_ops := map (option_map S) (nth 0 table_higher_ops nil) in
          let '(cur_mark, new_higher_ops) := (nth 0 next_ops None, tl next_ops) in
          ((if is_bin_op ch
            then Some 0 :: new_higher_ops
            else if is_close ch
                 then None :: next_ops
                 else if is_open ch
                      then new_higher_ops
                      else next_ops))).

  Definition list_of_next_bin_ops'_step
    := (fun ch table_higher_ops =>
          list_of_next_bin_ops'_step' ch table_higher_ops :: table_higher_ops).

  Definition list_of_next_bin_ops' (str : String)
  : list (list (option nat))
    := fold
         list_of_next_bin_ops'_step
         nil
         str.

  Definition list_of_next_bin_ops (str : String)
    := map (fun ls => nth 0 ls None) (list_of_next_bin_ops' str).

  Lemma list_of_next_bin_ops'_nil (str : String) (H : length str = 0)
  : list_of_next_bin_ops' str = nil.
  Proof.
    apply fold_nil; assumption.
  Qed.

  Lemma list_of_next_bin_ops'_recr {HSLP : StringLikeProperties Char} (str : String)
  : list_of_next_bin_ops' str
    = match get 0 str with
        | Some ch => list_of_next_bin_ops'_step ch (list_of_next_bin_ops' (drop 1 str))
        | None => nil
      end.
  Proof.
    apply fold_recr.
  Qed.

  Global Instance list_of_next_bin_ops'_Proper {HSLP : StringLikeProperties Char}
  : Proper (beq ==> eq) list_of_next_bin_ops'.
  Proof.
    apply fold_Proper.
  Qed.

  Typeclasses Opaque list_of_next_bin_ops'.
  Opaque list_of_next_bin_ops'.

  Lemma list_of_next_bin_ops'_length' {HSLP : StringLikeProperties Char} str
  : List.length (list_of_next_bin_ops' str) = length str.
  Proof.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len.
    revert str.
    induction len; simpl; intros str H'.
    { rewrite list_of_next_bin_ops'_nil by assumption; reflexivity. }
    { specialize (IHlen (drop 1 str)).
      rewrite drop_length, H' in IHlen.
      simpl in IHlen.
      specialize (IHlen (NPeano.Nat.sub_0_r _)).
      rewrite list_of_next_bin_ops'_recr.
      destruct (singleton_exists (take 1 str)) as [ch H''].
      { rewrite take_length, H'; reflexivity. }
      { erewrite (fun H => proj1 (get_0 _ H)) by eassumption.
        unfold list_of_next_bin_ops'_step.
        repeat match goal with
                 | _ => reflexivity
                 | _ => rewrite IHlen
                 | _ => progress simpl
                 | [ |- context[if ?f ch then _ else _] ] => destruct (f ch)
               end. } }
  Qed.

  Lemma list_of_next_bin_ops'_drop {HSLP : StringLikeProperties Char} str n
  : List.Operations.drop n (list_of_next_bin_ops' str) = list_of_next_bin_ops' (drop n str).
  Proof.
    revert str.
    induction n as [|n]; simpl; intros.
    { rewrite drop_0; reflexivity. }
    { replace (S n) with (n + 1) by omega.
      rewrite <- drop_drop, <- IHn; clear IHn.
      set (len := length str).
      generalize (eq_refl : length str = len).
      clearbody len.
      revert str n.
      induction len; simpl; intros str n H'.
      { rewrite !list_of_next_bin_ops'_nil by (rewrite ?drop_length; omega).
        destruct n; reflexivity. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length, H' in IHlen.
        simpl in IHlen.
        rewrite NPeano.Nat.sub_0_r in IHlen.
        specialize (IHlen (pred n) eq_refl).
        rewrite list_of_next_bin_ops'_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H'; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          reflexivity. } } }
  Qed.

  Definition index_points_to_binop (offset index : nat) (str : String)
    := for_first_char (drop (offset + index) str) is_bin_op.

  Lemma index_points_to_binop_spec {HSLP : StringLikeProperties Char} offset index str ch
        (H : (take 1 (drop (offset + index) str) ~= [ ch ])%string_like)
  : index_points_to_binop offset index str <-> is_bin_op ch.
  Proof.
    unfold index_points_to_binop.
    rewrite (for_first_char__take 0).
    rewrite <- for_first_char_singleton; [ reflexivity | assumption ].
  Qed.

  Lemma index_points_to_binop_S1 {HSLP : StringLikeProperties Char} offset index str
  : index_points_to_binop (S offset) index str <-> index_points_to_binop offset index (drop 1 str).
  Proof.
    unfold index_points_to_binop.
    rewrite ?drop_drop, !NPeano.Nat.add_1_r; simpl.
    reflexivity.
  Qed.

  Lemma index_points_to_binop_S2 {HSLP : StringLikeProperties Char} offset index str
  : index_points_to_binop offset (S index) str <-> index_points_to_binop offset index (drop 1 str).
  Proof.
    rewrite <- index_points_to_binop_S1.
    unfold index_points_to_binop.
    replace (offset + S index) with (S offset + index) by omega.
    reflexivity.
  Qed.

  Definition index_not_points_to_binop (offset index : nat) (str : String)
    := for_first_char (drop (offset + index) str) (fun ch => is_bin_op ch = false).

  Lemma index_not_points_to_binop_spec {HSLP : StringLikeProperties Char} offset index str ch
        (H : (take 1 (drop (offset + index) str) ~= [ ch ])%string_like)
  : index_not_points_to_binop offset index str <-> is_bin_op ch = false.
  Proof.
    unfold index_not_points_to_binop.
    rewrite (for_first_char__take 0).
    rewrite <- for_first_char_singleton; [ reflexivity | assumption ].
  Qed.

  Lemma index_not_points_to_binop_S1 {HSLP : StringLikeProperties Char} offset index str
  : index_not_points_to_binop (S offset) index str <-> index_not_points_to_binop offset index (drop 1 str).
  Proof.
    unfold index_not_points_to_binop.
    rewrite ?drop_drop, !NPeano.Nat.add_1_r; simpl.
    reflexivity.
  Qed.

  Lemma index_not_points_to_binop_S2 {HSLP : StringLikeProperties Char} offset index str
  : index_not_points_to_binop offset (S index) str <-> index_not_points_to_binop offset index (drop 1 str).
  Proof.
    rewrite <- index_not_points_to_binop_S1.
    unfold index_not_points_to_binop.
    replace (offset + S index) with (S offset + index) by omega.
    reflexivity.
  Qed.

  Lemma index_not_points_to_binop_nil {HSLP : StringLikeProperties Char}
        (offset index : nat) (str : String) (H : length str <= offset + index)
  : index_not_points_to_binop offset index str.
  Proof.
    unfold index_not_points_to_binop.
    apply for_first_char_nil.
    rewrite drop_length; omega.
  Qed.

  Definition list_of_next_bin_ops_spec'' (level : nat) (table : list (option nat)) (str : String) offset idx
    := (nth offset table None = Some idx
        -> index_points_to_binop offset idx str
           /\ paren_balanced_hiding' (take idx (drop offset str)) level)
       /\ (nth offset table None = None
           -> paren_balanced' (take idx (drop offset str)) level
           -> index_not_points_to_binop offset idx str).

  Definition list_of_next_bin_ops_spec' (level : nat) (table : list (option nat)) (str : String)
    := forall offset idx, list_of_next_bin_ops_spec'' level table str offset idx.

  Definition list_of_next_bin_ops_spec
    := list_of_next_bin_ops_spec' 0.

  Definition list_of_next_bin_ops_spec''_S_offset {HSLP : StringLikeProperties Char} {level table str offset t' idx}
             (H : list_of_next_bin_ops_spec'' level table (drop 1 str) offset idx)
  : list_of_next_bin_ops_spec'' level (t'::table) str (S offset) idx.
  Proof.
    unfold list_of_next_bin_ops_spec'' in *; simpl in *.
    rewrite !index_points_to_binop_S1.
    rewrite !index_not_points_to_binop_S1.
    rewrite drop_drop, NPeano.Nat.add_1_r in H.
    assumption.
  Qed.

  Local Ltac t_eq :=
    repeat match goal with
             | _ => assumption
             | _ => progress simpl in *
             | _ => progress subst
             | [ |- is_true true ] => reflexivity
             | [ H : None = Some _ |- _ ] => solve [ inversion H ]
             | [ H : Some _ = None |- _ ] => solve [ inversion H ]
             | [ H : 0 = S _ |- _ ] => solve [ inversion H ]
             | [ H : S _ = 0 |- _ ] => solve [ inversion H ]
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
             | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
             | [ H : option_map _ ?x = None |- _ ] => destruct x eqn:?; simpl in H
             | _ => progress split_and
             | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
               => assert (ch = ch') by (eapply singleton_unique; eassumption);
                 clear H'
             | [ H : ?x = true |- context[?x] ] => rewrite H
             | [ H : is_true ?x |- context[?x] ] => rewrite H
             | [ H : ?x = S _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
             | [ H : option_map _ ?x = None |- _ ] => destruct x eqn:?; simpl in H
             | [ H : forall x, _ = _ -> @?T x |- _ ] => specialize (H _ eq_refl)
             | [ |- and _ _ ] => split
             | _ => progress intros
           end.

  Local Ltac t :=
    repeat match goal with
             | _ => progress t_eq
             | [ |- index_points_to_binop 0 0 _ ] => eapply index_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
             | _ => rewrite paren_balanced_hiding'_nil by (rewrite take_length; reflexivity)
             | [ H : _ |- _ ] => progress rewrite ?nth_tl, ?drop_0 in H
             | _ => progress rewrite ?drop_0
             | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls None n)
             | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls nil n)
             | [ |- index_points_to_binop _ (S _) _ ] => rewrite index_points_to_binop_S2
           end.

  Definition list_of_next_bin_ops_spec''_0_0_bin_op {HSLP : StringLikeProperties Char} {table str idx ch}
             (H_ch : (take 1 str ~= [ch])%string_like)
             (H : is_bin_op ch)
  : list_of_next_bin_ops_spec'' 0 (Some 0 :: table) str 0 idx.
  Proof.
    hnf; t.
  Qed.

  (*Definition list_of_next_bin_ops_spec''_S__0_bin_op {HSLP : StringLikeProperties Char} {table table' str idx n ch}
             (IHlen : forall n idx : nat,
                        list_of_next_bin_ops_spec''
                          n
                          (map (fun ls : list (option nat) => nth n ls None)
                               (list_of_next_bin_ops' (drop 1 str)))
                          (drop 1 str) 0 idx)
             (H_ch : (take 1 str ~= [ch])%string_like)
             (H : is_bin_op ch)
  : list_of_next_bin_ops_spec''
      (S n)
      (nth n
           (tl
              (map (option_map S)
                   (nth 0 table []))) None
           :: table')
      str 0 idx.
  Proof.
    specialize (fun n => IHlen n (pred idx)).
    hnf; t.
    unfold list_of_next_bin_ops_spec'' in *; simpl in *.
    t.*)


  (*Lemma list_of_next_bin_ops_spec''_step {HSLP : StringLikeProperties Char} {str ch n offset idx ls}
        (H'' : (take 1 str ~= [ch])%string_like)
        (IH : list_of_next_bin_ops_spec''
                n
                (map (fun ls : list (option nat) => nth n ls None) ls)
                (drop 1 str) offset idx)
  : list_of_next_bin_ops_spec''
      n
      (nth n
           (list_of_next_bin_ops'_step' ch ls)
           None
           :: (map (fun ls : list (option nat) => nth n ls None) ls))
      str (S offset) idx.
  Proof.
    unfold list_of_next_bin_ops'_step'.
    apply list_of_next_bin_ops_spec''_S_offest; assumption.
  Qed.*)

  Lemma list_of_next_bin_ops'_satisfies_spec {HSLP : StringLikeProperties Char} (str : String)
  : forall n,
      list_of_next_bin_ops_spec' n (map (fun ls => nth n ls None) (list_of_next_bin_ops' str)) str.
  Proof.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len; revert str.
    induction len.
    { intros ??.
      rewrite list_of_next_bin_ops'_nil by assumption; simpl.
      intros [] []; split; simpl; intros; try congruence;
      try (apply index_not_points_to_binop_nil; omega). }
    { intros str H.
      specialize (IHlen (drop 1 str)).
      specialize_by ltac:(rewrite drop_length; omega).
      rewrite list_of_next_bin_ops'_recr.
      destruct (singleton_exists (take 1 str)) as [ch H''];
        [ rewrite take_length, H; reflexivity
        | ].
      rewrite (proj1 (get_0 _ _) H'').
      intros n [|offset] idx;
        [ specialize (fun n idx => IHlen n 0 idx)
        | unfold list_of_next_bin_ops'_step; simpl;
          apply list_of_next_bin_ops_spec''_S_offset, IHlen ].
      unfold list_of_next_bin_ops'_step; simpl.
      unfold list_of_next_bin_ops'_step'.
      repeat match goal with
               | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
             end.
      { generalize dependent (list_of_next_bin_ops' (drop 1 str)); intro table; intros.
        destruct n as [|n].
        { eapply list_of_next_bin_ops_spec''_0_0_bin_op; eassumption. }
        { revert idx; induction n as [|n IHn]; simpl; intro idx.
          unfold list_of_next_bin_ops_spec'' in *.
          specialize (IHlen 1).
          t.
          (*
          specialize
cbv delta [list_of_next_bin_ops_spec'']; simpl.


        { simpl

        unfold
      rewrite paren_balanced_hiding'_recr.
      unfold list_of_next_bin_ops'_step.
      repeat match goal with
               | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
             end.
      { split.
        intro; split.
        { specialize (IHlen n (pred idx)).
          unfold paren_balanced_hiding'_step, paren_balanced'_step.
          Timeout 5 repeat match goal with
                             | _ => assumption
                             | [ |- is_true true ] => reflexivity
                             | [ H : None = Some _ |- _ ] => solve [ inversion H ]
                             | [ H : Some _ = None |- _ ] => solve [ inversion H ]
                             | [ H : 0 = S _ |- _ ] => solve [ inversion H ]
                             | [ H : S _ = 0 |- _ ] => solve [ inversion H ]
                             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                             | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
                             | [ H : option_map _ ?x = None |- _ ] => destruct x eqn:?; simpl in H
                             | _ => progress split_and
                             | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
                               => assert (ch = ch') by (eapply singleton_unique; eassumption);
                                 clear H'
                             | [ H : ?x = true |- context[?x] ] => rewrite H
                             | [ H : is_true ?x |- context[?x] ] => rewrite H
                             | [ H : ?x = S _, H' : context[?x] |- _ ] => rewrite H in H'
                             | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
                             | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
                             | _ => rewrite paren_balanced_hiding'_nil by (rewrite take_length; reflexivity)
                             | _ => rewrite has_first_char_nonempty by (rewrite take_length; reflexivity)
                             | _ => progress subst
                             | _ => progress simpl in *
                             | [ H : appcontext[match ?e with 0 => _ | _ => _ end] |- _ ] => destruct e
                             | [ |- appcontext[match ?e with 0 => _ | _ => _ end] ] => destruct e
                             | [ |- and _ _ ] => split
                             | _ => progress intros
                             | [ |- index_points_to_binop 0 0 _ ] => eapply index_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
                             | [ |- index_not_points_to_binop 0 0 _ ] => eapply index_not_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
                             | [ |- index_points_to_binop _ (S _) _ ] => rewrite index_points_to_binop_S2
                             | [ |- index_not_points_to_binop _ (S _) _ ] => rewrite index_not_points_to_binop_S2
                             | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls None n)
                             | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls nil n)
                             | _ => progress specialize_by ltac:(exact eq_refl)
                             | [ |- appcontext[match get 0 ?str with _ => _ end] ]
                               => erewrite (proj1 (get_0 str _)) by eassumption
                             | [ |- appcontext[match get 0 ?str with _ => _ end] ] => destruct (get 0 str) eqn:?
                             | [ H : get 0 _ = Some _ |- _ ] => apply get_0 in H
                             | [ H : get 0 _ = None |- _ ] => apply no_first_char_empty in H
                             | [ H : is_true (take 0 _ ~= [ _ ])%string_like |- _ ] => apply length_singleton in H
                             | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?nth_tl, ?drop_0, ?take_take, ?take_length in H
                             | _ => progress rewrite ?nth_tl, ?drop_0, ?get_take_lt, ?drop_take, ?NPeano.Nat.sub_0_r by omega
                           end.
rewrite H0 in H2.

Focus 3.
repeat match goal with

       end.
Search
rewrite H3.

                 | [ |- index_not_points_to_binop _ ?x _ ] => is_var x; destruct x
Focus 2.
SearchAbout (_ - 0).
Show Profile.
        match goal with
        end.
Typeclasses eauto := debug.
Start Profiling.
Timeout 5       repeat   match goal with
                 | _ => assumption
                 | [ |- is_true true ] => reflexivity
                 | [ H : None = Some _ |- _ ] => solve [ inversion H ]
                 | [ H : Some _ = None |- _ ] => solve [ inversion H ]
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                 | _ => progress split_and
                 | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r in H
                 | _ => progress rewrite ?nth_tl, ?drop_0, ?get_take_lt by omega
                 | _ => rewrite paren_balanced_hiding'_nil by (rewrite take_length; reflexivity)
                 | _ => rewrite has_first_char_nonempty by (rewrite take_length; reflexivity)
                 | _ => progress subst
                 | _ => progress simpl in *
                 | [ |- appcontext[match ?e with 0 => _ | _ => _ end] ] => destruct e eqn:?
                 | [ |- and _ _ ] => split
                 | _ => progress intros
                 | [ |- index_points_to_binop 0 0 _ ] => eapply index_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
                 | [ |- index_points_to_binop _ (S _) _ ] => rewrite index_points_to_binop_S2
                 | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls None n)
                 | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls nil n)
                 | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
                 | _ => progress specialize_by ltac:(exact eq_refl)
               end.
Timeout 5 try timeout 2 rewrite drop_0.
unfold
rewrite drop_0.
Show Profile.
        5:match goal with
                         | [ |- appcontext[match get 0 ?str with _ => _ end] ]
                           => erewrite (proj1 (get_0 str _)) by eassumption
                       end.
        .
        2:rewrite take_take; apply

.



pose (map_nth).
        .
SearchAbout (_ + 1 = S _).
        simpl.
        intros n offset idx; split; revert n offset idx.
        { intros n [|offset]; revert n; simpl.
          { specialize (fun n => IHlen n 0).
            setoid_rewrite drop_0.
            setoid_rewrite drop_0 in IHlen.
            split_and.
            intros n idx.
            { intro H'; split;
              [ revert n idx H'
              | destruct idx as [|[|idx]];
                [ simpl(*;
                  rewrite paren_balanced_hiding'_nil by (rewrite ?take_length, ?drop_length; reflexivity);
                  reflexivity*)
                | simpl
                (*rewrite paren_balanced_hiding'_nil by (rewrite ?take_length, ?drop_length; reflexivity);
                  reflexivity*)
                | simpl;
                  rewrite paren_balanced_hiding'_recr; unfold paren_balanced_hiding'_step, paren_balanced'_step;
                  erewrite (proj1 (get_0 _ _)); [ | rewrite take_take; simpl; eassumption ];
                  revert n idx H' ] ];
              repeat match goal with
                       | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                     end;
              try
                solve [
                  intros [|n];
                  repeat
                    match goal with
                      | _ => intro
                      | _ => progress subst
                      | _ => progress simpl in *
                      | _ => assumption
                      | _ => reflexivity
                      | _ => congruence
                      | [ H : None = Some _ |- _ ] => solve [ inversion H ]
                      | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                      | [ H : get 0 _ = Some _ |- _ ] => apply get_0 in H
                      | [ |- get 0 _ = Some _ ] => apply get_0
                      | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
                        => assert (ch = ch') by (eapply singleton_unique; eassumption);
                          clear H'
                      | [ H : nth _ (tl _) _ = _ |- _ ] => rewrite nth_tl in H
                      | [ H : nth ?n (map ?f ?ls) _ = _ |- _ ] => revert H; simpl rewrite (map_nth f ls None n)
                      | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
                      | [ |- get ?n _ = _ ] => not constr_eq n 0; rewrite (get_drop (n := n))
                      | [ H : get ?n _ = _ |- _ ] => not constr_eq n 0; rewrite (get_drop (n := n)) in H
                      | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?drop_take, ?NPeano.Nat.sub_0_r
                      | [ |- _ /\ _ ] => split
                      | [ |- _ \/ _ ] => left; reflexivity
                      | [ |- S _ = 0 \/ _ ] => right
                      | [ H : forall a b c, _ /\ _ |- _ ]
                        => pose proof (fun a b c => proj1 (H a b c));
                          pose proof (fun a b c => proj2 (H a b c));
                          clear H
                      | [ H : context[nth ?n (map (fun ls' => nth _ ls' None) ?ls) _] |- _ ]
                        => let H' := fresh in
                           pose proof (fun a => map_nth (fun ls' => nth a ls' None) ls nil n) as H';
                             simpl in H';
                             match goal with
                               | [ H'' : _ |- _ ] => rewrite <- H' in H''
                             end;
                             clear H'
                      | [ IHlen : _ |- _ ] => eapply IHlen; [ eassumption | ]
                      | [ H : _ \/ _ |- _ ] => destruct H
                      | [ |- is_true (paren_balanced_hiding' _ _) ] => rewrite paren_balanced_hiding'_nil by (rewrite ?take_length, ?drop_length; reflexivity)
                      | [ H : context[match ?n with 0 => None | S _ => @None ?A end] |- _ ]
                        => replace (match n with 0 => None | S _ => @None A end) with (@None A) in H by (destruct n; reflexivity)
                      | [ IHlen : forall a b, nth _ (map _ (list_of_next_bin_ops' _)) None = Some _ -> _,
                            H : nth _ (map _ (list_of_next_bin_ops' _)) None = Some _ |- _ ]
                        => specialize (IHlen _ _ H)
                      | _ => solve [ eauto using paren_balanced_hiding'_S with nocore ]
                      | [ |- index_points_to_binop _ _ _ ] => eapply index_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
                      | [ |- index_points_to_binop _ (S _) _ ] => rewrite index_points_to_binop_S2
                    end
                | repeat
                    match goal with
                      | [ H : context[if ?e then _ else _] |- _ ] => destruct e eqn:?
                      | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                      | [ H : context[nth ?n (_ :: _) _] |- _ ] => is_var n; destruct n
                      | _ => progress simpl in *
                      | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                      | _ => congruence
                      | [ |- is_true (paren_balanced_hiding' (take 1 _) _) ]
                        => rewrite paren_balanced_hiding'_recr
                      | _ => rewrite get_take_lt by omega
                      | _ => erewrite (proj1 (get_0 _ _)) by eassumption
                      | _ => progress unfold paren_balanced_hiding'_step
                      | _ => progress unfold paren_balanced'_step
                      | [ H : ?x = true |- context[?x] ] => rewrite H
                      | [ H : ?x = false |- context[?x] ] => rewrite H
                      | _ => rewrite !drop_take, !paren_balanced_hiding'_nil
                            by (rewrite take_length; reflexivity)
                    end ]. } }
          { intros n idx H'.
            rewrite index_points_to_binop_S1.
            specialize (IHlen n offset idx).
            destruct IHlen as [IHlen ?].
            specialize (IHlen H').
            destruct IHlen as [IHlen0 IHlen1].
            split; [ exact IHlen0 | ].
            rewrite drop_drop, NPeano.Nat.add_1_r in IHlen1.
            exact IHlen1. } }
        { unfold list_of_next_bin_ops_spec' in IHlen.
          pose proof (fun n offset idx => proj2 (IHlen n offset idx)) as IHlen1.
          clear IHlen.
          intros n offset idx.
          specialize (fun n => IHlen1 n (pred offset)).
          unfold list_of_next_bin_ops'_step.
          rewrite paren_balanced'_recr.
          repeat match goal with
                   | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                 end.
          { specialize (IHlen1 n).
            destruct offset as [|offset].
            { destruct n as [|n]; simpl in *; [ intros; congruence | ].
              repeat match goal with
                       | _ => progress simpl in *
                       | [ |- index_not_points_to_binop _ ?x _ ] => is_var x; destruct x
                       | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls nil n); intro
                       | [ |- context[nth ?n (map ?f ?ls) _] ] => simpl rewrite (map_nth f ls None n)
                       | [ H : context[index_not_points_to_binop _ _ (drop 1 _)] |- _ ]
                         => setoid_rewrite <- index_not_points_to_binop_S2 in H
                       | [ H : context[drop 0 _] |- _ ] => setoid_rewrite drop_0 in H
                       | [ H : context[get 0 (take 0 _)] |- _ ]
                         => rewrite has_first_char_nonempty in H by (rewrite take_length; reflexivity)
                       | _ => progress rewrite ?nth_tl, ?option_map_None, ?drop_0
                       | _ => progress intros
                       | _ => solve [ eauto with nocore ]
                     end.
              .

              match goal with
                | [ |- index_not_points_to_binop _ _ _ ] => eapply index_not_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
                | [ |- index_not_points_to_binop _ (S _) _ ] => rewrite index_not_points_to_binop_S2

              end.
Focus 2.
eapply IHlen1.
assumption.
simpl in *.
assumption.

              eapply IHlen1.
              eauto with nocore.


SearchAbout option_map.
              simpl in
              pose (@map_nth).

              SearchAbout nth tl.
          intros n [|offset].
          {
            { simpl map.
              simpl nth.
              destruct n; [ intros; congruence | ].


          setoid_rewrite paren_balanced'_recr in IHlen.

          {
            unfold paren_balanced'_step.
            revert n.
            Local Ltac clean :=
              repeat match goal with
                       | [ H : ?x = ?x |- _ ] => clear H
                       | [ H1 : ?T, H2 : ?T |- _ ] => clear H2
                     end.
Start Profiling.
            intros [|n].
            { repeat match goal with
                       (*| _ => progress clean*)
                       | [ H : None = Some _ |- _ ] => solve [ inversion H ]
                       | [ H : Some _ = None |- _ ] => solve [ inversion H ]
                       | [ H : 0 = S _ |- _ ] => solve [ inversion H ]
                       | [ H : S _ = 0 |- _ ] => solve [ inversion H ]
                       | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                       | _ => progress intros
                       | _ => progress subst
                       | _ => assumption
                       | [ |- _ = _ ] => reflexivity
                       (*| _ => congruence*)
                       | [ H : context[index_not_points_to_binop _ _ (drop 1 _)] |- _ ]
                         => setoid_rewrite <- index_not_points_to_binop_S2 in H
                       | [ H : is_true (take 0 _ ~= [ _ ])%string_like |- _ ] => apply length_singleton in H
                       | [ H : get 0 _ = Some _ |- _ ] => apply get_0 in H
                       | [ H : context[drop _ (take _ _)] |- _ ] => rewrite !drop_take in H
                       | [ H : context[take _ (take _ _)] |- _ ] => rewrite !take_take in H
                       | [ H : context[length (take _ _)] |- _ ] => rewrite !take_length in H
                       | [ H : context[_ - 0] |- _ ] => rewrite !NPeano.Nat.sub_0_r in H
                       | _ => progress simpl in *
                       | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
                       (*| [ |- index_not_points_to_binop _ ?x _ ] => is_var x; destruct x*)
                     end.
eapply H1; simpl; [ | eassumption ].
SearchAbout (_ - 0).
Show Profile.

rewrite list_of_next_bin_ops'_nil in H0.

            eapply H1; [ | simpl; rewrite take_drop, NPeano.Nat.add_1_r; eassumption ].
                       | [ |- get 0 _ = Some _ ] => apply get_0
                       | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
                         => assert (ch = ch') by (eapply singleton_unique; eassumption);
                           clear H'
                       | [ H : nth _ (tl _) _ = _ |- _ ] => rewrite nth_tl in H
                       | [ H : nth ?n (map ?f ?ls) _ = _ |- _ ] => revert H; simpl rewrite (map_nth f ls None n)
                       | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
                       | [ |- get ?n _ = _ ] => not constr_eq n 0; rewrite (get_drop (n := n))
                       | [ H : get ?n _ = _ |- _ ] => not constr_eq n 0; rewrite (get_drop (n := n)) in H
                       | [ H : _ |- _ ] => progress rewrite ?take_take, ?take_length in H
                       | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?drop_take, ?NPeano.Nat.sub_0_r
                       | [ |- _ /\ _ ] => split
                       | [ |- _ \/ _ ] => left; reflexivity
                       | [ |- S _ = 0 \/ _ ] => right
                       | _ => progress split_and
                       | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
                       | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                       | [ H : context[nth ?n (map (fun ls' => nth _ ls' None) ?ls) _] |- _ ]
                         => let H' := fresh in
                            pose proof (fun a => map_nth (fun ls' => nth a ls' None) ls nil n) as H';
                              simpl in H';
                              match goal with
                                | [ H'' : _ |- _ ] => rewrite <- H' in H''
                              end;
                              clear H'
                       | [ H : pred ?x = S _ |- _ ] => is_var x; destruct x
                       | [ IHlen : _ |- _ ] => eapply IHlen; [ eassumption | ]
                       | [ H : _ \/ _ |- _ ] => destruct H
                       | [ |- is_true (paren_balanced_hiding' _ _) ] => rewrite paren_balanced_hiding'_nil by (rewrite ?take_length, ?drop_length; reflexivity)
                       | [ H : context[match ?n with 0 => None | S _ => @None ?A end] |- _ ]
                         => replace (match n with 0 => None | S _ => @None A end) with (@None A) in H by (destruct n; reflexivity)
                       | [ IHlen : forall a b, nth _ (map _ (list_of_next_bin_ops' _)) None = Some _ -> _,
                             H : nth _ (map _ (list_of_next_bin_ops' _)) None = Some _ |- _ ]
                         => specialize (IHlen _ _ H)
                       | _ => solve [ eauto using paren_balanced_hiding'_S with nocore ]
                     end.
            SearchAbout (_ + 1 = S _).
            end
            unfold paren_balanced'_step in H4.
            rewrite Heqb in H4.
            rewrite Heqb0 in H4.
            simpl in H4.



            erewrite (proj1 (get_0 _ _)) in H4.
            Focus 2.
            rewrite take_take.

 by eassumption.
            intros H' Hbal. *)(* }
            { intros n idx H'.
              rewrite index_points_to_binop_S1.
              specialize (IHlen n offset idx H').
              destruct IHlen as [IHlen0 IHlen1].
              split; [ exact IHlen0 | ].
              rewrite drop_drop, NPeano.Nat.add_1_r in IHlen1.
              exact IHlen1. } } } *)
  Admitted.

  Lemma list_of_next_bin_ops_satisfies_spec {HSLP : StringLikeProperties Char} (str : String)
  : list_of_next_bin_ops_spec (list_of_next_bin_ops str) str.
  Proof.
    apply list_of_next_bin_ops'_satisfies_spec.
  Qed.
End make_table.
