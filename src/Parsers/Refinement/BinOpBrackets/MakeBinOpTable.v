(** * Build a table for the next binop at a given level *)
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.
Require Import Fiat.Common.SetoidInstances.

Set Implicit Arguments.

Section make_table.
  Context {Char} {HSL : StringLike Char} (char_beq : Char -> Char -> bool).
  Context (is_bin_op : Char -> bool)
          (is_open : Char -> bool) (is_close : Char -> bool).


  (** We build a table to tell us where to split.
      For each character, we store an [option nat], and keep a
      transient [list nat].

      We store where the next '+' at the current level of
      parenthetization is.  The transient list stores where the
      next '+' is for higher levels. *)

  Definition list_of_next_bin_ops'_step
    := (fun ch table_higher_ops =>
          let next_ops := map (option_map S) (nth 0 table_higher_ops nil) in
          let '(cur_mark, new_higher_ops) := (nth 0 next_ops None, tl next_ops) in
          ((if is_bin_op ch
            then Some 0 :: new_higher_ops
            else if is_close ch
                 then None :: next_ops
                 else if is_open ch
                      then new_higher_ops
                      else next_ops)
             :: table_higher_ops)).

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

  (**
<<
pbh' ch n "" = true
pbh' ch n (ch :: s) = n > 0 && pbh' ch n s
pbh' ch n ('(' :: s) = pbh' ch (n + 1) s
pbh' ch n (')' :: s) = n > 0 && pbh' ch (n - 1) s
pbh' ch n (_ :: s) = pbh' ch n s

pbh = pbh' '+' 0
>>
*)

  Local Ltac induction_str_len str :=
    let len := fresh "len" in
    set (len := length str);
      generalize (eq_refl : length str = len);
      clearbody len; revert str;
      induction len; intros str ?.

  Section paren_balanced_def.
    Definition paren_balanced'_step (ch : Char) (pbh_rest : nat -> bool) (start_level : nat)
    : bool
      := if is_bin_op ch
         then pbh_rest start_level
         else if is_open ch
              then pbh_rest (S start_level)
              else if is_close ch
                   then ((Compare_dec.gt_dec start_level 0)
                           && pbh_rest (pred start_level))%bool
                   else pbh_rest start_level.

    Definition paren_balanced' (str : String) (start_level : nat)
    : bool
      := fold
           paren_balanced'_step
           (fun _ => true)
           str
           start_level.

    Lemma paren_balanced'_nil (str : String) (H : length str = 0)
    : paren_balanced' str = fun _ => true.
    Proof.
      apply fold_nil; assumption.
    Qed.

    Lemma paren_balanced'_recr {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced' str
      = match get 0 str with
          | Some ch => paren_balanced'_step ch (paren_balanced' (drop 1 str))
          | None => fun _ => true
        end.
    Proof.
      apply fold_recr.
    Qed.

    Global Instance paren_balanced'_Proper1 {HSLP : StringLikeProperties Char}
    : Proper (beq ==> eq ==> eq) paren_balanced'.
    Proof.
      unfold paren_balanced'.
      repeat intro; subst.
      match goal with
        | [ |- ?f ?x = ?g ?x ] => cut (f = g); [ let H := fresh in intro H; rewrite H; reflexivity | ]
      end.
      setoid_subst_rel beq.
      reflexivity.
    Qed.

    Typeclasses Opaque paren_balanced'.
    Opaque paren_balanced'.

    Lemma paren_balanced'_S {HSLP : StringLikeProperties Char} (str : String) n
    : paren_balanced' str n -> paren_balanced' str (S n).
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced'_nil by assumption; simpl.
        reflexivity. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length in IHlen.
        repeat match goal with
                 | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by omega; specialize (H H'); clear H'
               end.
        rewrite paren_balanced'_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          unfold paren_balanced'_step.
          repeat match goal with
                   | [ |- context[if ?f ch then _ else _] ] => destruct (f ch) eqn:?
                   | _ => reflexivity
                   | _ => solve [ eauto with nocore ]
                   | _ => progress simpl in *
                   | _ => setoid_rewrite Bool.andb_true_iff
                   | _ => intro
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : bool_of_sumbool (Compare_dec.gt_dec ?a ?b) = true |- _ ] => destruct (Compare_dec.gt_dec a b)
                   | _ => congruence
                   | [ H : ?n > 0 |- _ ] => is_var n; destruct n
                 end. } }
    Qed.

    Lemma paren_balanced'_le {HSLP : StringLikeProperties Char} (str : String) n1 n2 (H : n1 <= n2)
    : paren_balanced' str n1 -> paren_balanced' str n2.
    Proof.
      apply Minus.le_plus_minus in H.
      revert str.
      generalize dependent (n2 - n1).
      intros diff ?; subst n2; revert n1.
      induction diff; simpl.
      { intros ?? H.
        replace (n1 + 0) with n1 by omega.
        assumption. }
      { intro n1.
        replace (n1 + S diff) with (S (n1 + diff)) by omega.
        intros.
        eauto using paren_balanced'_S with nocore. }
    Qed.

    Definition paren_balanced (str : String) := paren_balanced' str 0.
  End paren_balanced_def.

  Section paren_balanced_hiding_def.
    Definition paren_balanced_hiding'_step (ch : Char) (pbh_rest : nat -> bool) (start_level : nat)
    : bool
      := if is_bin_op ch
         then ((Compare_dec.gt_dec start_level 0)
                 && pbh_rest start_level)%bool
         else paren_balanced'_step ch pbh_rest start_level.

    Definition paren_balanced_hiding' (str : String) (start_level : nat)
    : bool
      := fold
           paren_balanced_hiding'_step
           (fun _ => true)
           str
           start_level.

    Lemma paren_balanced_hiding'_nil (str : String) (H : length str = 0)
    : paren_balanced_hiding' str = fun _ => true.
    Proof.
      apply fold_nil; assumption.
    Qed.

    Lemma paren_balanced_hiding'_recr {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced_hiding' str
      = match get 0 str with
          | Some ch => paren_balanced_hiding'_step ch (paren_balanced_hiding' (drop 1 str))
          | None => fun _ => true
        end.
    Proof.
      apply fold_recr.
    Qed.

    Global Instance paren_balanced_hiding'_Proper1 {HSLP : StringLikeProperties Char}
    : Proper (beq ==> eq ==> eq) paren_balanced_hiding'.
    Proof.
      unfold paren_balanced_hiding'.
      repeat intro; subst.
      match goal with
        | [ |- ?f ?x = ?g ?x ] => cut (f = g); [ let H := fresh in intro H; rewrite H; reflexivity | ]
      end.
      setoid_subst_rel beq.
      reflexivity.
    Qed.

    Typeclasses Opaque paren_balanced_hiding'.
    Opaque paren_balanced_hiding'.

    Lemma paren_balanced_hiding'_S {HSLP : StringLikeProperties Char} (str : String) n
    : paren_balanced_hiding' str n -> paren_balanced_hiding' str (S n).
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced_hiding'_nil by assumption; simpl.
        reflexivity. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length in IHlen.
        repeat match goal with
                 | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by omega; specialize (H H'); clear H'
               end.
        rewrite paren_balanced_hiding'_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          unfold paren_balanced_hiding'_step, paren_balanced'_step.
          repeat match goal with
                   | [ |- context[if ?f ch then _ else _] ] => destruct (f ch) eqn:?
                   | _ => reflexivity
                   | _ => solve [ eauto with nocore ]
                   | _ => progress simpl in *
                   | _ => setoid_rewrite Bool.andb_true_iff
                   | _ => intro
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : bool_of_sumbool (Compare_dec.gt_dec ?a ?b) = true |- _ ] => destruct (Compare_dec.gt_dec a b)
                   | _ => congruence
                   | [ H : ?n > 0 |- _ ] => is_var n; destruct n
                 end. } }
    Qed.

    Lemma paren_balanced_hiding'_le {HSLP : StringLikeProperties Char} (str : String) n1 n2 (H : n1 <= n2)
    : paren_balanced_hiding' str n1 -> paren_balanced_hiding' str n2.
    Proof.
      apply Minus.le_plus_minus in H.
      revert str.
      generalize dependent (n2 - n1).
      intros diff ?; subst n2; revert n1.
      induction diff; simpl.
      { intros ?? H.
        replace (n1 + 0) with n1 by omega.
        assumption. }
      { intro n1.
        replace (n1 + S diff) with (S (n1 + diff)) by omega.
        intros.
        eauto using paren_balanced_hiding'_S with nocore. }
    Qed.

    Definition paren_balanced_hiding (str : String) := paren_balanced_hiding' str 0.
  End paren_balanced_hiding_def.

  Section paren_balanced_to_hiding.
    Lemma paren_balanced_hiding_impl_paren_balanced' {HSLP : StringLikeProperties Char} n (str : String)
    : paren_balanced_hiding' str n -> paren_balanced' str n.
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced_hiding'_nil, paren_balanced'_nil by assumption; trivial. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length, <- Minus.pred_of_minus in IHlen.
        specialize (IHlen (f_equal pred H)).
        rewrite paren_balanced_hiding'_recr, paren_balanced'_recr.
        edestruct get as [ch|]; trivial; [].
        unfold paren_balanced_hiding'_step, paren_balanced'_step.
        destruct (is_bin_op ch); try reflexivity;
        intros [|?]; simpl;
        destruct (is_open ch), (is_close ch);
        eauto with nocore;
        try (unfold is_true; intros; congruence). }
    Qed.

    Lemma paren_balanced_hiding_impl_paren_balanced {HSLP : StringLikeProperties Char} (str : String)
    : paren_balanced_hiding str -> paren_balanced str.
    Proof.
      apply paren_balanced_hiding_impl_paren_balanced'.
    Qed.

    Lemma paren_balanced_impl_paren_balanced_hiding' {HSLP : StringLikeProperties Char} n (str : String)
    : paren_balanced' str n -> paren_balanced_hiding' str (S n).
    Proof.
      revert n.
      induction_str_len str.
      { rewrite paren_balanced_hiding'_nil, paren_balanced'_nil by assumption; trivial. }
      { specialize (IHlen (drop 1 str)).
        rewrite drop_length, <- Minus.pred_of_minus in IHlen.
        specialize (IHlen (f_equal pred H)).
        rewrite paren_balanced_hiding'_recr, paren_balanced'_recr.
        edestruct get as [ch|]; trivial; [].
        unfold paren_balanced_hiding'_step, paren_balanced'_step.
        destruct (is_bin_op ch); simpl; eauto with nocore; [].
        intros [|?]; simpl;
        destruct (is_open ch), (is_close ch);
        eauto with nocore;
        try (unfold is_true; intros; congruence). }
    Qed.

    Lemma paren_balanced_impl_paren_balanced_hiding'_lt {HSLP : StringLikeProperties Char} n n' (Hlt : n < n') (str : String)
    : paren_balanced' str n -> paren_balanced_hiding' str n'.
    Proof.
      apply Minus.le_plus_minus in Hlt.
      generalize dependent (n' - S n).
      intros n'' ?; subst.
      revert n.
      induction n''.
      { intro.
        rewrite <- plus_n_O.
        apply paren_balanced_impl_paren_balanced_hiding'. }
      { simpl in *.
        intros n H'.
        apply paren_balanced_hiding'_S.
        rewrite NPeano.Nat.add_succ_r; eauto with nocore. }
    Qed.
  End paren_balanced_to_hiding.

  Definition index_points_to_binop (offset index : nat) (str : String)
    := forall ch,
         get (offset + index) str = Some ch
         -> is_bin_op ch.

  Lemma index_points_to_binop_S1 {HSLP : StringLikeProperties Char} offset index str
  : index_points_to_binop (S offset) index str <-> index_points_to_binop offset index (drop 1 str).
  Proof.
    unfold index_points_to_binop; split; intros H ch; specialize (H ch);
    rewrite get_drop, ?drop_drop; rewrite get_drop, ?drop_drop in H;
    intro H'; apply H;
    rewrite <- H'; do 2 (f_equal; []);
    omega.
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
    := forall ch,
         get (offset + index) str = Some ch
         -> is_bin_op ch = false.

  Lemma index_not_points_to_binop_S1 {HSLP : StringLikeProperties Char} offset index str
  : index_not_points_to_binop (S offset) index str <-> index_not_points_to_binop offset index (drop 1 str).
  Proof.
    unfold index_not_points_to_binop; split; intros H ch; specialize (H ch);
    rewrite get_drop, ?drop_drop; rewrite get_drop, ?drop_drop in H;
    intro H'; apply H;
    rewrite <- H'; do 2 (f_equal; []);
    omega.
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
    rewrite get_drop.
    rewrite has_first_char_nonempty by (rewrite drop_length; omega).
    intros; congruence.
  Qed.

  Definition list_of_next_bin_ops_spec' (level : nat) (table : list (option nat)) (str : String)
    := forall offset idx,
         (nth offset table None = Some idx
          -> index_points_to_binop offset idx str
             /\ paren_balanced_hiding' (take (pred idx) (drop offset str)) level)
         /\ (nth offset table None = None
             -> paren_balanced' (take (pred idx) (drop offset str)) level
             -> index_not_points_to_binop offset idx str).

  Definition list_of_next_bin_ops_spec
    := list_of_next_bin_ops_spec' 0.

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
      intros [] []; simpl; split; intros; try congruence;
      try (apply index_not_points_to_binop_nil; omega). }
      { intro str.
        specialize (IHlen (drop 1 str)).
        rewrite drop_length in IHlen.
        intro H.
        repeat match goal with
                 | [ H : ?A -> ?B |- _ ] => let H' := fresh in assert (H' : A) by omega; specialize (H H'); clear H'
               end.
        rewrite list_of_next_bin_ops'_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          intros n [|offset]; revert n; simpl.
          { specialize (fun n => IHlen n 0).
            setoid_rewrite drop_0.
            setoid_rewrite drop_0 in IHlen.
            pose proof (fun n idx => proj1 (IHlen n idx)) as IHlen0.
            pose proof (fun n idx => proj2 (IHlen n idx)) as IHlen1.
            clear IHlen.
            intros n idx; split.
            { intro H'; split;
              [ revert n idx H'
              | destruct idx as [|[|idx]];
                [ simpl;
                  rewrite paren_balanced_hiding'_nil by (rewrite ?take_length, ?drop_length; reflexivity);
                  reflexivity
                | simpl;
                  rewrite paren_balanced_hiding'_nil by (rewrite ?take_length, ?drop_length; reflexivity);
                  reflexivity
                | simpl;
                  rewrite paren_balanced_hiding'_recr; unfold paren_balanced_hiding'_step, paren_balanced'_step;
                  erewrite (proj1 (get_0 _ _)); [ | rewrite take_take; simpl; eassumption ];
                  revert n idx H' ] ];
              repeat match goal with
                       | [ |- context[if ?f ch then _ else _] ] => destruct (f ch) eqn:?
                     end;
              intros [|n];
              repeat match goal with
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
                     end. }
            { revert n.
              intros [|n];
                repeat match goal with
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
                       end.
intros H' Hbal.

            { intros n idx H'.
              rewrite index_points_to_binop_S1.
              specialize (IHlen n offset idx H').
              destruct IHlen as [IHlen0 IHlen1].
              split; [ exact IHlen0 | ].
              rewrite drop_drop, NPeano.Nat.add_1_r in IHlen1.
              exact IHlen1. } } } }
      { SearchAbout nth.
  Qed.

  Lemma list_of_next_bin_ops_satisfies_spec {HSLP : StringLikeProperties Char} (str : String)
  : list_of_next_bin_ops_spec (list_of_next_bin_ops str) str.
  Proof.
    apply list_of_next_bin_ops'_satisfies_spec.
  Qed.
End make_table.
