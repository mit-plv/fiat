(** * Build a table for the next binop at a given level *)
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.ZArith.BinInt.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.

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
    := (fun ch table_op_higher_ops =>
          let '(table, (next_op, higher_ops))
              := (fst table_op_higher_ops,
                  (option_map S (nth 0 (fst table_op_higher_ops) None),
                   map (option_map S) (snd table_op_higher_ops))) in
          let '(cur_mark, new_higher_ops)
              := (if is_bin_op ch
                  then (Some 0,
                        higher_ops)
                  else if is_close ch
                       then (None,
                             None::higher_ops)
                       else if is_open ch
                            then ((nth 0 higher_ops None),
                                  tl higher_ops)
                            else (next_op,
                                  higher_ops)) in
          (cur_mark::table, new_higher_ops)).

  Definition list_of_next_bin_ops' (str : String)
  : list (option nat) * list (option nat)
    := fold
         list_of_next_bin_ops'_step
         (nil, nil)
         str.

  Lemma list_of_next_bin_ops'_nil (str : String) (H : length str = 0)
  : list_of_next_bin_ops' str = (nil, nil).
  Proof.
    unfold list_of_next_bin_ops'; rewrite fold_nil by assumption.
    reflexivity.
  Qed.

  Global Instance list_of_next_bin_ops'_Proper {HSLP : StringLikeProperties Char}
  : Proper (beq ==> eq) list_of_next_bin_ops'.
  Proof.
    apply fold_Proper.
  Qed.

  Definition Let_In {A B} (a : A) (f : forall a : A, B a) : B a
    := f a.

  Lemma list_of_next_bin_ops'_length' {HSLP : StringLikeProperties Char} str
  : List.length (fst (list_of_next_bin_ops' str)) = length str.
  Proof.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len.
    revert str.
    induction len; simpl; intros str H'.
    { rewrite list_of_next_bin_ops'_nil by assumption; reflexivity. }
    { unfold list_of_next_bin_ops' in *.
      specialize (IHlen (drop 1 str)).
      rewrite drop_length, H' in IHlen.
      simpl in IHlen.
      specialize (IHlen (NPeano.Nat.sub_0_r _)).
      rewrite fold_recr.
      destruct (singleton_exists (take 1 str)) as [ch H''].
      { rewrite take_length, H'; reflexivity. }
      { erewrite (fun H => proj1 (get_0 _ H)) by eassumption.
        unfold list_of_next_bin_ops'_step at 1.
        repeat match goal with
                 | _ => reflexivity
                 | _ => rewrite IHlen
                 | _ => progress simpl
                 | [ |- context[if ?f ch then _ else _] ] => destruct (f ch)
               end. } }
  Qed.

  Lemma list_of_next_bin_ops'_length2' {HSLP : StringLikeProperties Char} str
  : List.length (snd (list_of_next_bin_ops' str)) <= length str.
  Proof.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len.
    revert str.
    induction len; simpl; intros str H'.
    { rewrite list_of_next_bin_ops'_nil by assumption; reflexivity. }
    { unfold list_of_next_bin_ops' in *.
      specialize (IHlen (drop 1 str)).
      rewrite drop_length, H' in IHlen.
      simpl in IHlen.
      specialize (IHlen (NPeano.Nat.sub_0_r _)).
      rewrite fold_recr.
      destruct (singleton_exists (take 1 str)) as [ch H''].
      { rewrite take_length, H'; reflexivity. }
      { erewrite (fun H => proj1 (get_0 _ H)) by eassumption.
        unfold list_of_next_bin_ops'_step at 1.
        repeat match goal with
                 | _ => reflexivity
                 | _ => omega
                 | _ => progress simpl in *
                 | _ => rewrite IHlen
                 | _ => rewrite map_length
                 | _ => progress simpl
                 | [ |- context[if ?f ch then _ else _] ] => destruct (f ch)
                 | [ H : context[List.length ?ls] |- context[?ls] ] => destruct ls
               end. } }
  Qed.

  Typeclasses Opaque list_of_next_bin_ops'.

  Lemma list_of_next_bin_ops'_drop {HSLP : StringLikeProperties Char} str n
  : List.Operations.drop n (fst (list_of_next_bin_ops' str)) = fst (list_of_next_bin_ops' (drop n str)).
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
        unfold list_of_next_bin_ops' at 1.
        rewrite fold_recr.
        destruct (singleton_exists (take 1 str)) as [ch H''].
        { rewrite take_length, H'; reflexivity. }
        { rewrite (proj1 (get_0 _ _) H'').
          unfold list_of_next_bin_ops'_step at 1.
          repeat match goal with
                   | _ => reflexivity
                   | _ => progress simpl
                   | [ |- context[if ?f ch then _ else _] ] => destruct (f ch)
                 end. } } }
  Qed.


  (** TODO FIXME: How do I say "first _at this level of parenthetization_?" *)
  Definition list_of_next_bin_ops'_spec (str : String) (tbl : list (option nat))
    := forall n idx,
         nth n tbl None = Some idx
         -> (forall idx' ch',
               idx' < idx
               -> get (n + idx') str = Some ch'
               -> ~is_true (is_bin_op ch'))
            /\ (forall ch,
                  get (n + idx) str = Some ch
                  -> is_true (is_bin_op ch)).

  Lemma list_of_next_bin_ops'_snd_is_bin_op {HSLP : StringLikeProperties Char} str
  : forall n idx,
      nth n (snd (list_of_next_bin_ops' str)) None = Some idx
      -> exists ch,
           is_true (is_bin_op ch)
           /\ get idx str = Some ch.
  Proof.
    intro n.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len; generalize dependent n.
    revert str.
    induction len.
    { intros ???? H'.
      rewrite nth_overflow in H' by (rewrite list_of_next_bin_ops'_length2'; omega).
      congruence. }
    { intros str n H0 idx H1.
      specialize (IHlen (drop 1 str)).
      rewrite drop_length, H0 in IHlen; simpl in IHlen.
      rewrite NPeano.Nat.sub_0_r in IHlen.
      unfold list_of_next_bin_ops' in *.
      rewrite fold_recr in H1.
      destruct (singleton_exists (take 1 str)) as [ch H2].
      { rewrite take_length, H0; reflexivity. }
      { rewrite (proj1 (get_0 _ _) H2) in H1.
        unfold list_of_next_bin_ops'_step at 1 in H1.
        repeat match type of H1 with
                 | _ => progress simpl in *
                 | context[if ?f ch then _ else _] => destruct (f ch) eqn:?
               end;
          solve [
              destruct n; simpl in *;
              repeat match goal with
                       | _ => progress subst
                       | _ => progress simpl in *
                       | _ => assumption
                       | _ => omega
                       | _ => congruence
                       | [ H : is_true (?x ~= [ ?ch ])%string_like, H' : is_true (?x ~= [ ?ch' ])%string_like |- _ ]
                         => assert (ch = ch') by (eapply singleton_unique; eassumption); clear H'
                       | [ H : S _ < S _ |- _ ] => apply Lt.lt_S_n in H
                       | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?
                       | [ H : ex _ |- _ ] => destruct H
                       | _ => progress intros
                       | [ H : and _ _ |- _ ] => destruct H
                       | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                       | [ |- _ /\ _ ] => split
                       | _ => setoid_rewrite <- get_0
                       | [ H : _ = false |- _ ] => apply Bool.not_true_iff_false in H
                       | [ H : _ |- _ ] => setoid_rewrite <- get_0 in H
                       | [ |- exists ch, _ /\ _ ] => eexists; split; [ | eassumption ]; eassumption
                       | [ IHlen : forall n, ?len = ?len -> _, H : _ |- _ ] => specialize (IHlen _ eq_refl _ H)
                       | [ H : context[get ?x _] |- _ ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x) in H
                       | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?drop_0, ?nth_tl in H
                       | [ |- context[get ?x _] ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x)
                       | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, <- ?plus_n_Sm
                       | [ H : forall idx' ch', idx' < _ -> _ -> ~ is_true (is_bin_op _) |- ~ is_true (is_bin_op _) ]
                         => eapply H; try eassumption; []
                       | [ H : ?idx < S _ |- _ ] => is_var idx; destruct idx
                       | [ H : nth ?n (map ?f ?ls) ?d = _ |- _ ] => revert H; simpl rewrite (map_nth f ls d n)
                       | [ H : context[if ?f ch then _ else _] |- _ ] => destruct (f ch) eqn:?
                     end ]. } }
  Qed.

  Lemma list_of_next_bin_ops'_satisfies_spec {HSLP : StringLikeProperties Char} str
  : list_of_next_bin_ops'_spec str (fst (list_of_next_bin_ops' str)).
  Proof.
    intro n.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len; generalize dependent n.
    revert str.
    induction len.
    { intros ???? H'.
      rewrite nth_overflow in H' by (rewrite list_of_next_bin_ops'_length'; omega).
      congruence. }
    { intros str n H0 idx H1.
      specialize (IHlen (drop 1 str)).
      rewrite drop_length, H0 in IHlen; simpl in IHlen.
      rewrite NPeano.Nat.sub_0_r in IHlen.
      unfold list_of_next_bin_ops' in *.
      rewrite fold_recr in H1.
      destruct (singleton_exists (take 1 str)) as [ch H2].
      { rewrite take_length, H0; reflexivity. }
      { rewrite (proj1 (get_0 _ _) H2) in H1.
        unfold list_of_next_bin_ops'_step at 1 in H1.
        repeat match type of H1 with
                 | _ => progress simpl in *
                 | context[if ?f ch then _ else _] => destruct (f ch) eqn:?
               end;
          try solve [
        destruct n; simpl in *;
          repeat match goal with
                   | _ => progress subst
                   | _ => progress simpl in *
                   | _ => assumption
                   | _ => omega
                   | _ => congruence
                   | [ H : is_true (?x ~= [ ?ch ])%string_like, H' : is_true (?x ~= [ ?ch' ])%string_like |- _ ]
                     => assert (ch = ch') by (eapply singleton_unique; eassumption); clear H'
                   | [ H : S _ < S _ |- _ ] => apply Lt.lt_S_n in H
                   | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?
                   | [ H : ex _ |- _ ] => destruct H
                   | _ => progress intros
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                   | [ |- _ /\ _ ] => split
                   | _ => setoid_rewrite <- get_0
                   | [ H : _ = false |- _ ] => apply Bool.not_true_iff_false in H
                   | [ H : _ |- _ ] => setoid_rewrite <- get_0 in H
                   | [ |- exists ch, _ /\ _ ] => eexists; split; [ | eassumption ]; eassumption
                   | [ IHlen : forall n, ?len = ?len -> _, H : _ |- _ ] => specialize (IHlen _ eq_refl _ H)
                   | [ H : context[get ?x _] |- _ ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x) in H
                   | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?drop_0 in H
                   | [ H : _ |- _ ] => setoid_rewrite drop_drop in H
                   | [ |- context[get ?x _] ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x)
                   | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r
                   | [ H : forall idx' ch', idx' < _ -> _ -> ~ is_true (is_bin_op _) |- ~ is_true (is_bin_op _) ]
                     => eapply H; try eassumption; []
                   | [ H : ?idx < S _ |- _ ] => is_var idx; destruct idx
                   | [ H : nth ?n (map ?f ?ls) ?d = _ |- _ ] => revert H; simpl rewrite (map_nth f ls d n)
                   | [ H : forall ch, is_true (?x ~= [ ch ])%string_like -> _, H' : is_true (?x ~= [ _ ])%string_like |- _ ]
                     => specialize (H _ H')
                 end ].

        destruct n; simpl in *;
          repeat match goal with
                   | _ => progress subst
                   | _ => progress simpl in *
                   | _ => assumption
                   | _ => omega
                   | _ => congruence
                   | [ H : is_true (?x ~= [ ?ch ])%string_like, H' : is_true (?x ~= [ ?ch' ])%string_like |- _ ]
                     => assert (ch = ch') by (eapply singleton_unique; eassumption); clear H'
                   | [ H : S _ < S _ |- _ ] => apply Lt.lt_S_n in H
                   | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?
                   | [ H : ex _ |- _ ] => destruct H
                   | _ => progress intros
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                   | [ |- _ /\ _ ] => split
                   | _ => setoid_rewrite <- get_0
                   | [ H : _ = false |- _ ] => apply Bool.not_true_iff_false in H
                   | [ H : _ |- _ ] => setoid_rewrite <- get_0 in H
                   | [ |- exists ch, _ /\ _ ] => eexists; split; [ | eassumption ]; eassumption
                   | [ IHlen : forall n, ?len = ?len -> _, H : _ |- _ ] => specialize (IHlen _ eq_refl _ H)
                   | [ H : context[get ?x _] |- _ ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x) in H
                   | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?drop_0 in H
                   | [ H : _ |- _ ] => setoid_rewrite drop_drop in H
                   | [ |- context[get ?x _] ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x)
                   | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r
                   | [ H : forall idx' ch', idx' < _ -> _ -> ~ is_true (is_bin_op _) |- ~ is_true (is_bin_op _) ]
                     => eapply H; try eassumption; []
                   | [ H : ?idx < S _ |- _ ] => is_var idx; destruct idx
                   | [ H : nth ?n (map ?f ?ls) ?d = _ |- _ ] => revert H; simpl rewrite (map_nth f ls d n)
                   | [ H : forall ch, is_true (?x ~= [ ch ])%string_like -> _, H' : is_true (?x ~= [ _ ])%string_like |- _ ]
                     => specialize (H _ H')
                   | [ H : nth _ (snd (fold list_of_next_bin_ops'_step _ _)) _ = _ |- _ ]
                     => apply list_of_next_bin_ops'_snd_is_bin_op in H
                 end.
setoid_rewrite drop_drop in H4.
rewrite (@get_drop _ _ _ (n + )

        rewrite fold_recr in Heqo.
        Focus 2.
match goal with
                 end.

           repeat match goal with
                   | _ => progress subst
                   | _ => progress simpl in *
                   | _ => assumption
                   | _ => omega
                   | _ => congruence
                   | [ H : is_true (?x ~= [ ?ch ])%string_like, H' : is_true (?x ~= [ ?ch' ])%string_like |- _ ]
                     => assert (ch = ch') by (eapply singleton_unique; eassumption); clear H'
                   | [ H : S _ < S _ |- _ ] => apply Lt.lt_S_n in H
                   | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?
                   | [ H : ex _ |- _ ] => destruct H
                   | _ => progress intros
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                   | [ |- _ /\ _ ] => split
                   | _ => setoid_rewrite <- get_0
                   | [ H : _ = false |- _ ] => apply Bool.not_true_iff_false in H
                   | [ H : _ |- _ ] => setoid_rewrite <- get_0 in H
                   | [ |- exists ch, _ /\ _ ] => eexists; split; [ | eassumption ]; eassumption
                   | [ IHlen : forall n, ?len = ?len -> _, H : _ |- _ ] => specialize (IHlen _ eq_refl _ H)
                   | [ H : context[get ?x _] |- _ ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x) in H
                   | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r, ?drop_0 in H
                   | [ |- context[get ?x _] ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x)
                   | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r
                   | [ H : forall idx' ch', idx' < _ -> _ -> ~ is_true (is_bin_op _) |- ~ is_true (is_bin_op _) ]
                     => eapply H; try eassumption; []
                   | [ H : ?idx < S _ |- _ ] => is_var idx; destruct idx
                   | [ H : nth ?n (map ?f ?ls) ?d = _ |- _ ] => revert H; simpl rewrite (map_nth f ls d n)
                 end.
        lazymatch goal with
                 end.

rewrite nth_map in H1.

list_of_next_bin_ops'_snd_is_bin_op

admit.
        {
        destruct n; simpl in *;
          repeat match goal with
                 end.
        destruct  idx'; try solve [ exfalso; omega ];
        try rewrite drop_0 in H1;
        repeat match goal with
                 | _ => progress subst
                 | _ => assumption
                 | [ H : forall idx' ch', idx' < _ -> _ -> ~ is_true (is_bin_op _) |- ~ is_true (is_bin_op _) ]
                   => eapply H; try eassumption; []
                   | _ => progress subst
                   | _ => progress simpl in *
                   | _ => assumption
                   | _ => omega
                   | _ => congruence
                   | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?
                   | [ H : ex _ |- _ ] => destruct H
                   | _ => progress intros
                   | [ H : and _ _ |- _ ] => destruct H
                   | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
                   | [ |- _ /\ _ ] => split
                   | _ => setoid_rewrite <- get_0
                   | [ H : _ = false |- _ ] => apply Bool.not_true_iff_false in H
                   | [ H : _ |- _ ] => setoid_rewrite <- get_0 in H
                   | [ |- exists ch, _ /\ _ ] => eexists; split; [ | eassumption ]; eassumption
                   | [ IHlen : forall n, ?len = ?len -> _, H : _ |- _ ] => specialize (IHlen _ eq_refl _ H)
                   | [ H : context[get ?x _] |- _ ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x) in H
                   | [ H : _ |- _ ] => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r in H
                   | [ |- context[get ?x _] ] => not constr_eq x 0; rewrite (@get_drop _ _ _ x)
                   | _ => progress rewrite ?drop_drop, ?NPeano.Nat.add_1_r
                   | [ H : forall idx' ch', idx' < _ -> _ -> ~ is_true (is_bin_op _) |- ~ is_true (is_bin_op _) ]
                     => eapply H; try eassumption; []
               end.
SearchAbout (S _ < S _).

SearchAbout (_ = false) (~(_ = true)).


SearchAbout hd nth.
match goal with
end.
simpl in *.
eexists; split; try eassumption.
lazymatch goal with
end.
SearchAbout (_ + 1).
lazymatch goal with
end.

                   | [ |- get 0 _ = Some _ ] => apply get_0
                 end ].
          { inversion H1; subst.
            split; intros; try omega; [].
            exists ch; split; try assumption; [].
            apply get_0; assumption. }
          { specialize (IHlen n eq_refl idx H1).
            destruct IHlen as [IHlen0 [ch'' [? IHlen1]]].
            split.
            { intros idx' ch' H' H''.
              eapply IHlen0; try eassumption.
              rewrite get_drop, drop_drop.
              rewrite get_drop in H''.
              rewrite <- H''.
              repeat (f_equal; []); omega. }
            { exists ch''; split; try assumption; [].
              rewrite get_drop.
              rewrite get_drop, drop_drop in IHlen1.
              rewrite <- IHlen1.
              repeat (f_equal; []); omega. } } }
        {
              rewrite
              destr
              rewrite drop_drop
              specialize (IHlen0 idx' ch' H').
              rewrite (proj1 (get_0 _ _) H2); reflexivity.
      specialize (IHlen  eq_refl).

      destruct n as [|n].
      { simpl.
        rewrite <- list_of_next_bin_ops'_drop in IHlen.

        SearchAbout (_ - 0).
        assert (n = 0) by omega; subst.
        simpl in *.

    { rewrite nth_overflow by (rewrite list_of_next_bin_ops'_length'; omega).
      intros; congruence. }
    SearchAbout nth.
    SearchAbout nth.
    set (n' := len - n)
    replace n with (

    intro n; revert str.
    replace
    induction n; simpl.
    {
    intros n idx H'.
    destruct (get (n + idx) str) eqn:H''.
    { eexists; split; [ | reflexivity ].
      generalize dependent idx.
      revert str.
      induction n; simpl.
      { intros.
        destruct (length str) eqn:H'''.
        { exfalso.
          simpl in *.
          unfold list_of_next_bin_ops' in *.
          rewrite fold_nil in H' by assumption.
          simpl in *.
          congruence. }
        { destruct (singleton_exists (take 1 str)) as [ch H''''].
          { rewrite take_length, H'''; reflexivity. }
          { unfold list_of_next_bin_ops' in *.
            rewrite fold_recr in H' by assumption.
            rewrite (proj1 (get_0 _ _) H'''') in H'.

          rewrite H''' in

          apply has_first_char_nonempty in H'''.
          congruence.

        unfold list_of_next_bin_ops' in *.
        rewrite fold_





  Definition make_binop_table (str : String) (init_next_binop : list (option nat *


  Definition next_bracket_level (is_open_ch is_close_ch : bool)
             (initial_bracket_level  : Z)
  : Z
    := (if is_open_ch
        then 1 + initial_bracket_level
        else if is_close_ch
             then -1 + initial_bracket_level
             else initial_bracket_level)%Z.

 Definition make_bracket_levels' (str : String) (len : nat)
  : Z -> list (Char * Z)
    := nat_rect
         (fun _ => Z -> list (Char * Z))
         (fun _ => nil)
         (fun len' make_bracket_levels' initial_bracket_level
          => match get (length str - S len') str with
               | Some ch
                 => (ch, initial_bracket_level)::make_bracket_levels' (next_bracket_level (is_open ch) (is_close ch) initial_bracket_level)
               | None => (* bad len *) nil
             end)
         len.

  Definition make_bracket_levels str initial_level
    := make_bracket_levels' str (length str) initial_level.
SearchAbout (nat ->
  (** TODO: make something that isn't quadratic in string length *)
  Definition make_binop_table' (str : String) (len : nat) (initial_level : Z)
  : list (option nat * Z)
    := list_rect
         (fun _ => list (option nat * Z))
         nil
         (fun ch_level brackets rest_table
          => let '(ch, level) := (fst ch_level, snd ch_level) in
             (find (fun ch_level'
                    => let '(ch', level') := (fst ch_level', snd ch_level') in
                       (is_bin_op ch' && EqNat.
                    =>
::rest_table



  Definition list_of_next_bin_ops_closes' (s : String) (len : nat)
             (next_op__higher_ops : option nat * list nat)
  : list (option nat) * (option nat * list nat)
    := nat_rect
         (fun _ => list (option nat) * (option nat * list nat))%type
         (nil, next_op__higher_closes)
         (fun len' table_op_higher_closes =>
            let ch := get (length s - S len') s in
            let '(table, (next_op, higher_closes))
                := (fst table_op_higher_closes,
                    (option_map S (fst (snd table_op_higher_closes)),
                     map S (snd (snd table_op_higher_closes)))) in
            let '(cur_mark, new_next_op, new_higher_closes)
                := (if is_bin_op ch
                    then (Some 0,
                          Some 0,
                          higher_closes)
                    else if is_close ch
                         then (None,
                               None,
                               0::higher_closes)
                         else if is_open ch
                              then ((hd None (map Some higher_closes)),
                                    None,
                                    tl higher_closes)
                              else (next_op,
                                    next_op,
                                    higher_closes)) in
            (cur_mark::table, (new_next_op, new_higher_closes)))
         s.

  Lemma list_of_next_bin_ops_closes_compute_empty {hc}
  : list_of_next_bin_ops_closes (Empty String) hc
    = (nil, hc).
  Proof.
    unfold list_of_next_bin_ops_closes.
    rewrite Fold_compute_empty; reflexivity.
  Qed.

  Lemma list_of_next_bin_ops_closes_compute_cons {ch s hc}
  : list_of_next_bin_ops_closes ([[ ch ]] ++ s) hc
    = (let table_op_higher_closes := list_of_next_bin_ops_closes s hc in
       let '(table, (next_op, higher_closes))
           := (fst table_op_higher_closes,
               (option_map S (fst (snd table_op_higher_closes)),
                map S (snd (snd table_op_higher_closes)))) in
       ((if is_bin_op ch
         then Some 0
         else if is_close ch
              then None
              else if is_open ch
                   then hd None (map Some higher_closes)
                   else next_op)
          ::table,
        ((if is_bin_op ch
          then Some 0
          else if is_close ch
               then None
               else if is_open ch
                    then None
                    else next_op),
         (if is_bin_op ch
          then higher_closes
          else if is_close ch
               then 0::higher_closes
               else if is_open ch
                    then tl higher_closes
                    else higher_closes)))).
  Proof.
    unfold list_of_next_bin_ops_closes; simpl.
    rewrite Fold_compute_cons; simpl.
    destruct (is_bin_op ch), (is_close ch), (is_open ch); simpl;
    reflexivity.
  Qed.

  Lemma list_of_next_bin_ops_closes_compute_append {s1 s2 hc}
  : list_of_next_bin_ops_closes (s1 ++ s2) hc
    = (let table_hc' := list_of_next_bin_ops_closes s2 hc in
       let '(table, hc') := (fst table_hc', snd table_hc') in
       ((fst (list_of_next_bin_ops_closes s1 hc') ++ table)%list,
        snd (list_of_next_bin_ops_closes s1 hc'))).
  Proof.
    simpl.
    revert s1 s2.
    match goal with
      | [ |- forall s, @?P s ]
        => refine (Fold _ P _ _)
    end.
    { intro s2.
      rewrite list_of_next_bin_ops_closes_compute_empty; simpl.
      rewrite LeftId.
      apply injective_projections; reflexivity. }
    { intros ch ? IHs s2.
      rewrite Associativity.
      rewrite !list_of_next_bin_ops_closes_compute_cons, !IHs; simpl.
      reflexivity. }
  Qed.

  Lemma length_fst_list_of_next_bin_ops_closes {s hc}
  : List.length (fst (list_of_next_bin_ops_closes s hc)) = Length s.
  Proof.
    revert s.
    apply Fold.
    { rewrite list_of_next_bin_ops_closes_compute_empty, Length_Empty; reflexivity. }
    { intros ? ? H; rewrite list_of_next_bin_ops_closes_compute_cons; simpl.
      rewrite <- Length_correct, Singleton_Length, H; reflexivity. }
  Qed.

  Context (open close op : Char).

  Definition make_table' (str : String) (len : nat) : Z -> (list (option nat)) * Z
    := nat_rect
         (fun _ => Z -> (list (option nat)) * Z)
         (fun init_paren_level => (nil, init_paren_level))
         (fun len' make_table' cur_paren_level
          => if char_beq (get str (length str - S len')) close
             then let lsn := make_table' (1 + cur_paren_level)%Z in
                  (
EqNat.beq_nat

match len with
         | 0 => nil
         | S len' =
