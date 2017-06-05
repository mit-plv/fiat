(** * Build a table for the next binop at a given level *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Common.
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
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  (** We build a version of paren-balanced-hiding to compute each cell
      of the table. *)
  (**
<<
pb' ch n "" = (n == 0)
pb' ch n (ch :: s) = n > 0 && pb' ch n s
pb' ch n ('(' :: s) = pb' ch (n + 1) s
pb' ch n (')' :: s) = n > 0 && pb' ch (n - 1) s
pb' ch n (_ :: s) = pb' ch n s

pb = pb' '+' 0
>>
*)

  Definition compute_next_bin_op'_step
    := (fun ch next level
        => if is_bin_op ch
           then if Compare_dec.gt_dec level 0
                then option_map S (next level)
                else Some 0
           else if is_open ch
                then option_map S (next (S level))
                else if is_close ch
                     then if Compare_dec.gt_dec level 0
                          then option_map S (next (pred level))
                          else None
                     else option_map S (next level)).

  Definition compute_next_bin_op' (str : String) (level : nat)
  : option nat
    := fold
         compute_next_bin_op'_step
         (fun _ => None)
         str
         level.

  Lemma compute_next_bin_op'_nil (str : String) (H : length str = 0)
  : compute_next_bin_op' str = fun _ => None.
  Proof.
    apply fold_nil; assumption.
  Qed.

  Lemma compute_next_bin_op'_recr {HSLP : StringLikeProperties Char} (str : String)
  : compute_next_bin_op' str
    = match get 0 str with
        | Some ch => compute_next_bin_op'_step ch (compute_next_bin_op' (drop 1 str))
        | None => fun _ => None
      end.
  Proof.
    apply fold_recr.
  Qed.

  Global Instance compute_next_bin_op'_step_Proper {HSLP : StringLikeProperties Char}
  : Proper (eq ==> (eq ==> eq) ==> eq ==> eq) compute_next_bin_op'_step.
  Proof.
    repeat intro; subst.
    unfold compute_next_bin_op'_step.
    unfold respectful in *.
    match goal with
      | [ H : _ |- _ ] => erewrite !H by reflexivity
    end.
    reflexivity.
  Qed.

  Global Instance compute_next_bin_op'_Proper {HSLP : StringLikeProperties Char}
  : Proper (beq ==> eq) compute_next_bin_op'.
  Proof.
    apply fold_Proper.
  Qed.

  Global Instance compute_next_bin_op'_Proper' {HSLP : StringLikeProperties Char}
  : Proper (beq ==> eq ==> eq) compute_next_bin_op'.
  Proof.
    repeat intro; subst.
    refine (f_equal (fun f => f _) _).
    setoid_subst_rel beq.
    reflexivity.
  Qed.

  Typeclasses Opaque compute_next_bin_op'.
  Opaque compute_next_bin_op'.

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
            else if is_open ch
                 then new_higher_ops
                 else if is_close ch
                      then None :: next_ops
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
      { erewrite (fun s H => proj1 (get_0 s H)) by eassumption.
        unfold list_of_next_bin_ops'_step.
        repeat match goal with
                 | _ => reflexivity
                 | _ => rewrite IHlen
                 | _ => progress simpl
                 | [ |- context[if ?f ch then _ else _] ] => destruct (f ch)
               end. } }
  Qed.

  Lemma list_of_next_bin_ops'_drop {HSLP : StringLikeProperties Char} str n
  : List.drop n (list_of_next_bin_ops' str) = list_of_next_bin_ops' (drop n str).
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

  Lemma index_points_to_binop_nil {HSLP : StringLikeProperties Char}
        (offset index : nat) (str : String) (H : length str <= offset + index)
  : index_points_to_binop offset index str.
  Proof.
    unfold index_points_to_binop.
    apply for_first_char_nil.
    rewrite drop_length; omega.
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

  Definition cell_of_next_bin_ops_spec'' (level : nat) (cell : option nat) (str : String) offset idx
    := (cell = Some idx
        -> index_points_to_binop offset idx str
           /\ paren_balanced_hiding' (take idx (drop offset str)) level)
       /\ (cell = None
           -> paren_balanced' (take idx (drop offset str)) level
           -> index_not_points_to_binop offset idx str).

  Definition list_of_next_bin_ops_spec'' (level : nat) (table : list (option nat)) (str : String) offset idx
    := cell_of_next_bin_ops_spec'' level (nth offset table None) str offset idx.

  Definition list_of_next_bin_ops_spec' (level : nat) (table : list (option nat)) (str : String)
    := forall offset idx, list_of_next_bin_ops_spec'' level table str offset idx.

  Definition list_of_next_bin_ops_spec
    := list_of_next_bin_ops_spec' 0.

  Global Instance cell_of_next_bin_ops_spec''_Proper {HSLP : StringLikeProperties Char}
  : Proper (eq ==> eq ==> beq ==> eq ==> eq ==> iff) cell_of_next_bin_ops_spec''.
  Proof.
    repeat intro; subst.
    unfold cell_of_next_bin_ops_spec''.
    repeat (split || intros || split_and);
    specialize_by assumption;
    unfold index_points_to_binop in *;
    unfold index_not_points_to_binop in *;
    try match goal with
          | [ H : (_ =s _) |- _ ] => rewrite <- H; assumption
          | [ H : (_ =s _) |- _ ] => rewrite H; assumption
        end.
    repeat match goal with
             | [ H : (_ =s _) |- _ ] => rewrite <- H
             | [ H : (_ =s ?x), H' : context[?x] |- _ ] => rewrite <- H in H'
             | _ => progress specialize_by assumption
             | _ => assumption
           end.
    repeat match goal with
             | [ H : (_ =s _) |- _ ] => rewrite H
             | [ H : (?x =s _), H' : context[?x] |- _ ] => rewrite H in H'
             | _ => progress specialize_by assumption
             | _ => assumption
           end.
  Qed.

  Definition cell_of_next_bin_op_spec''_S_offset {HSLP : StringLikeProperties Char} {level cell str offset idx}
             (H : cell_of_next_bin_ops_spec'' level cell (drop 1 str) offset idx)
  : cell_of_next_bin_ops_spec'' level cell str (S offset) idx.
  Proof.
    unfold cell_of_next_bin_ops_spec'' in *; simpl in *.
    rewrite !index_points_to_binop_S1.
    rewrite !index_not_points_to_binop_S1.
    rewrite drop_drop, NPeano.Nat.add_1_r in H.
    assumption.
  Qed.

  Definition list_of_next_bin_ops_spec''_S_offset {HSLP : StringLikeProperties Char} {level table str offset t' idx}
             (H : list_of_next_bin_ops_spec'' level table (drop 1 str) offset idx)
  : list_of_next_bin_ops_spec'' level (t'::table) str (S offset) idx.
  Proof.
    unfold list_of_next_bin_ops_spec''; simpl.
    apply cell_of_next_bin_op_spec''_S_offset.
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
             | [ H : is_true false |- _ ] => solve [ inversion H ]
             | [ H : false = true |- _ ] => solve [ inversion H ]
             | [ H : true = false |- _ ] => solve [ inversion H ]
             | [ H : ?x = ?x |- _ ] => clear H
             | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
             | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
             | [ H : option_map _ ?x = None |- _ ] => destruct x eqn:?; simpl in H
             | _ => progress split_and
             | [ H : is_true (?str ~= [ ?ch ])%string_like, H' : is_true (?str ~= [ ?ch' ])%string_like |- _ ]
               => assert (ch = ch') by (eapply singleton_unique; eassumption);
                 clear H'
             | [ H : ?x = true |- context[?x] ] => rewrite H
             | [ H : ?x = false |- context[?x] ] => rewrite H
             | [ H : is_true ?x |- context[?x] ] => rewrite H
             | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = false, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : is_true ?x, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = S _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = Some _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : ?x = None, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : option_map _ ?x = Some _ |- _ ] => destruct x eqn:?; simpl in H
             | [ H : option_map _ ?x = None |- _ ] => destruct x eqn:?; simpl in H
             | [ H : forall x, _ = _ -> @?T x |- _ ] => specialize (H _ eq_refl)
             | [ H : _ = _ -> ?T |- _ ] => specialize (H eq_refl)
             | [ H : context[_ - 0] |- _ ] => rewrite NPeano.Nat.sub_0_r in H
             | [ |- context[_ - 0] ] => rewrite NPeano.Nat.sub_0_r
             | [ H : context[(_ + 1)%nat] |- _ ] => rewrite NPeano.Nat.add_1_r in H || setoid_rewrite NPeano.Nat.add_1_r in H
             | [ H : ?x > 0 |- _ ] => is_var x; destruct x; [ exfalso; clear -H; omega | clear dependent H ]
             | [ H : ~ ?x > 0 |- _ ] => is_var x; destruct x; [ clear dependent H | exfalso; clear -H; omega ]
             | [ H : 0 > 0 |- _ ] => exfalso; clear -H; omega
             | [ |- and _ _ ] => split
             | _ => progress intros
           end.

  Local Ltac t' :=
    idtac;
    match goal with
      | _ => progress t_eq
      | [ |- index_points_to_binop 0 0 _ ] => eapply index_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
      | _ => rewrite paren_balanced_hiding'_nil by (rewrite take_length; reflexivity)
      | [ H : _ |- _ ] => progress rewrite ?nth_tl in H
      | _ => progress rewrite ?drop_0, ?nth_tl
      | [ |- context[drop _ (take _ _)] ] => rewrite drop_take
      | [ H : context[drop _ (take _ _)] |- _ ] => rewrite drop_take in H
      | [ |- context[get 0 (take _ _)] ] => rewrite get_take_lt by omega
      | [ |- context[nth ?n (map ?f ?ls) _] ] => simpl rewrite (map_nth f ls None n)
      | [ |- context[nth ?n (map ?f ?ls) _] ] => simpl rewrite (map_nth f ls nil n)
      | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls None n)
      | [ H : context[nth ?n (map ?f ?ls) _] |- _ ] => revert H; simpl rewrite (map_nth f ls nil n)
      | [ |- index_points_to_binop _ (S _) _ ] => rewrite index_points_to_binop_S2
      | [ H : context[length (take _ _)] |- _ ] => rewrite take_length in H
      | [ H : context[length (drop _ _)] |- _ ] => rewrite drop_length in H
      | [ H : context[drop 0 _] |- _ ] => rewrite drop_0 in H || setoid_rewrite drop_0 in H
      | [ H : context[drop _ (drop _ _)] |- _ ] => rewrite drop_drop in H || setoid_rewrite drop_drop in H
      | [ H : context[take _ (take _ _)] |- _ ] => rewrite take_take in H || setoid_rewrite take_take in H
      | [ H : context[get 0 ?str] |- _ ] => erewrite (proj1 (get_0 str _)) in H by eassumption
      | [ H : context[get 0 (take 0 _)] |- _ ]
        => rewrite has_first_char_nonempty in H by (rewrite take_length; reflexivity)
      | [ |- context[get 0 ?str] ] => erewrite (proj1 (get_0 str _)) by eassumption
      | [ |- context[get 0 (take 0 _)] ]
        => rewrite has_first_char_nonempty by (rewrite take_length; reflexivity)
      | [ H : get 0 _ = Some _ |- _ ] => apply get_0 in H
      | [ H : get 0 _ = None |- _ ] => apply no_first_char_empty in H
      | [ H : context[(take ?n ?str ~= [ _ ])%string_like] |- _ ]
        => pose proof (length_singleton _ _ H);
          progress apply take_n_1_singleton in H
      | [ |- index_not_points_to_binop 0 0 _ ] => eapply index_not_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
      | [ |- index_points_to_binop 0 0 _ ] => eapply index_points_to_binop_spec; [ simpl; rewrite ?drop_0; eassumption | ]
      | [ |- index_points_to_binop (S _) _ _ ] => rewrite index_points_to_binop_S1
      | [ |- index_not_points_to_binop (S _) _ _ ] => rewrite index_not_points_to_binop_S1
      | [ |- index_points_to_binop _ (S _) _ ] => rewrite index_points_to_binop_S2
      | [ |- index_not_points_to_binop _ (S _) _ ] => rewrite index_not_points_to_binop_S2
      | _ => solve [ eauto with nocore ]
    end.

  Local Ltac t := repeat t'.

  Lemma tables_agree {HSLP : StringLikeProperties Char}
        {level str offset}
  : nth offset (map (fun ls => nth level ls None) (list_of_next_bin_ops' str)) None
    = compute_next_bin_op' (drop offset str) level.
  Proof.
    revert level offset.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len.
    revert str.
    induction len; simpl; intros str Hlen level offset.
    { hnf.
      rewrite compute_next_bin_op'_nil, list_of_next_bin_ops'_nil by (rewrite ?drop_length; omega).
      destruct offset; reflexivity. }
    { specialize (IHlen (drop 1 str)).
      specialize_by (rewrite drop_length; omega).
      setoid_rewrite drop_drop in IHlen.
      t_eq.
      rewrite list_of_next_bin_ops'_recr.
      destruct (get 0 str) eqn:H'; [ | solve [ t ] ].
      destruct offset as [|offset].
      { rewrite compute_next_bin_op'_recr.
        rewrite drop_0, H'.
        unfold list_of_next_bin_ops'_step; simpl.
        rewrite drop_0.
        unfold compute_next_bin_op'_step, list_of_next_bin_ops'_step'.
        rewrite <- !IHlen; clear IHlen.
        repeat match goal with
                 | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                 | _ => progress t
                 | _ => reflexivity
               end;
          match goal with
            | [ |- context[nth ?n (map ?f ?ls) _] ] => simpl rewrite <- (map_nth f ls nil n)
          end;
          destruct level; reflexivity. }
      { rewrite <- IHlen; clear IHlen.
        reflexivity. } }
  Qed.

  Definition list_of_next_bin_ops_spec''_0_0_bin_op {HSLP : StringLikeProperties Char} {table str idx ch}
             (H_ch : (take 1 str ~= [ch])%string_like)
             (H : is_bin_op ch)
  : list_of_next_bin_ops_spec'' 0 (Some 0 :: table) str 0 idx.
  Proof.
    hnf; t.
  Qed.

  Lemma cell_of_next_bin_ops_spec''_compute_next_bin_op' {HSLP : StringLikeProperties Char}
        {level str offset idx}
  : cell_of_next_bin_ops_spec'' level (compute_next_bin_op' (drop offset str) level) str offset idx.
  Proof.
    revert level offset idx.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len.
    revert str.
    induction len; simpl; intros str Hlen level offset idx.
    { hnf.
      rewrite compute_next_bin_op'_nil by (rewrite drop_length; omega).
      repeat split; intros.
      { apply index_points_to_binop_nil; omega. }
      { congruence. }
      { apply index_not_points_to_binop_nil; omega. } }
    { specialize (IHlen (drop 1 str)).
      specialize_by (rewrite drop_length; omega).
      setoid_rewrite drop_drop in IHlen; t_eq.
      destruct offset as [|offset];
        [
        | solve [ eauto using cell_of_next_bin_op_spec''_S_offset with nocore ] ].
      rewrite drop_0.
      specialize (fun level => IHlen level 0).
      split.
      { specialize (fun level => IHlen level (pred idx)).
        destruct idx as [|idx].
        { clear IHlen.
          rewrite compute_next_bin_op'_recr.
          unfold compute_next_bin_op'_step.
          repeat match goal with
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end;
          t. }
        { rewrite compute_next_bin_op'_recr.
          repeat match goal with
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end;
            [ | solve [ t ] ].
          rewrite paren_balanced_hiding'_recr.
          repeat match goal with
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end;
            [ | solve [ t ] ].
          unfold compute_next_bin_op'_step, paren_balanced_hiding'_step, paren_balanced'_step, cell_of_next_bin_ops_spec'' in *.
          repeat match goal with
                   | _ => progress t
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                   | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
                 end. } }
      { specialize (fun level => IHlen level (pred idx)).
        destruct idx as [|idx].
        { clear IHlen.
          rewrite compute_next_bin_op'_recr, paren_balanced'_recr.
          unfold compute_next_bin_op'_step, paren_balanced'_step.
          repeat match goal with
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end;
          t. }
        { simpl in *.
          rewrite compute_next_bin_op'_recr.
          repeat match goal with
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end;
            [ | solve [ t ] ].
          rewrite paren_balanced'_recr.
          repeat match goal with
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                 end;
            [ | solve [ t ] ].
          unfold compute_next_bin_op'_step, paren_balanced'_step, cell_of_next_bin_ops_spec'' in *.
          repeat match goal with
                   | _ => progress t
                   | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                   | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
                 end. } } }
  Qed.

  Lemma list_of_next_bin_ops'_satisfies_spec {HSLP : StringLikeProperties Char} (str : String)
  : forall n,
      list_of_next_bin_ops_spec' n (map (fun ls => nth n ls None) (list_of_next_bin_ops' str)) str.
  Proof.
    unfold list_of_next_bin_ops_spec'.
    intros n offset idx.
    unfold list_of_next_bin_ops_spec''.
    rewrite tables_agree.
    apply cell_of_next_bin_ops_spec''_compute_next_bin_op'.
  Qed.

  Lemma list_of_next_bin_ops_satisfies_spec {HSLP : StringLikeProperties Char} (str : String)
  : list_of_next_bin_ops_spec (list_of_next_bin_ops str) str.
  Proof.
    apply list_of_next_bin_ops'_satisfies_spec.
  Qed.
End make_table.

Section for_string.
  Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.
  Context {pdata : paren_balanced_hiding_dataT Ascii.ascii}.

  Definition list_of_next_bin_ops'_step'_opt
    := (fun ch (table_higher_ops : option (list (option nat)) * list (option nat)) =>
          let next_ops := map (option_map S) (match fst table_higher_ops with
                                                | None => nil
                                                | Some ls => ls
                                              end) in
          let '(cur_mark, new_higher_ops) := (nth 0 next_ops None, tl next_ops) in
          (Some (if is_bin_op ch
                 then Some 0 :: new_higher_ops
                 else if is_open ch
                      then new_higher_ops
                      else if is_close ch
                           then None :: next_ops
                           else next_ops))).

  Definition list_of_next_bin_ops'_step_opt
    := (fun ch table_higher_ops =>
          (list_of_next_bin_ops'_step'_opt ch table_higher_ops,
           (match fst table_higher_ops with
              | Some ls => nth 0 ls None :: snd table_higher_ops
              | None => snd table_higher_ops
            end))).

  Definition list_of_next_bin_ops'_opt0 (str : String)
  : option (list (option nat)) * list (option nat)
    := fold
         list_of_next_bin_ops'_step_opt
         (None, nil)
         str.

  Section no_fold.
    Local Arguments fold / _ _ _ _ _ _ _.
    Local Arguments fold' / _ _ _ _ _ _ _ _.
    Local Arguments list_of_next_bin_ops'_opt0 / _.
    Local Arguments list_of_next_bin_ops'_step_opt / _ _.
    Local Arguments list_of_next_bin_ops'_step'_opt / _ _.
    Definition list_of_next_bin_ops'_opt (str : String)
    : option (list (option nat)) * list (option nat)
      := Eval simpl in list_of_next_bin_ops'_opt0 str.
  End no_fold.

  Definition list_of_next_bin_ops_opt (str : String)
    := let ls' := list_of_next_bin_ops'_opt str in
       match fst ls' with
         | Some ls'' => nth 0 ls'' None :: snd ls'
         | None => snd ls'
       end.

  Lemma list_of_next_bin_ops'_opt_correct (str : String)
  : list_of_next_bin_ops'_opt str
    = (nth 0 (map Some (list_of_next_bin_ops' str)) None,
       tl (map (fun ls => nth 0 ls None) (list_of_next_bin_ops' str))).
  Proof.
    change list_of_next_bin_ops'_opt with list_of_next_bin_ops'_opt0.
    unfold list_of_next_bin_ops', list_of_next_bin_ops'_opt0.
    set (len := length str).
    generalize (eq_refl : length str = len).
    clearbody len.
    revert str.
    induction len; intros str H'.
    { rewrite !fold_nil by assumption; reflexivity. }
    { specialize (IHlen (drop 1 str)).
      specialize_by (rewrite drop_length; omega).
      rewrite !(fold_recr _ _ str).
      destruct (get 0 str) eqn:H''.
      { unfold list_of_next_bin_ops'_step_opt at 1.
        rewrite !IHlen; clear IHlen.
        unfold list_of_next_bin_ops'_step'_opt.
        generalize (fold list_of_next_bin_ops'_step [] (drop 1 str)).
        intros ls'.
        unfold list_of_next_bin_ops'_step.
        unfold list_of_next_bin_ops'_step'.
        repeat match goal with
                 | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                 | _ => progress cbv beta
                 | [ |- context[fst (?x, ?y)] ] =>
                   change (fst (x, y)) with x
                 | [ |- context[snd (?x, ?y)] ] =>
                   change (snd (x, y)) with y
                 | [ |- context[nth 0 (?x::?xs) ?v] ]
                   => change (nth 0 (x::xs) v) with x
                 | [ |- (_, _) = (_, _) ] => apply f_equal2
                 | [ |- context[map ?f (?x::?xs)] ]
                   => change (map f (x::xs)) with (f x :: map f xs)
                 | [ |- Some _ = Some _ ] => apply f_equal
                 | [ |- _::_ = _::_ ] => apply f_equal2
                 | _ => reflexivity
                 | [ |- context[nth 0 (map Some ?ls) None] ]
                   => is_var ls; destruct ls
               end. }
      { reflexivity. } }
  Qed.

  Lemma list_of_next_bin_ops_opt_correct (str : String)
  : list_of_next_bin_ops_opt str = list_of_next_bin_ops str.
  Proof.
    unfold list_of_next_bin_ops_opt, list_of_next_bin_ops.
    rewrite !list_of_next_bin_ops'_opt_correct.
    simpl.
    generalize (list_of_next_bin_ops' str).
    intro ls'.
    destruct ls'; simpl; reflexivity.
  Qed.

  Lemma list_of_next_bin_ops_opt_satisfies_spec (str : String)
  : list_of_next_bin_ops_spec (list_of_next_bin_ops_opt str) str.
  Proof.
    rewrite list_of_next_bin_ops_opt_correct.
    apply list_of_next_bin_ops_satisfies_spec.
  Qed.
End for_string.

Section no_records.
  Section specialized.
    Context {String : Type}.

    Class list_of_next_bin_ops_opt_data :=
      { is_open : Ascii.ascii -> bool;
        is_close : Ascii.ascii -> bool;
        is_bin_op : Ascii.ascii -> bool;
        length : String -> nat;
        get : nat -> String -> option Ascii.ascii;
        unsafe_get : nat -> String -> Ascii.ascii }.
    Context {ldata : list_of_next_bin_ops_opt_data}.

    Section exploded.
      Context (char_at_matches : nat -> String -> (Ascii.ascii -> bool) -> bool)
              (is_char : String -> Ascii.ascii -> bool)
              (take : nat -> String -> String)
              (drop : nat -> String -> String)
              (bool_eq : String -> String -> bool).

      Local Instance temp_pbh : paren_balanced_hiding_dataT Ascii.ascii
        := { is_open := is_open;
             is_close := is_close;
             is_bin_op := is_bin_op }.

      Local Instance temp_hslm : StringLikeMin Ascii.ascii
        := { length := length;
             unsafe_get := unsafe_get;
             char_at_matches := char_at_matches }.

      Local Instance temp_hsl : StringLike Ascii.ascii
        := { is_char := is_char;
             drop := drop;
             take := take;
             get := get;
             bool_eq := bool_eq }.

      Local Arguments list_of_next_bin_ops'_opt / _ _ _ _.
      Definition list_of_next_bin_ops'_opt_nor' (str : String)
      : option (list (option nat)) * list (option nat)
        := Eval simpl in list_of_next_bin_ops'_opt (str : @StringLike.String _ temp_hslm).
    End exploded.

    Definition list_of_next_bin_ops'_opt_nor (str : String)
    : option (list (option nat)) * list (option nat)
      := Eval unfold list_of_next_bin_ops'_opt_nor' in list_of_next_bin_ops'_opt_nor' str.

    Definition list_of_next_bin_ops_opt_nor (str : String)
      := let ls' := list_of_next_bin_ops'_opt_nor str in
         match fst ls' with
           | Some ls'' => nth 0 ls'' None :: snd ls'
           | None => snd ls'
         end.
  End specialized.

  Section correct.
    Context {HSLM : StringLikeMin Ascii.ascii} {HSL : StringLike Ascii.ascii} {HSLP : StringLikeProperties Ascii.ascii}.
    Context {pdata : paren_balanced_hiding_dataT Ascii.ascii}.

    Global Instance default_list_of_next_bin_ops_opt_data : list_of_next_bin_ops_opt_data
      := { is_open := ParenBalanced.Core.is_open;
           is_close := ParenBalanced.Core.is_close;
           is_bin_op := ParenBalanced.Core.is_bin_op;
           length := StringLike.length;
           get := StringLike.get;
           unsafe_get := StringLike.unsafe_get }.

    Lemma list_of_next_bin_ops'_opt_nor_correct (str : String)
    : list_of_next_bin_ops'_opt_nor str
      = (nth 0 (map Some (list_of_next_bin_ops' str)) None,
         tl (map (fun ls => nth 0 ls None) (list_of_next_bin_ops' str))).
    Proof.
      exact (list_of_next_bin_ops'_opt_correct str).
    Qed.

    Lemma list_of_next_bin_ops_opt_nor_correct (str : String)
    : list_of_next_bin_ops_opt_nor str = list_of_next_bin_ops str.
    Proof.
      exact (list_of_next_bin_ops_opt_correct str).
    Qed.

    Lemma list_of_next_bin_ops_opt_nor_satisfies_spec (str : String)
    : list_of_next_bin_ops_spec (list_of_next_bin_ops_opt_nor str) str.
    Proof.
      exact (list_of_next_bin_ops_opt_satisfies_spec str).
    Qed.
  End correct.
End no_records.
