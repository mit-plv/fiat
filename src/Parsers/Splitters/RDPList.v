(** * Definition of the part of boolean-returning CFG parser-recognizer that instantiates things to lists *)
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.

Set Implicit Arguments.
Local Open Scope type_scope.
Local Open Scope string_like_scope.

Local Arguments leb !_ !_.

Section recursive_descent_parser_list.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HLSP : StringLikeProperties Char} {G : pregrammar' Char}
          (Char_beq : Char -> Char -> bool).
  Definition rdp_list_nonterminals_listT : Type := list nat.
  Notation rdp_list_nonterminal_carrierT := default_nonterminal_carrierT.
  (** (nonterminal, production_index, drop_count) *)
  Notation rdp_list_production_carrierT := default_production_carrierT.

  Definition list_bin_eq
    := Eval unfold list_bin in list_bin EqNat.beq_nat.

  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> bool
    := fun ls nt => list_bin_eq nt ls.

  Local Ltac fix_list_bin_eq :=
    unfold rdp_list_is_valid_nonterminal;
    change list_bin_eq with (list_bin EqNat.beq_nat) in *.

  Local Notation valid_nonterminals := (map fst (pregrammar_productions G)).

  Definition rdp_list_initial_nonterminals_data
  : rdp_list_nonterminals_listT
    := up_to (List.length valid_nonterminals).

  Definition rdp_list_of_nonterminal
  : String.string -> rdp_list_nonterminal_carrierT
    := default_of_nonterminal (G := G).
  Definition rdp_list_to_nonterminal
  : rdp_list_nonterminal_carrierT -> String.string
    := default_to_nonterminal (G := G).

  Definition rdp_list_to_production : rdp_list_production_carrierT -> production Char
    := default_to_production (G := G).

  Definition rdp_list_nonterminal_to_production : rdp_list_nonterminal_carrierT -> list rdp_list_production_carrierT
    := fun nt_idx
       => List.map
            (fun p_idx : nat => (nt_idx, (p_idx, 0)))
            (up_to (List.length (Lookup G (rdp_list_to_nonterminal nt_idx)))).

  Definition rdp_list_production_tl : rdp_list_production_carrierT -> rdp_list_production_carrierT
    := (default_production_tl (G := G)).


  Local Ltac t' :=
    idtac;
    match goal with
      | _ => assumption
      | _ => omega
      | _ => congruence
      | _ => discriminate
      | [ H : first_index_error _ _ = Some _ |- _ ] => apply first_index_error_Some_correct in H
      | [ H : first_index_error _ _ = None |- _ ] => rewrite first_index_error_None_correct in H
      | _ => intro
      | [ H : and _ _ |- _ ] => destruct H
      | [ H : ex _ |- _ ] => destruct H
      | [ H : string_beq _ _ = true |- _ ] => apply string_bl in H
      | _ => progress subst
      | [ |- nth _ _ _ = _ ] => apply nth_error_Some_nth
      | [ H : ?T |- _ <-> ?T ] => split; [ intro; assumption | intro ]
      | [ H : is_true (list_bin _ _ _) |- _ ] => apply (list_in_bl (@beq_nat_true)) in H
      | [ |- is_true (list_bin _ _ _) ] => apply list_in_lb; [ intros ???; subst; symmetry; apply beq_nat_refl | ]
      | [ H : In _ (up_to _) |- _ ] => apply in_up_to_iff in H
      | [ |- In _ (up_to _) ] => apply in_up_to_iff
      | [ H : In ?nt _ |- _ ] => let H' := fresh in assert (H' : string_beq nt nt = false) by eauto; exfalso; clear -H'
      | [ H : context[string_beq ?x ?x] |- _ ] => rewrite (string_lb eq_refl) in H
      | [ |- _ <-> _ ] => split
      | [ |- In (nth _ ?ls _) ?ls ] => apply nth_In; assumption
      | [ H : nth_error _ _ = Some _ |- _ ]
        => let H' := fresh in
           pose proof H as H';
             apply nth_error_In in H;
             apply nth_error_Some_short in H'
      | [ |- ?x < ?y ] => destruct (le_lt_dec y x); [ exfalso | assumption ]
      | [ H : context[nth ?nt ?ls ?d] |- _ ]
        => rewrite nth_overflow in H by assumption
      | [ H : In some_invalid_nonterminal _ |- _ ]
        => apply some_invalid_nonterminal_invalid in H
      | _ => progress simpl in *
      | [ |- In (nth _ (uniquize ?beq ?ls) _) ?ls ]
        => apply (uniquize_In _ beq)
      | [ H : In ?x (uniquize ?beq ?ls) |- In ?x ?ls ]
        => eapply uniquize_In; eexact H
      | [ H : forall elem, In elem (uniquize ?beq ?ls) -> ?beq ?nt elem = false,
            H' : In ?nt ?ls
            |- _ ]
        => exfalso; specialize (H nt)
      | _ => progress specialize_by (apply uniquize_In_refl; first [ apply string_lb; reflexivity | apply @string_bl | assumption ])
    end.

  Local Ltac t := repeat t'.

  Definition rdp_list_initial_nonterminals_correct'
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt) <-> List.In (rdp_list_to_nonterminal nt) (Valid_nonterminals G).
  Proof.
    fix_list_bin_eq.
    unfold rdp_list_is_valid_nonterminal, rdp_list_to_nonterminal, rdp_list_initial_nonterminals_data, default_to_nonterminal.
    intro nt.
    t.
  Qed.

  Definition rdp_list_initial_nonterminals_correct
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data (rdp_list_of_nonterminal nt)) <-> List.In nt (Valid_nonterminals G).
  Proof.
    fix_list_bin_eq.
    unfold rdp_list_is_valid_nonterminal, rdp_list_of_nonterminal, rdp_list_initial_nonterminals_data, default_of_nonterminal.
    intro nt.
    rewrite first_index_default_first_index_error.
    destruct (first_index_error (string_beq nt) valid_nonterminals) eqn:H'; t.
  Qed.

  Lemma rdp_list_find_to_nonterminal idx
  : List.first_index_error
      (string_beq (rdp_list_to_nonterminal idx))
      valid_nonterminals
    = bool_rect
        (fun _ => option _)
        (Some idx)
        (None)
        (Compare_dec.leb (S idx) (List.length valid_nonterminals)).
  Proof.
    apply default_find_to_nonterminal.
  Qed.

  Lemma rdp_list_to_of_nonterminal
  : forall nt,
      List.In nt (Valid_nonterminals G)
      -> rdp_list_to_nonterminal (rdp_list_of_nonterminal nt) = nt.
  Proof.
    unfold rdp_list_to_nonterminal, rdp_list_of_nonterminal, default_to_nonterminal, default_of_nonterminal.
    intro nt.
    rewrite first_index_default_first_index_error.
    destruct (first_index_error (string_beq nt) valid_nonterminals) eqn:H';
      t.
  Qed.

  Lemma rdp_list_of_to_nonterminal
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt)
      -> rdp_list_of_nonterminal (rdp_list_to_nonterminal nt) = nt.
  Proof.
    pose proof (nonterminals_unique G) as HNoDup.
    hnf in HNoDup.
    simpl in *.
    unfold rdp_list_to_nonterminal, rdp_list_of_nonterminal, rdp_list_is_valid_nonterminal, rdp_list_initial_nonterminals_data, default_to_nonterminal, default_of_nonterminal.
    intros nt H.
    apply (list_in_bl (@beq_nat_true)), in_up_to_iff in H.
    revert nt H.
    replace valid_nonterminals with (uniquize string_beq valid_nonterminals) by (rewrite HNoDup; reflexivity).
    induction valid_nonterminals as [|x xs IHxs].
    { simpl; intros; omega. }
    { simpl in *.
      destruct (list_bin string_beq x (uniquize string_beq xs)) eqn:Hbin; try assumption.
      { apply (f_equal (@List.length _)) in HNoDup.
        simpl in *.
        pose proof (uniquize_shorter xs string_beq) as H'.
        rewrite HNoDup in H'.
        exfalso; clear -H'.
        omega. }
      apply (f_equal (@tl _)) in HNoDup; simpl @tl in HNoDup.
      specialize_by assumption.

      intros [|nt].
      { simpl.
        rewrite (string_lb eq_refl); trivial. }
      { simpl Datatypes.length.
        intro H.
        apply lt_S_n in H.
        etransitivity; [ | eapply (f_equal S), (IHxs _ H); clear IHxs ].
        rewrite first_index_default_S_cons; simpl.
        match goal with
          | [ |- context[string_beq ?x ?y] ]
            => destruct (string_beq x y) eqn:H'
        end; simpl;
        [ exfalso | reflexivity ].
        clear -Hbin H H'.
        apply string_bl in H'.
        subst.
        rewrite list_in_lb in Hbin; [ congruence | apply @string_lb | ].
        apply nth_In; assumption. } }
  Qed.

  Definition rdp_list_production_carrier_valid
  : rdp_list_production_carrierT -> bool
    := default_production_carrier_valid (G := G).

  Lemma rdp_list_production_tl_correct
  : forall p,
      rdp_list_to_production (rdp_list_production_tl p) = tl (rdp_list_to_production p).
  Proof.
    unfold rdp_list_to_production, rdp_list_production_tl, default_production_tl, default_to_production; simpl.
    intros [? [? p]]; rewrite tl_drop; simpl.
    do 2 try
       match goal with
         | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?; simpl
       end;
      repeat match goal with
               | _ => destruct p; reflexivity
               | _ => assumption
               | _ => omega
               | [ H : leb _ _ = false |- _ ] => apply leb_iff_conv in H
               | [ H : ?x < 1 |- _ ] => assert (x = 0) by omega; clear H
               | [ H : ?x = 0 |- context[?x] ] => rewrite H
               | [ H : ?x = nil |- context[?x] ] => rewrite H
               | [ H : List.length ?x = 0 |- _ ] => assert (x = nil) by (destruct x; simpl in *; trivial; discriminate); clear H
               | _ => progress simpl in *
               | _ => reflexivity
               | [ H : _ < S _ |- _ ] => apply le_S_n in H
               | _ => rewrite drop_all by assumption
               | [ |- nil = drop _ _ ] => symmetry; apply drop_all
               | [ |- context[List.length (tl ?x)] ] => destruct x eqn:?
             end.
  Qed.

  Local Arguments List.nth _ !_ !_ _.
  Local Arguments minus !_ !_.

  Lemma rdp_list_nonterminal_to_production_correct
  : forall nt,
      List.In nt (Valid_nonterminals G)
      -> List.map rdp_list_to_production (rdp_list_nonterminal_to_production (rdp_list_of_nonterminal nt))
         = Lookup G nt.
  Proof.
    intros nt Hvalid.
    unfold rdp_list_to_production, rdp_list_nonterminal_to_production, default_to_production.
    rewrite map_map; simpl.
    rewrite !rdp_list_to_of_nonterminal by assumption.
    rewrite <- list_to_productions_to_nonterminal.
    change default_to_nonterminal with rdp_list_to_nonterminal.
    rewrite rdp_list_to_of_nonterminal by assumption.
    induction (Lookup_string G nt) as [|p ps IHps]; simpl.
    { reflexivity. }
    { simpl.
      rewrite minus_diag; simpl.
      apply f_equal.
      etransitivity; [ | apply IHps ]; clear IHps.
      apply map_ext_in.
      intros a H; apply in_up_to_iff in H.
      rewrite NPeano.Nat.sub_succ_r.
      destruct (Datatypes.length ps - a) eqn:H'; try omega; [].
      reflexivity. }
  Qed.

  Lemma rdp_list_production_tl_valid
  : forall p,
      rdp_list_production_carrier_valid p -> rdp_list_production_carrier_valid (rdp_list_production_tl p).
  Proof.
    unfold rdp_list_production_carrier_valid, default_production_carrier_valid, rdp_list_production_tl, default_production_tl; simpl; trivial.
    repeat match goal with
             | _ => progress simpl in *
             | _ => intro
             | _ => progress unfold is_true in *
             | [ |- andb ?x ?y = true ] => apply Bool.andb_true_iff
             | [ H : andb ?x ?y = true |- _ ] => apply Bool.andb_true_iff in H
             | [ H : and _ _ |- _ ] => destruct H
             | [ H : ?x = true |- context[?x] ] => rewrite H
             | [ |- ?x = ?x ] => reflexivity
             | [ |- and _ _ ] => split
             | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
           end.
  Qed.

  Local Arguments leb !_ !_.

  Lemma rdp_list_nonterminal_to_production_valid
  : forall nt,
      rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt
      -> List.Forall rdp_list_production_carrier_valid (rdp_list_nonterminal_to_production nt).
  Proof.
    unfold rdp_list_production_carrier_valid, rdp_list_is_valid_nonterminal, rdp_list_initial_nonterminals_data, rdp_list_nonterminal_to_production.
    intros nt Hnt.
    apply Forall_map, Forall_forall; unfold compose; simpl; intros ? H.
    fix_list_bin_eq.
    apply list_in_bl in Hnt; [ | exact (EqNat.beq_nat_true) ].
    apply in_up_to_iff in Hnt.
    unfold default_production_carrier_valid; simpl.
    repeat (apply Bool.andb_true_iff; split); apply leb_iff.
    { rewrite map_length in Hnt.
      exact Hnt. }
    { apply in_up_to_iff in H.
      rewrite <- list_to_productions_to_nonterminal.
      exact H. }
    { omega. }
  Qed.

  Lemma rdp_list_production_carrier_valid_reachable (idx : rdp_list_production_carrierT)
        (Hvalid : rdp_list_production_carrier_valid idx)
  : production_is_reachable G (rdp_list_to_production idx).
  Proof.
    unfold production_is_reachable, rdp_list_production_carrier_valid, default_production_carrier_valid, rdp_list_production_carrierT in *.
    repeat setoid_rewrite Bool.andb_true_iff in Hvalid.
    repeat setoid_rewrite Compare_dec.leb_iff in Hvalid.
    destruct_head and.
    simpl in *.
    exists (rdp_list_to_nonterminal (fst idx)).
    unfold rdp_list_to_production, default_to_production in *; simpl in *.
    match goal with
      | [ |- context[In (_ ++ Operations.List.drop ?n ?ls)%list _] ]
        => exists (Operations.List.take n ls)
    end.
    rewrite app_take_drop.
    split.
    { apply rdp_list_initial_nonterminals_correct'.
      unfold rdp_list_is_valid_nonterminal, rdp_list_initial_nonterminals_data.
      fix_list_bin_eq.
      apply list_in_lb; [ apply beq_nat_true_iff | ].
      rewrite map_length.
      apply in_up_to; assumption. }
    { unfold rdp_list_to_nonterminal.
      rewrite list_to_productions_to_nonterminal.
      destruct (Lookup_idx G (fst idx)) eqn:Heq.
      { simpl in *.
        omega. }
      { apply nth_In.
        simpl; omega. } }
  Qed.

  Definition filter_out_eq nt ls
    := Eval unfold filter_out in filter_out (EqNat.beq_nat nt) ls.

  Definition rdp_list_remove_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> rdp_list_nonterminals_listT
    := fun ls nt =>
         filter_out_eq nt ls.

  Local Ltac fix_filter_out_eq :=
    unfold rdp_list_remove_nonterminal;
    change filter_out_eq with (fun nt ls => filter_out (EqNat.beq_nat nt) ls); cbv beta;
    setoid_rewrite filter_out_filter.

  Local Ltac fix_eqs := try fix_filter_out_eq; try fix_list_bin_eq.

  Definition rdp_list_nonterminals_listT_R : rdp_list_nonterminals_listT -> rdp_list_nonterminals_listT -> Prop
    := ltof _ (@List.length _).
  Lemma filter_list_dec {T} f (ls : list T) : List.length (filter f ls) <= List.length ls.
  Proof.
    induction ls; trivial; simpl in *.
    repeat match goal with
             | [ |- context[if ?a then _ else _] ] => destruct a; simpl in *
             | [ |- S _ <= S _ ] => solve [ apply Le.le_n_S; auto ]
             | [ |- _ <= S _ ] => solve [ apply le_S; auto ]
           end.
  Qed.
  Lemma rdp_list_remove_nonterminal_dec : forall ls prods,
                                            @rdp_list_is_valid_nonterminal ls prods = true
                                            -> @rdp_list_nonterminals_listT_R (@rdp_list_remove_nonterminal ls prods) ls.
  Proof.
    intros ls prods H.
    unfold rdp_list_is_valid_nonterminal, rdp_list_nonterminals_listT_R, rdp_list_remove_nonterminal, ltof in *.
    fix_eqs.
    apply list_in_bl in H; [ | solve [ intros; apply beq_nat_true; trivial ] ].
    match goal with
      | [ H : In ?prods ?ls |- context[filter ?f ?ls] ]
        => assert (~In prods (filter f ls))
    end.
    { intro H'.
      apply filter_In in H'.
      destruct H' as [? H'].
      rewrite <- beq_nat_refl in H'.
      simpl in *; congruence. }
    { match goal with
        | [ |- context[filter ?f ?ls] ] => generalize dependent f; intros
      end.
      induction ls; simpl in *; try congruence.
      repeat match goal with
               | [ |- context[if ?x then _ else _] ] => destruct x; simpl in *
               | [ H : _ \/ _ |- _ ] => destruct H
               | _ => progress subst
               | [ H : ~(_ \/ _) |- _ ] => apply Decidable.not_or in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : ?x <> ?x |- _ ] => exfalso; apply (H eq_refl)
               | _ => apply Lt.lt_n_S
               | _ => apply Le.le_n_S
               | _ => apply filter_list_dec
               | [ H : _ -> _ -> ?G |- ?G ] => apply H; auto
             end. }
  Qed.
  Lemma rdp_list_ntl_wf : well_founded rdp_list_nonterminals_listT_R.
  Proof.
    unfold rdp_list_nonterminals_listT_R.
    intro.
    apply well_founded_ltof.
  Defined.

  Lemma rdp_list_remove_nonterminal_1
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = true
      -> rdp_list_is_valid_nonterminal ls ps' = true.
  Proof.
    unfold rdp_list_is_valid_nonterminal, rdp_list_remove_nonterminal.
    fix_eqs.
    repeat match goal with
             | _ => exfalso; congruence
             | _ => reflexivity
             | _ => assumption
             | [ |- context[if ?E then _ else _] ] => destruct E
             | _ => intro
             | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
             | [ H : list_bin _ _ _ = true |- _ ] => apply list_in_bl in H; [ | solve [ intros; apply beq_nat_true; trivial ] ]
             | [ |- list_bin _ _ _ = true ] => apply list_in_lb
             | _ => progress subst
             | [ |- context[beq_nat ?x ?x] ] => rewrite <- beq_nat_refl
           end.
  Qed.

  Lemma rdp_list_remove_nonterminal_2
  : forall ls ps ps',
      rdp_list_is_valid_nonterminal (rdp_list_remove_nonterminal ls ps) ps' = false
      <-> rdp_list_is_valid_nonterminal ls ps' = false \/ ps = ps'.
  Proof.
    unfold rdp_list_is_valid_nonterminal, rdp_list_remove_nonterminal.
    fix_eqs.
    repeat match goal with
             | _ => exfalso; congruence
             | _ => reflexivity
             | _ => progress subst
             | _ => intro
             | [ H : @eq bool ?x ?y -> False |- _ ] => apply Bool.eq_true_not_negb in H
             | [ H : context[In _ (filter _ _)] |- _ ] => rewrite filter_In in H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : ?T, H' : ~?T |- _ ] => destruct (H' H)
             | [ |- true = false \/ _ ] => right
             | [ |- ?x = ?x \/ _ ] => left; reflexivity
             | [ H : ~(_ /\ ?x = ?x) |- _ ] => specialize (fun y => H (conj y eq_refl))
             | [ H : ~(?T /\ _), H' : ?T |- _ ] => specialize (fun y => H (conj H' y))
             | [ H : (?T /\ _) -> False, H' : ?T |- _ ] => specialize (fun y => H (conj H' y))
             | [ H : _ \/ _ |- _ ] => destruct H
             | [ |- _ <-> _ ] => split
             | [ H : context[match ?E with left _ => _ | right _ => _ end] |- _ ] => destruct E
             | [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
             | [ H : _ |- _ ] => rewrite Bool.negb_involutive in H
             | [ H : string_beq _ _ = true |- _ ] => apply string_bl in H
             | [ H : context[string_beq ?x ?x] |- _ ] => rewrite (string_lb (eq_refl x)) in H
             | _ => progress simpl in *
             | [ H : list_bin _ _ _ = true |- _ ] => apply list_in_bl in H; [ | solve [ intros; apply beq_nat_true; trivial ] ]
             | [ |- list_bin _ _ _ = true ] => apply list_in_lb
             | [ |- context[list_bin ?x ?y ?z = false] ] => case_eq (list_bin x y z)
             | [ H : list_bin _ _ _ = false |- _ ] => apply Bool.not_true_iff_false in H
             | [ H : list_bin _ _ _ <> true |- _ ] => specialize (fun pf H' => H (list_in_lb pf H'))
             | [ H : ?A -> ?B |- _ ]
               => let H' := fresh in
                  assert (H' : A) by (intros; subst; rewrite <- ?beq_nat_refl; reflexivity);
                    specialize (H H'); clear H'
             | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
             | [ H : context[beq_nat ?x ?x] |- _ ] => rewrite <- beq_nat_refl in H
           end.
  Qed.

  Lemma rdp_list_remove_nonterminal_noninc (ls : rdp_list_nonterminals_listT) nonterminal
  : ~ rdp_list_nonterminals_listT_R ls (rdp_list_remove_nonterminal ls nonterminal).
  Proof.
    simpl. unfold ltof, rdp_list_remove_nonterminal.
    fix_eqs.
    intro H.
    cut (Datatypes.length ls < Datatypes.length ls); try omega.
    eapply Lt.lt_le_trans; [ eassumption | ].
    apply filter_list_dec.
  Qed.

  Lemma rdp_list_nonterminals_length_zero
  : forall ls,
      List.length ls = 0
      -> forall nt, rdp_list_is_valid_nonterminal ls nt = false.
  Proof.
    destruct ls; simpl; trivial; intro; exfalso; omega.
  Qed.

  Lemma rdp_list_is_valid_nonterminal_nth_error
        nt_idx
    : rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt_idx
      <-> nth_error (pregrammar_productions G) nt_idx <> None.
  Proof.
    unfold rdp_list_is_valid_nonterminal; fix_eqs.
    transitivity (List.In nt_idx rdp_list_initial_nonterminals_data).
    { split; intro H.
      { apply list_in_bl in H; [ assumption | apply Nat.eqb_eq ]. }
      { apply list_in_lb; [ apply Nat.eqb_eq | assumption ]. } }
    unfold rdp_list_initial_nonterminals_data.
    rewrite <- in_up_to_iff, map_length.
    rewrite nth_error_Some; reflexivity.
  Qed.

  Global Instance rdp_list_predata : @parser_computational_predataT Char
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := rdp_list_initial_nonterminals_data;
         of_nonterminal := rdp_list_of_nonterminal;
         to_nonterminal := rdp_list_to_nonterminal;
         production_carrierT := rdp_list_production_carrierT;
         to_production := rdp_list_to_production;
         nonterminal_to_production := rdp_list_nonterminal_to_production;
         production_tl := rdp_list_production_tl;
         production_carrier_valid := rdp_list_production_carrier_valid;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_length := @List.length _ }.

  Global Instance rdp_list_rdata' : @parser_removal_dataT' _ G rdp_list_predata
    := { nonterminals_length_zero := rdp_list_nonterminals_length_zero;
         remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         remove_nonterminal_noninc := rdp_list_remove_nonterminal_noninc;
         to_of_nonterminal := rdp_list_to_of_nonterminal;
         of_to_nonterminal := rdp_list_of_to_nonterminal;
         production_tl_correct := rdp_list_production_tl_correct;
         nonterminal_to_production_correct := rdp_list_nonterminal_to_production_correct;
         production_tl_valid := rdp_list_production_tl_valid;
         nonterminal_to_production_valid := rdp_list_nonterminal_to_production_valid;
         initial_nonterminals_correct := rdp_list_initial_nonterminals_correct;
         initial_nonterminals_correct' := rdp_list_initial_nonterminals_correct';
         remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2 }.
End recursive_descent_parser_list.
