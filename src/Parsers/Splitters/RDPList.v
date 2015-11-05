(** * Definition of the part of boolean-returning CFG parser-recognizer that instantiates things to lists *)
Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Wf_nat.
Require Import Coq.Strings.Ascii.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section recursive_descent_parser_list.
  Context {Char} {HSL : StringLike Char} {HLSP : StringLikeProperties Char} {G : grammar Char}.
  Definition rdp_list_nonterminals_listT : Type := list nat.
  Definition rdp_list_nonterminal_carrierT : Type := nat.

  Definition list_bin_eq
    := Eval unfold list_bin in list_bin EqNat.beq_nat.

  Definition rdp_list_is_valid_nonterminal : rdp_list_nonterminals_listT -> rdp_list_nonterminal_carrierT -> bool
    := fun ls nt => list_bin_eq nt ls.

  Local Ltac fix_list_bin_eq :=
    unfold rdp_list_is_valid_nonterminal;
    change list_bin_eq with (list_bin EqNat.beq_nat) in *.

  Definition rdp_list_initial_nonterminals_data
  : rdp_list_nonterminals_listT
    := up_to (List.length (Valid_nonterminals G)).

  Definition rdp_list_of_nonterminal
  : String.string -> rdp_list_nonterminal_carrierT
    := fun nt => match first_index_error (string_beq nt) (Valid_nonterminals G) with
                   | Some idx => idx
                   | None => List.length (Valid_nonterminals G)
                 end.
  Fixpoint string_copy (n : nat) (ch : Ascii.ascii)
    := match n with
         | 0 => EmptyString
         | S n' => String.String ch (string_copy n' ch)
       end.
  Lemma string_copy_length n ch
  : String.length (string_copy n ch) = n.
  Proof.
    induction n; simpl; eauto.
  Qed.
  Definition some_invalid_nonterminal
    := string_copy (S (fold_right max 0 (map String.length (Valid_nonterminals G)))) "a"%char.
  Lemma some_invalid_nonterminal_invalid_helper
  : forall x, List.In x (Valid_nonterminals G) -> String.length x < String.length some_invalid_nonterminal.
  Proof.
    unfold some_invalid_nonterminal in *.
    induction (Valid_nonterminals G) as [|x xs IHxs].
    { intros ? []. }
    { intros nt H.
      destruct H as [H|H]; subst.
      { clear IHxs; simpl.
        rewrite string_copy_length; simpl.
        apply Max.max_case_strong; simpl; intros; omega. }
      { specialize (IHxs _ H).
        rewrite string_copy_length in IHxs |- *; simpl in *.
        apply Max.max_case_strong; omega. } }
  Qed.
  Lemma some_invalid_nonterminal_invalid
  : ~List.In some_invalid_nonterminal (Valid_nonterminals G).
  Proof.
    intro H; apply some_invalid_nonterminal_invalid_helper in H.
    omega.
  Qed.
  Definition rdp_list_to_nonterminal
  : rdp_list_nonterminal_carrierT -> String.string
    := fun nt => nth nt (Valid_nonterminals G) some_invalid_nonterminal.

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
      | [ H : In some_invalid_nonterminal (Valid_nonterminals G) |- _ ]
        => apply some_invalid_nonterminal_invalid in H
    end.

  Local Ltac t := repeat t'.

  Definition rdp_list_initial_nonterminals_correct'
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt) <-> List.In (rdp_list_to_nonterminal nt) (Valid_nonterminals G).
  Proof.
    fix_list_bin_eq.
    unfold rdp_list_is_valid_nonterminal, rdp_list_to_nonterminal, rdp_list_initial_nonterminals_data.
    intro nt.
    t.
  Qed.

  Definition rdp_list_initial_nonterminals_correct
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data (rdp_list_of_nonterminal nt)) <-> List.In nt (Valid_nonterminals G).
  Proof.
    fix_list_bin_eq.
    unfold rdp_list_is_valid_nonterminal, rdp_list_of_nonterminal, rdp_list_initial_nonterminals_data.
    intro nt.
    destruct (first_index_error (string_beq nt) (Valid_nonterminals G)) eqn:H'; t.
  Qed.

  Lemma rdp_list_find_to_nonterminal idx
  : Operations.first_index_error
      (string_beq (rdp_list_to_nonterminal idx))
      (Valid_nonterminals G)
    = if list_beq string_beq (Valid_nonterminals G) (uniquize string_beq (Valid_nonterminals G))
      then bool_rect
             (fun _ => option _)
             (Some idx)
             (None)
             (Compare_dec.leb (S idx) (List.length (Valid_nonterminals G)))
      else Operations.first_index_error
             (string_beq (rdp_list_to_nonterminal idx))
             (Valid_nonterminals G).
  Proof.
    destruct (list_beq string_beq (Valid_nonterminals G) (uniquize string_beq (Valid_nonterminals G))) eqn:H; [ | reflexivity ].
    { apply (list_bl (@string_bl)) in H.
      symmetry in H.
      apply uniquize_length in H.
      destruct (leb (S idx) (List.length (Valid_nonterminals G))) eqn:H0; simpl;
      [ apply leb_complete in H0
      | apply leb_complete_conv in H0 ].
      { generalize dependent idx.
        unfold rdp_list_to_nonterminal.
        induction (Valid_nonterminals G) as [|x xs IHxs].
        { simpl; intros; omega. }
        { intros [|idx].
          { simpl.
            rewrite (string_lb eq_refl); trivial. }
          { simpl nth.
            simpl.
            intros.
            simpl in H.
            destruct (list_bin string_beq x (uniquize string_beq xs)) eqn:H''.
            { exfalso; clear -H.
              pose proof (uniquize_shorter xs string_beq).
              omega. }
            { simpl in H.
              rewrite IHxs by omega; clear IHxs.
              repeat match goal with
                       | _ => exact (@string_lb)
                       | _ => progress simpl in *
                       | [ |- context[if ?E then _ else _] ] => destruct E eqn:?
                       | _ => reflexivity
                       | [ |- Some _ = Some _ ] => apply f_equal
                       | [ |- 0 = S _ ] => exfalso
                       | [ H : string_beq _ _ = true |- _ ] => apply string_bl in H
                       | _ => progress subst
                       | [ H : S _ = S _ |- _ ] => apply (f_equal pred) in H
                       | [ H : List.length (uniquize _ _) = List.length _ |- _ ]
                         => apply uniquize_length in H
                       | [ H : uniquize ?beq ?ls = ?ls, H' : context[uniquize ?beq ?ls] |- _ ]
                         => rewrite H in H'
                       | [ H : list_bin _ _ _ = false |- False ]
                         => rewrite list_in_lb in H; [ discriminate | | ]
                       | [ |- In (nth _ _ _) _ ] => apply nth_In; omega
                     end. } } } }
      { unfold rdp_list_to_nonterminal.
        rewrite nth_overflow by omega.
        apply first_index_error_None_correct; intros elem H''.
        destruct (string_beq some_invalid_nonterminal elem) eqn:H'''; trivial.
        apply string_bl in H'''.
        subst.
        apply some_invalid_nonterminal_invalid in H''; destruct H''. } }
  Qed.

  Lemma rdp_list_to_of_nonterminal
  : forall nt,
      List.In nt (Valid_nonterminals G)
      -> rdp_list_to_nonterminal (rdp_list_of_nonterminal nt) = nt.
  Proof.
    unfold rdp_list_to_nonterminal, rdp_list_of_nonterminal.
    intro nt.
    destruct (first_index_error (string_beq nt) (Valid_nonterminals G)) eqn:H';
      t.
  Qed.

  (*Lemma rdp_list_of_to_nonterminal
  : forall nt,
      is_true (rdp_list_is_valid_nonterminal rdp_list_initial_nonterminals_data nt)
      -> rdp_list_of_nonterminal (rdp_list_to_nonterminal nt) = nt.
  Proof.
    unfold rdp_list_to_nonterminal, rdp_list_of_nonterminal, rdp_list_is_valid_nonterminal, rdp_list_initial_nonterminals_data.
    intros nt H.
    apply (list_in_bl (@beq_nat_true)), in_up_to_iff in H.
    revert nt H.
    induction (Valid_nonterminals G) as [|x xs IHxs].
    { simpl; intros; omega. }
    { intros [|nt].
      { simpl.
        rewrite (string_lb eq_refl); trivial. }
      { simpl Datatypes.length.
        intro H.
        apply lt_S_n in H.
        specialize (IHxs _ H).
        simpl nth.simpl.

        SearchAbout (S _ < S _).
    match goal with
    destruct (first_index_error (string_beq nt) (Valid_nonterminals G)) eqn:H';
      t.
  Qed.*)

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
             | [ |- appcontext[if ?E then _ else _] ] => destruct E
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
             | [ H : appcontext[match ?E with left _ => _ | right _ => _ end] |- _ ] => destruct E
             | [ |- appcontext[match ?E with left _ => _ | right _ => _ end] ] => destruct E
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

  Global Instance rdp_list_predata : parser_computational_predataT
    := { nonterminals_listT := rdp_list_nonterminals_listT;
         initial_nonterminals_data := rdp_list_initial_nonterminals_data;
         of_nonterminal := rdp_list_of_nonterminal;
         to_nonterminal := rdp_list_to_nonterminal;
         is_valid_nonterminal := rdp_list_is_valid_nonterminal;
         remove_nonterminal := rdp_list_remove_nonterminal;
         nonterminals_length := @List.length _
         (*nonterminals_listT_R := rdp_list_nonterminals_listT_R;*)
         (*remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;*)
         (*ntl_wf := rdp_list_ntl_wf*) }.

  Global Instance rdp_list_rdata' : @parser_removal_dataT' _ G rdp_list_predata
    := { remove_nonterminal_dec := rdp_list_remove_nonterminal_dec;
         remove_nonterminal_noninc := rdp_list_remove_nonterminal_noninc;
         to_of_nonterminal := rdp_list_to_of_nonterminal;
         initial_nonterminals_correct := rdp_list_initial_nonterminals_correct;
         initial_nonterminals_correct' := rdp_list_initial_nonterminals_correct';
         remove_nonterminal_1 := rdp_list_remove_nonterminal_1;
         remove_nonterminal_2 := rdp_list_remove_nonterminal_2 }.
End recursive_descent_parser_list.
