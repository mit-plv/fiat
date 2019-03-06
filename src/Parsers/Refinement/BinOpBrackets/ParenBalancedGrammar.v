Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.FixedPoints.

Local Open Scope bool_scope.
Local Open Scope string_like_scope.

Set Implicit Arguments.

Local Notation eta x := (fst x, snd x) (only parsing).
Local Notation eta2 x := (fst x, (fst (snd x), snd (snd x))) (only parsing).

Local Opaque rdp_list_predata.

Section specific.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {CharE : Enumerable Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.
  Context (G : pregrammar' Char).
  Let predata := (@rdp_list_predata _ G).
  Local Existing Instance predata.

  Section assume_lists.
    Context (pb_nts pbh_nts : nonterminals_listT).

    Definition paren_balanced''_production_step
               (hiding : bool)
      := fun (it : item Char) (rest_balanced : nat -> bool) level
         => let predata := @rdp_list_predata _ G in
            match it with
              | Terminal P
                => ((pb_check_level_fun hiding P level)
                      && match pb_new_level_fun P level with
                           | new_level::nil => rest_balanced new_level
                           | _ => false
                         end)%bool
              | NonTerminal nt
                => (*(is_valid_nonterminal initial_nonterminals_data nt)
                   &&*)
                (if (hiding && Compare_dec.zerop level)
                 then is_valid_nonterminal pbh_nts (of_nonterminal nt)
                 else is_valid_nonterminal pb_nts (of_nonterminal nt))
                  && rest_balanced level
            end.

    Definition paren_balanced''_production
               (hiding : bool)
               (level : nat)
               (pat : production Char)
    : bool
      := fold_right
           (paren_balanced''_production_step hiding)
           Compare_dec.zerop
           pat
           level.

    Definition paren_balanced''_productions
               (hiding : bool)
               (level : nat)
               (pats : productions Char)
    : bool
      := fold_right
           andb
           true
           (map (paren_balanced''_production hiding level) pats).

    Definition paren_balanced''_nt
               (hiding : bool)
               (nt : nonterminal_carrierT)
    : bool
      := let predata := @rdp_list_predata _ G in
         (paren_balanced''_productions
            hiding
            0
            (Lookup_idx G nt)).

    Section correct.
      Context (H_pb : forall nt, is_valid_nonterminal pb_nts nt
                                 -> paren_balanced''_nt false nt)
              (H_pbh : forall nt, is_valid_nonterminal pbh_nts nt
                                  -> paren_balanced''_nt true nt).

      Fixpoint paren_balanced_productions_correct
               (hiding : bool)
               (level : nat)
               (pats : productions Char)
               (H_p : paren_balanced''_productions hiding level pats)
               (str : String)
               (p : parse_of G str pats)
      : if hiding
        then paren_balanced_hiding' str level
        else paren_balanced' str level
      with paren_balanced_production_correct
             (hiding : bool)
             (level : nat)
             (pat : production Char)
             (H_p : paren_balanced''_production hiding level pat)
             (str : String)
             (p : parse_of_production G str pat)
           : if hiding
             then paren_balanced_hiding' str level
             else paren_balanced' str level.
      Proof.
        { destruct p as [?? p | ?? p ];
          [ apply (fun hiding level H_p => paren_balanced_production_correct hiding level _ H_p _ p)
          | apply (fun hiding level H_p => paren_balanced_productions_correct hiding level _ H_p _ p) ];
          clear paren_balanced_production_correct paren_balanced_productions_correct;
          unfold paren_balanced''_productions in *;
          simpl in *;
          apply Bool.andb_true_iff in H_p;
          destruct H_p as [H_p0 H_p1];
          assumption. }
        { destruct p as [| ??? p0 p1 ].
          { clear paren_balanced_productions_correct paren_balanced_production_correct.
            unfold paren_balanced''_production in *.
            simpl in *.
            edestruct Compare_dec.zerop; subst; simpl in *; try congruence; [].
            destruct hiding.
            { rewrite paren_balanced_hiding'_nil by assumption; reflexivity. }
            { rewrite paren_balanced'_nil by assumption; reflexivity. } }
          { specialize (fun hiding level H_p => paren_balanced_production_correct hiding level _ H_p _ p1); clear p1.
            unfold paren_balanced''_production in *.
            simpl in *.
            destruct p0 as [| ? ? p0 ].
            { clear paren_balanced_productions_correct.
              unfold paren_balanced''_production_step at 1 in H_p.
              destruct (pb_new_level_fun P level) as [|? [|]] eqn:Heq;
                simpl in *;
                try rewrite Bool.andb_false_r in *; try congruence;
                [].
              apply Bool.andb_true_iff in H_p;
                destruct H_p as [H_p0 H_p1].
              specialize (paren_balanced_production_correct _ _ H_p1).
              clear H_p1.
              rewrite paren_balanced_hiding'_recr.
              rewrite paren_balanced'_recr.
              repeat match goal with
                       | [ H : is_true (_ ~= [ _ ]) |- _ ]
                         => pose proof (length_singleton _ _ H);
                           progress apply take_n_1_singleton in H
                       | [ H : context[length (StringLike.take _ _)] |- _ ]
                         => rewrite take_length in H
                     end.
              erewrite !(proj1 (get_0 _ _)) by eassumption.
              assert (H' : StringLike.drop n str =s StringLike.drop 1 str).
              { destruct n as [|[|n]]; simpl in *; try congruence; try reflexivity.
                destruct (length str) as [|[|]] eqn:?; try congruence.
                apply bool_eq_empty; rewrite ?drop_length; omega. }
              rewrite !H' in paren_balanced_production_correct; clear H'.
              repeat match goal with
                       | [ H : _ |- _ ] => setoid_rewrite pb_check_level_fun_correct in H
                       | [ H : _ |- _ ] => setoid_rewrite pb_new_level_fun_correct in H
                     end.
              unfold paren_balanced_hiding'_step, paren_balanced'_step, pb_check_level_fun, pb_new_level_fun, pb_check_level, pb_new_level in *.
              repeat match goal with
                       | _ => assumption
                       | _ => progress subst
                       | [ H : filter _ _ = _::nil |- _ ] => eapply filter_enumerate in H
                       | _ => progress split_iff
                       | _ => specialize_by eassumption; progress subst
                       | [ H : context[fold_right andb true (map _ _)] |- _ ]
                         => rewrite fold_right_andb_map_in_iff in H
                       | [ H : context[In _ (filter _ _)] |- _ ]
                         => setoid_rewrite filter_In in H
                       | [ H : forall x, _ /\ _ -> _ |- _ ] => specialize (fun x A B => H x (conj A B))
                       | [ H : forall x, In _ (enumerate _) -> _ |- _ ]
                           => specialize (fun x => H x (enumerate_correct _))
                       | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : ?x = false, H' : context[?x] |- _ ] => rewrite H in H'
                       | [ H : ?x = ?y::nil |- _ ]
                         => assert (forall n, In n x <-> n = y)
                           by (intro; rewrite H; simpl; intuition);
                           clear H
                       | [ H : forall x, _ = x -> _ |- _ ] => specialize (H _ eq_refl)
                       | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
                       | [ H : context[In _ (uniquize _ _)] |- _ ]
                         => setoid_rewrite <- (ListFacts.uniquize_In_refl_iff _ EqNat.beq_nat _ (lb eq_refl) bl) in H
                       | [ H : context[In _ (map _ _)] |- _ ]
                         => setoid_rewrite in_map_iff in H
                       | _ => progress destruct_head ex
                       | _ => progress destruct_head and
                       | [ H : forall x, ex _ -> _ |- _ ]
                         => specialize (fun x a b => H x (ex_intro _ a b))
                       | _ => progress cbv beta in *
                       | _ => progress split_and
                       | [ |- context[bool_of_sumbool ?e] ] => destruct e; simpl
                       | [ |- context[if ?e then _ else _] ]
                         => destruct e eqn:?
                       | [ H : forall ch, is_true (?P ch) -> _ |- _ ]
                         => repeat match goal with
                                     | [ H' : is_true (P ?ch') |- _ ]
                                       => unique pose proof (H _ H')
                                     | [ H' : P ?ch' = true |- _ ]
                                       => unique pose proof (H _ H')
                                   end;
                           clear H
                     end. }
            { specialize (fun hiding level H_p => paren_balanced_productions_correct hiding level _ H_p _ p0); clear p0.
              unfold paren_balanced''_production_step at 1 in H_p.
              apply Bool.andb_true_iff in H_p;
                destruct H_p as [H_p0 H_p1].
              specialize (paren_balanced_production_correct _ _ H_p1); clear H_p1.
              destruct hiding.
              { simpl in *.
                rewrite paren_balanced_hiding'_split_0; [ reflexivity | | eassumption ].
                destruct level as [|level]; simpl in *.
                { specialize (H_pbh _ H_p0); clear H_p0.
                  unfold paren_balanced''_nt in *.
                  (*apply Bool.andb_true_iff in H_pbh;
                  destruct H_pbh as [H_pbh0 H_pbh1]; clear H_pbh.*)
                  rewrite <- Carriers.list_to_productions_to_nonterminal in H_pbh.
                  change Carriers.default_to_nonterminal with to_nonterminal in H_pbh.
                  rewrite to_of_nonterminal in H_pbh by assumption.
                  specialize (paren_balanced_productions_correct _ _ H_pbh).
                  simpl in *.
                  assumption. }
                { specialize (H_pb _ H_p0); clear H_p0.
                  unfold paren_balanced''_nt in *.
                  (*apply Bool.andb_true_iff in H_pb;
                  destruct H_pb as [H_pb0 H_pb1]; clear H_pb.*)
                  rewrite <- Carriers.list_to_productions_to_nonterminal in H_pb.
                  change Carriers.default_to_nonterminal with to_nonterminal in H_pb.
                  rewrite to_of_nonterminal in H_pb by assumption.
                  specialize (paren_balanced_productions_correct _ _ H_pb).
                  simpl in *.
                  assumption. } }
              { simpl in *.
                rewrite paren_balanced'_split_0; [ reflexivity | | eassumption ].
                specialize (H_pb _ H_p0); clear H_p0.
                unfold paren_balanced''_nt in *.
                (*apply Bool.andb_true_iff in H_pb;
                destruct H_pb as [H_pb0 H_pb1]; clear H_pb.*)
                rewrite <- Carriers.list_to_productions_to_nonterminal in H_pb.
                change Carriers.default_to_nonterminal with to_nonterminal in H_pb.
                rewrite to_of_nonterminal in H_pb by assumption.
                specialize (paren_balanced_productions_correct _ _ H_pb).
                simpl in *.
                assumption. } } } }
      Defined.

      Lemma paren_balanced_nt''_correct
            (hiding : bool)
            nt
            (H_p : paren_balanced''_nt hiding (of_nonterminal nt))
            (str : String)
            (p : parse_of_item G str (NonTerminal nt))
      : if hiding
        then paren_balanced_hiding str
        else paren_balanced str.
      Proof.
        dependent destruction p.
        eapply paren_balanced_productions_correct;
          try eassumption; instantiate;
            rewrite <- Carriers.list_to_productions_to_nonterminal;
            change Carriers.default_to_nonterminal with to_nonterminal;
            rewrite ?to_of_nonterminal; eassumption.
      Qed.
    End correct.

    Section correct_reflective.
      Local Transparent rdp_list_predata.

      Context (H_pb : fold_right andb true (map (paren_balanced''_nt false) pb_nts))
              (H_pbh : fold_right andb true (map (paren_balanced''_nt true) pbh_nts)).

      Local Ltac t :=
        repeat match goal with
                 | _ => progress simpl in *
                 | _ => progress specialize_by assumption
                 | _ => progress intros
                 | _ => progress unfold rdp_list_is_valid_nonterminal in *
                 | _ => progress subst
                 | _ => congruence
                 | [ H : string_beq _ _ = true |- _ ] => apply string_bl in H
                 | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
                 | [ H : is_true (_ || _) |- _ ] => apply Bool.orb_true_iff in H
                 | [ H : is_true (_ && _) |- _ ] => apply Bool.andb_true_iff in H
                 | [ H : _ /\ _ |- _ ] => let H1 := fresh in
                                          let H2 := fresh in
                                          destruct H as [H1 H2]; try clear H
                 | [ H : _ \/ _ |- _ ] => destruct H
                 | _ => solve [ eauto with nocore ]
               end.

      Lemma paren_balanced_nt'_correct
            (hiding : bool)
            nt
            (H_p : paren_balanced''_nt hiding (of_nonterminal nt))
            (str : String)
            (p : parse_of_item G str (NonTerminal nt))
      : if hiding
        then paren_balanced_hiding str
        else paren_balanced str.
      Proof.
        eapply paren_balanced_nt''_correct; try eassumption.
        { clear -H_pb.
          induction pb_nts; t. }
        { clear -H_pbh.
          induction pbh_nts; t. }
      Qed.
    End correct_reflective.
  End assume_lists.
End specific.

Section paren_balanced_nonterminals.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.
  Context {HEC : Enumerable Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          (G : pregrammar' Char)
          (hiding : bool).
  Let predata := (@rdp_list_predata _ G).
  Local Existing Instance predata.

  Definition paren_balanced_nonterminals (nt : String.string) : list nonterminal_carrierT * list nonterminal_carrierT
    := greatest_fixpoint_of_lists
         (fun pb_nts pbh_nts => paren_balanced''_nt (G := G) pb_nts pbh_nts false)
         (fun pb_nts pbh_nts => paren_balanced''_nt (G := G) pb_nts pbh_nts true)
         initial_nonterminals_data
         initial_nonterminals_data.
End paren_balanced_nonterminals.

Local Transparent rdp_list_predata.

Section with_lists.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {HEC : Enumerable Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.
  Context (G : pregrammar' Char).
  Let predata := (@rdp_list_predata _ G).
  Local Existing Instance predata.

  Section pre.
    Context (hiding : bool)
            (nt : String.string).

    Let pb_nts : nonterminals_listT
      := fst (paren_balanced_nonterminals G nt).
    Let pbh_nts : nonterminals_listT
      := snd (paren_balanced_nonterminals G nt).

    Let H_pb : fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts false) pb_nts).
    Proof.
      rapply @greatest_fixpoint_of_lists_correct_1.
    Qed.
    Let H_pbh : fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts true) pbh_nts).
    Proof.
      rapply @greatest_fixpoint_of_lists_correct_2.
    Qed.

    Lemma paren_balanced_nt_correct
          (H_p : paren_balanced''_nt pb_nts pbh_nts hiding (of_nonterminal nt))
          (str : String)
          (p : parse_of_item G str (NonTerminal nt))
    : if hiding
      then paren_balanced_hiding str
      else paren_balanced str.
    Proof.
      eapply paren_balanced_nt'_correct; eassumption.
    Qed.
  End pre.

  Section rule.
    Context (nt : String.string).

    Let pb_nts : nonterminals_listT
      := fst (paren_balanced_nonterminals G nt).
    Let pbh_nts : nonterminals_listT
      := snd (paren_balanced_nonterminals G nt).

    Definition paren_balanced_hiding_correctness_type
      := (*(fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts false) pb_nts))
           && (fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts true) pbh_nts))
           && *)(paren_balanced''_nt pb_nts pbh_nts true (of_nonterminal nt)).

    Global Arguments paren_balanced_hiding_correctness_type / .

    (** Just check for paren-balanced-ness, not for that it hides the binary operation. *)
    Definition paren_balanced_correctness_type
      := (*(fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts false) pb_nts))
           && (fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts false) pbh_nts))
           &&*) (paren_balanced''_nt pb_nts pbh_nts false (of_nonterminal nt)).

    Global Arguments paren_balanced_hiding_correctness_type / .

    Lemma paren_balanced_hiding_nt_correct
          (Hvalid : paren_balanced_hiding_correctness_type)
    : forall str', parse_of_item G str' (NonTerminal nt)
                   -> paren_balanced_hiding str'.
    Proof.
      simpl in Hvalid.
      apply (paren_balanced_nt_correct true);
      assumption.
    Qed.
  End rule.
End with_lists.
