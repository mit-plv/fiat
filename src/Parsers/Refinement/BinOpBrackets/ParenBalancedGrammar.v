Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.

Local Open Scope bool_scope.
Local Open Scope string_like_scope.

Set Implicit Arguments.

Local Notation eta x := (fst x, snd x) (only parsing).
Local Notation eta2 x := (fst x, (fst (snd x), snd (snd x))) (only parsing).

Local Opaque rdp_list_predata.

Section specific.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.
  Context (G : grammar Char).
  Let predata := (@rdp_list_predata _ G).
  Local Existing Instance predata.

  Section assume_lists.
    Context (pb_nts pbh_nts : nonterminals_listT).

    Definition paren_balanced''_production_step
               (hiding : bool)
      := fun (it : item Char) (rest_balanced : nat -> bool) level
         => let predata := @rdp_list_predata _ G in
            match it with
              | Terminal ch
                => (pb_check_level hiding ch level)
                     && rest_balanced (pb_new_level ch level)
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
            (Lookup G (to_nonterminal nt))).

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
              unfold paren_balanced_hiding'_step, paren_balanced'_step, pb_check_level, pb_new_level in *.
              repeat match goal with
                       | _ => assumption
                       | [ |- context[bool_of_sumbool ?e] ] => destruct e; simpl
                       | [ |- appcontext[if ?e then _ else _] ]
                         => destruct e eqn:?
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
                  rewrite to_of_nonterminal in H_pbh by assumption.
                  specialize (paren_balanced_productions_correct _ _ H_pbh).
                  simpl in *.
                  assumption. }
                { specialize (H_pb _ H_p0); clear H_p0.
                  unfold paren_balanced''_nt in *.
                  (*apply Bool.andb_true_iff in H_pb;
                  destruct H_pb as [H_pb0 H_pb1]; clear H_pb.*)
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
          try eassumption; instantiate; rewrite ?to_of_nonterminal; eassumption.
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
  Context {Char} {HSL : StringLike Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          (G : grammar Char)
          (hiding : bool).
  Let predata := (@rdp_list_predata _ G).
  Local Existing Instance predata.

  Definition paren_balanced_nonterminals_T
    := nat -> nat * (list nonterminal_carrierT * list nonterminal_carrierT).

  Local Instance paren_balanced_nonterminals_fold_data : fold_grammar_data Char paren_balanced_nonterminals_T
    := { on_terminal ch level
         := (pb_new_level ch level,
             (nil, nil));
         on_redundant_nonterminal nt level
         := (0, (nil, nil));
         on_nil_production level
         := (level,
             (nil, nil));
         combine_production f1 f2 level
         := let '(level1, (pb_ls1, pbh_ls1)) := eta2 (f1 level) in
            let '(level2, (pb_ls2, pbh_ls2)) := eta2 (f2 level1) in
            (level2, (pb_ls1 ++ pb_ls2, pbh_ls1 ++ pbh_ls2));
         on_nil_productions level := (0, (nil, nil));
         combine_productions f1 f2 level
         := let '(level1, (pb_ls1, pbh_ls1)) := eta2 (f1 0) in
            let '(level2, (pb_ls2, pbh_ls2)) := eta2 (f2 0) in
            (0, (pb_ls1 ++ pb_ls2, pbh_ls1 ++ pbh_ls2));
         on_nonterminal nt f level
         := (level,
             let '(pb_ls, pbh_ls) := eta (snd (f level)) in
             ((of_nonterminal nt::pb_ls)
                ++ (if Compare_dec.gt_dec level 0
                    then pbh_ls
                    else nil),
              if Compare_dec.gt_dec level 0
              then nil
              else of_nonterminal nt::pbh_ls)) }.

  Definition paren_balanced_nonterminals_of : String.string -> paren_balanced_nonterminals_T
    := @fold_nt _ _ paren_balanced_nonterminals_fold_data G.
  Definition paren_balanced_nonterminals_of_productions : productions Char -> paren_balanced_nonterminals_T
    := @fold_productions _ _ paren_balanced_nonterminals_fold_data G.
  Definition paren_balanced_nonterminals_of_production : production Char -> paren_balanced_nonterminals_T
    := @fold_production _ _ paren_balanced_nonterminals_fold_data G.

  Definition paren_balanced_nonterminals nt : list nonterminal_carrierT * list nonterminal_carrierT
    := snd (paren_balanced_nonterminals_of nt 0).
End paren_balanced_nonterminals.

Local Transparent rdp_list_predata.

Section with_lists.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.
  Context (G : grammar Char).
  Let predata := (@rdp_list_predata _ G).
  Local Existing Instance predata.

  Section pre.
    Context (hiding : bool)
            (nt : String.string).

    Let pb_nts : @nonterminals_listT (@rdp_list_predata _ G)
      := fst (paren_balanced_nonterminals G nt).
    Let pbh_nts : @nonterminals_listT (@rdp_list_predata _ G)
      := snd (paren_balanced_nonterminals G nt).

    Context (H_pb : fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts false) pb_nts))
            (H_pbh : fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts true) pbh_nts)).

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

    Let pb_nts : @nonterminals_listT (@rdp_list_predata _ G)
      := fst (paren_balanced_nonterminals G nt).
    Let pbh_nts : @nonterminals_listT (@rdp_list_predata _ G)
      := snd (paren_balanced_nonterminals G nt).

    Definition paren_balanced_hiding_correctness_type
      := (fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts false) pb_nts))
           && (fold_right andb true (map (paren_balanced''_nt pb_nts pbh_nts true) pbh_nts))
           && (paren_balanced''_nt pb_nts pbh_nts true (of_nonterminal nt)).

    Global Arguments paren_balanced_hiding_correctness_type / .

    Lemma paren_balanced_hiding_nt_correct
          (Hvalid : paren_balanced_hiding_correctness_type)
    : forall str', parse_of_item G str' (NonTerminal nt)
                   -> paren_balanced_hiding str'.
    Proof.
      simpl in Hvalid.
      do 2 setoid_rewrite Bool.andb_true_iff in Hvalid.
      destruct Hvalid as [[? ?] ?].
      apply (paren_balanced_nt_correct true);
      assumption.
    Qed.
  End rule.
End with_lists.
