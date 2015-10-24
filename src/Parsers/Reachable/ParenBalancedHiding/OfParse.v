(** * Every parse tree has a corresponding minimal parse tree *)
Require Import Coq.Program.Basics.
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalanced.OfParse.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.MinimalOfCore.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          {predata : parser_computational_predataT}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Fixpoint paren_balanced_hiding_pbh_parse_of_productions
             {valid00 valid0 pats}
             (str : String) (p : parse_of G str pats)
             (Hforall0 : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid00 nt') p)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p)
             (Hp : pbh'_productions G valid00 valid0 pats)
             {struct Hp}
  : paren_balanced_hiding' str 0 = true
  with paren_balanced_hiding_pbh_parse_of_production
         {valid00 valid0 pat level}
         (str : String) (p : parse_of_production G str pat)
         (Hforall0 : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid00 nt') p)
         (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p)
         (Hp : pbh'_production G valid00 valid0 level pat)
         {struct Hp}
       : paren_balanced_hiding' str level = true.
  Proof.
    { destruct Hp as [|??? Hp0 Hp1].
      { inversion p. }
      { specialize (fun str p H0 H => paren_balanced_hiding_pbh_parse_of_production _ _ _ _ str p H0 H Hp0).
        specialize (fun str p H0 H => paren_balanced_hiding_pbh_parse_of_productions _ _ _ str p H0 H Hp1).
        dependent destruction p; eauto with nocore. } }
    { destruct Hp as [|???? Hp0 Hp1|???? Hp0 Hp1|????? Hp].
      { inversion p.
        rewrite paren_balanced_hiding'_nil by assumption.
        reflexivity. }
      { specialize (fun str p H0 H => paren_balanced_hiding_pbh_parse_of_production _ _ _ _ str p H0 H Hp1).
        specialize (fun str p H0 H => paren_balanced_hiding_pbh_parse_of_productions _ _ _ str p H0 H Hp0).
        dependent destruction p.
        let p1 := match goal with p1 : parse_of_production _ _ _ |- _ => constr:p1 end in
        specialize (paren_balanced_hiding_pbh_parse_of_production _ p1 (snd Hforall0) (snd Hforall)).
        let p0 := match goal with p0 : parse_of_item _ _ _ |- _ => constr:p0 end in
        let p := fresh in
        rename p0 into p;
          dependent destruction p.
        let p0 := match goal with p0 : parse_of _ _ _ |- _ => constr:p0 end in
        specialize (paren_balanced_hiding_pbh_parse_of_productions _ p0 (snd (fst Hforall0)) (snd (fst Hforall))).
        eapply paren_balanced_hiding'_split_0; simpl; eassumption. }
      { specialize (fun str p H0 H => paren_balanced_hiding_pbh_parse_of_production _ _ _ _ str p H0 H Hp1).
        clear paren_balanced_hiding_pbh_parse_of_productions.
        pose proof (fun str p H => paren_balanced_pb_parse_of_production (str := str) p H Hp0) as paren_balanced_hiding_pbh_parse_of_productions.
        dependent destruction p.
        let p1 := match goal with p1 : parse_of_production _ _ _ |- _ => constr:p1 end in
        specialize (paren_balanced_hiding_pbh_parse_of_production _ p1 (snd Hforall0) (snd Hforall)).
        let p0 := match goal with p0 : parse_of_item _ _ _ |- _ => constr:p0 end in
        let p := fresh in
        rename p0 into p;
          dependent destruction p.
        specialize (fun H'' str p H (H' : is_valid_nonterminal _ _ * Forall_parse_of _ (parse_of_respectful (symmetry (take_take str n n)) p) * unit)
                    => paren_balanced_hiding_pbh_parse_of_productions
                         (take n str)
                         (ParseProductionCons
                            _ n
                            (ParseNonTerminal
                               _
                               H''
                               (parse_of_respectful (symmetry (take_take str n n)) p))
                            (ParseProductionNil _ _ H))
                         H').
        specialize_by assumption.
        specialize (fun x H p H1 H0
                    => paren_balanced_hiding_pbh_parse_of_productions
                         str p H (H0, expand_forall_parse_of (str' := take (min n n) str) (P := fun _ nt => is_valid_nonterminal valid00 nt) x (reflexivity _) _ _ H1, tt)).
        simpl in *.
        specialize_by trivial.
        specialize_by ltac:(rewrite drop_length, take_length; apply Min.min_case_strong; omega).
        rewrite Min.min_idempotent in paren_balanced_hiding_pbh_parse_of_productions.
        let p0 := match goal with p0 : parse_of _ _ _ |- _ => constr:p0 end in
        specialize (paren_balanced_hiding_pbh_parse_of_productions p0).
        rewrite parse_of_respectful_refl in paren_balanced_hiding_pbh_parse_of_productions.
        specialize (paren_balanced_hiding_pbh_parse_of_productions (snd (fst (Hforall0)))).
        specialize (paren_balanced_hiding_pbh_parse_of_productions (fst (fst (Hforall0)))).
        eapply paren_balanced_hiding'_split_0; simpl; eassumption. }
      { specialize (fun str p H0 H => paren_balanced_hiding_pbh_parse_of_production _ _ _ _ str p H0 H Hp).
        clear paren_balanced_hiding_pbh_parse_of_productions.
        dependent destruction p.
        let p1 := match goal with p1 : parse_of_production _ _ _ |- _ => constr:p1 end in
        specialize (paren_balanced_hiding_pbh_parse_of_production _ p1 (snd Hforall0) (snd Hforall)).
        let p0 := match goal with p0 : parse_of_item _ _ _ |- _ => constr:p0 end in
        let p := fresh in
        rename p0 into p;
          dependent destruction p.
        match goal with
          | [ H : is_true (take _ _ ~= [ _ ]) |- _ ]
            => generalize (length_singleton _ _ H);
              pose proof (take_n_1_singleton _ _ _ H)
        end.
        rewrite paren_balanced_hiding'_recr.
        erewrite (proj1 (get_0 _ _)) by eassumption.
        rewrite take_length.
        unfold paren_balanced_hiding'_step, paren_balanced'_step, pbh_check_level, pbh_new_level, pb_check_level, pb_new_level in *.
        apply Min.min_case_strong;
          repeat match goal with
                   | _ => progress subst
                   | _ => progress intros
                   | [ H : is_true (_ && _)%bool |- _ ] => apply Bool.andb_true_iff in H
                   | _ => progress split_and
                   | [ H : is_true ?x |- context[?x] ] => rewrite H
                   | _ => progress simpl in *
                   | _ => solve [ eauto with nocore ]
                   | [ n : nat, str : _ |- _ ]
                     => let H' := fresh in
                        assert (H' : drop 1 str =s drop n str)
                          by (apply bool_eq_empty; rewrite drop_length; omega);
                          rewrite H';
                          solve [ eauto with nocore ]
                   | [ H : context[if ?e then _ else _] |- _ ] => destruct e eqn:?
                   | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                   | [ H : context[bool_of_sumbool ?e] |- _ ] => destruct e; simpl in H
                   | [ |- context[bool_of_sumbool ?e] ] => destruct e; simpl
                 end. } }
  Defined.
End cfg.
