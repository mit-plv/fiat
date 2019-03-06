(** * Every parse tree has a corresponding minimal parse tree *)

Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G predata}.

  Fixpoint paren_balanced_pb_parse_of_productions
             {valid0 pats}
             (str : String) (p : parse_of G str pats)
             (Hforall : Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
             (Hp : pb'_productions G valid0 pats)
             {struct Hp}
  : paren_balanced' str 0 = true
  with paren_balanced_pb_parse_of_production
         {valid0 pat level}
         (str : String) (p : parse_of_production G str pat)
         (Hforall : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 (of_nonterminal nt')) p)
         (Hp : pb'_production G valid0 level pat)
         {struct Hp}
       : paren_balanced' str level = true.
  Proof.
    { destruct Hp as [|??? Hp0 Hp1].
      { inversion p. }
      { specialize (fun str p H => paren_balanced_pb_parse_of_production _ _ _ str p H Hp0).
        specialize (fun str p H => paren_balanced_pb_parse_of_productions _ _ str p H Hp1).
        dependent destruction p; eauto with nocore. } }
    { destruct Hp as [|????? Hp0 Hp1|??????? Hp].
      { inversion p.
        rewrite paren_balanced'_nil by assumption.
        reflexivity. }
      { specialize (fun str p H => paren_balanced_pb_parse_of_production _ _ _ str p H Hp1).
        specialize (fun str p H => paren_balanced_pb_parse_of_productions _ _ str p H Hp0).
        dependent destruction p.
        let p1 := match goal with p1 : parse_of_production _ _ _ |- _ => constr:(p1) end in
        specialize (paren_balanced_pb_parse_of_production _ p1 (snd Hforall)).
        let p0 := match goal with p0 : parse_of_item _ _ _ |- _ => constr:(p0) end in
        let p := fresh in
        rename p0 into p;
          dependent destruction p.
        let p0 := match goal with p0 : parse_of _ _ _ |- _ => constr:(p0) end in
        specialize (paren_balanced_pb_parse_of_productions _ p0 (snd (fst Hforall))).
        eapply paren_balanced'_split_0; eassumption. }
      { specialize (fun str p H => paren_balanced_pb_parse_of_production _ _ _ str p H Hp).
        clear paren_balanced_pb_parse_of_productions.
        dependent destruction p.
        let p1 := match goal with p1 : parse_of_production _ _ _ |- _ => constr:(p1) end in
        specialize (paren_balanced_pb_parse_of_production _ p1 (snd Hforall)).
        let p0 := match goal with p0 : parse_of_item _ _ _ |- _ => constr:(p0) end in
        let p := fresh in
        rename p0 into p;
          dependent destruction p.
        match goal with
          | [ H : is_true (take _ _ ~= [ _ ]) |- _ ]
            => generalize (length_singleton _ _ H);
              pose proof (take_n_1_singleton _ _ _ H)
        end.
        rewrite paren_balanced'_recr.
        erewrite (proj1 (get_0 _ _)) by eassumption.
        rewrite take_length.
        unfold paren_balanced'_step, pb_check_level, pb_new_level in *.
        split_iff.
        apply Min.min_case_strong;
          repeat match goal with
                   | _ => progress subst
                   | _ => progress intros
                   | [ H : is_true (P ?ch), H' : forall ch', is_true (P ch') -> _ |- _ ]
                     => specialize (H' _ H)
                   | [ |- context[if ?e then _ else _] ] => destruct e eqn:?
                   | [ H : is_true ?x |- context[?x] ] => rewrite H
                   | _ => progress simpl in *
                   | _ => solve [ eauto with nocore ]
                   | [ n : nat, str : _ |- _ ]
                     => let H' := fresh in
                        assert (H' : drop 1 str =s drop n str)
                          by (apply bool_eq_empty; rewrite drop_length; omega);
                          rewrite H';
                          solve [ eauto with nocore ]
                 end. } }
  Defined.
End cfg.
