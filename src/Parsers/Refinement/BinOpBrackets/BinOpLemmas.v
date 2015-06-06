Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Common.

(*
Require Import Coq.Lists.List Coq.Setoids.Setoid Coq.Classes.Morphisms.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.SetoidInstances.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Common.
Require Import Fiat.Common.SetoidInstances.


Require Import Fiat.

Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammarEquality.
Require Import Coq.Program.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Wf.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerFull.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.ContextFreeGrammarValid.
Require Import Fiat.Parsers.ContextFreeGrammarValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammarValidReflective.
Require Fiat.Parsers.Reachable.All.MinimalReachable.
Require Fiat.Parsers.Reachable.All.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.All.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.ReachableParse.
Require Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Fiat.Parsers.Reachable.MaybeEmpty.OfParse.
*)
Set Implicit Arguments.

Local Notation eta x := (fst x, snd x) (only parsing).

Section paren_balanced.
  Context {Char} {HSL : StringLike Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}.

  Definition paren_balanced_T := nat -> nat * bool.

  Local Instance paren_balanced_fold_data : fold_grammar_data Char paren_balanced_T
    := { on_terminal ch level := (pb_new_level ch level, pb_check_level ch level);
         on_redundant_nonterminal nt level := (level, true);
         on_nil_production level := (level, Compare_dec.zerop level : bool);
         combine_production f1 f2 level := let '(level1, b1) := eta (f1 level) in
                                           let '(level2, b2) := eta (f2 level1) in
                                           (level2, (b1 && b2)%bool);
         on_nil_productions level := (0, true);
         combine_productions f1 f2 level := let '(level1, b1) := eta (f1 0) in
                                            let '(level2, b2) := eta (f2 0) in
                                            (0, (b1 && b2)%bool);
         on_nonterminal nt value := value }.

  Definition is_paren_balanced_of : grammar Char -> String.string -> paren_balanced_T
    := @fold_nt _ _ paren_balanced_fold_data.
  Definition is_paren_balanced_of_productions : grammar Char -> productions Char -> paren_balanced_T
    := @fold_productions _ _ paren_balanced_fold_data.
  Definition is_paren_balanced_of_production : grammar Char -> production Char -> paren_balanced_T
    := @fold_production _ _ paren_balanced_fold_data.

  Definition is_paren_balanced (G : grammar Char) (nt : String.string) : bool
    := snd (is_paren_balanced_of G nt 0).
End paren_balanced.

Section paren_balanced_hiding.
  Context {Char} {HSL : StringLike Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          (G : grammar Char).

  Definition paren_balanced_hiding_T := nat -> nat * bool.

  Local Instance paren_balanced_hiding_fold_data : fold_grammar_data Char paren_balanced_hiding_T
    := { on_terminal ch level
         := (pbh_new_level ch level, pbh_check_level ch level);
         on_redundant_nonterminal nt level
         := (level, true);
         on_nil_production level
         := (level, Compare_dec.zerop level : bool);
         combine_production f1 f2 level
         := let '(level1, b1) := eta (f1 level) in
            let '(level2, b2) := eta (f2 level1) in
            (level2, (b1 && b2)%bool);
         on_nil_productions level := (0, true);
         combine_productions f1 f2 level := let '(level1, b1) := eta (f1 0) in
                                            let '(level2, b2) := eta (f2 0) in
                                            (0, (b1 && b2)%bool);
         on_nonterminal nt f level
         := if Compare_dec.gt_dec level 0
            then (level, is_paren_balanced G nt)
            else f level }.

  Definition is_paren_balanced_hiding_of : grammar Char -> String.string -> paren_balanced_hiding_T
    := @fold_nt _ _ paren_balanced_hiding_fold_data.
  Definition is_paren_balanced_hiding_of_productions : grammar Char -> productions Char -> paren_balanced_hiding_T
    := @fold_productions _ _ paren_balanced_hiding_fold_data.
  Definition is_paren_balanced_hiding_of_production : grammar Char -> production Char -> paren_balanced_hiding_T
    := @fold_production _ _ paren_balanced_hiding_fold_data.

  Definition is_paren_balanced_hiding (G : grammar Char) (nt : String.string) : bool
    := snd (is_paren_balanced_hiding_of G nt 0).
End paren_balanced_hiding.

Section paren_balanced_correctness.
  Context {Char : Type} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          (G : grammar Char).
  Local Open Scope string_like_scope.

  Local Existing Instance paren_balanced_fold_data.

  Local Ltac dependent_destruction_head h :=
    idtac;
    match goal with
      | [ H : ?T |- _ ] => let x := head T in
                           constr_eq h x;
                             let H' := fresh in
                             rename H into H';
                               dependent destruction H'
    end.

  Local Ltac ddestruction H
    := let p := fresh in rename H into p; dependent destruction p.

  Local Ltac t' :=
    idtac;
    match goal with
      (*| _ => rewrite in_app_iff*)
      | _ => progress simpl in *
      | _ => intro
      | _ => progress destruct_head inhabited
      | [ H : is_true true -> _ |- _ ] => specialize (H eq_refl)
      | [ H : is_true false -> _ |- _ ] => clear H
      | [ H : context[is_true ?A] |- _ ] => not constr_eq A true; not constr_eq A false; destruct A eqn:?
      | _ => progress destruct_head iff
      | _ => progress subst
      | _ => reflexivity
      | _ => congruence
      | _ => tauto
      | [ H : context[fst ?x] |- _ ] => destruct x eqn:?; simpl in H
      | [ H : context[snd ?x] |- _ ] => destruct x eqn:?; simpl in H
      | [ |- context[fst ?x] ] => destruct x eqn:?; simpl
      | [ |- context[snd ?x] ] => destruct x eqn:?; simpl
      | [ level : nat, H : forall level : nat, _ |- _ ]
        => repeat match goal with
                    | [ level : nat |- _ ] => unique pose proof (H level)
                  end;
          clear H
      | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
      | _ => progress destruct_head or
      | [ |- _ <-> _ ] => split
      | [ |- inhabited _ ] => constructor
      | _ => assumption
      | _ => left; assumption
      | _ => right; assumption
      | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
      | [ H : ?A -> ?B |- ?B ] => apply H; clear H
      | [ H : context[bool_of_sumbool ?e] |- _ ] => destruct e
      | _ => solve [ constructor ]
      | [ H : minimal_pbh'_production _ _ _ _ nil |- _ ] => ddestruction H
      | [ H : minimal_pb'_production _ _ _ nil |- _ ] => ddestruction H
      | [ |- minimal_pbh'_production _ _ _ ?x (NonTerminal _ :: _)%list ]
        => is_var x; destruct x; [ apply PBHProductionConsNonTerminal0 | apply PBHProductionConsNonTerminalS ]
      | [ |- minimal_pb'_production _ _ _ (NonTerminal _ :: _)%list ]
        => apply PBProductionConsNonTerminal
      | [ H : ?x = (_, _) |- context[?x] ] => rewrite H
      (*| [ H : All.MinimalReachable.minimal_reachable_from_item _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_item _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_production _ _ nil |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_production _ _ (_::_) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_productions _ _ nil |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_productions _ _ (_::_) |- _ ] => ddestruction H*)
    end.

  Local Ltac t := repeat first [ t' | left; solve [ t ] | right; solve [ t ] ].

  Local Instance paren_balanced_ccdata : @fold_grammar_correctness_computational_data Char paren_balanced_T G
    := { Pnt valid0 nt f
         := forall level : nat, is_valid_nonterminal valid0 nt -> (snd (f level) <-> inhabited (minimal_pb'_productions G (remove_nonterminal valid0 nt) (Lookup G nt)));
         Ppat valid0 pat f
         := forall level : nat, snd (f level) <-> inhabited (minimal_pb'_production G valid0 (fst (f level)) pat);
         Ppats valid0 pats f
         := forall level : nat, snd (f level) <-> inhabited (minimal_pb'_productions G valid0 pats) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.

  Local Instance paren_balanced_cdata : @fold_grammar_correctness_data Char _ paren_balanced_fold_data G
    := { fgccd := paren_balanced_ccdata }.
  Proof.
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { simpl.
      intros.
      specialize (H level).
      specialize (H0 (fst (p level))).
      t.
      split; try solve [ t ].
      t.
      unfold minimal_pb'_production in *.
      exact X.
t. simpl.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t'.
      t.
      subst.
      clear Heqp2
      t'.
      unfold
      unfold
simpl.
t.

      constructor 4.
 }
    { abstract t. }
    { abstract t. }
    { abstract t. }
  Defined.

  Lemma is_paren_balanced_of_correct (G : grammar Char)
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (p : parse_of_item G str (NonTerminal nt))
        (Hp : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal initial_nonterminals_data nt') p)
  : forall_chars__char_in str (is_paren_balanced_of G nt).
  Proof.
    unfold is_paren_balanced_of.
    generalize (All.ReachableParse.forall_chars_reachable_from_parse_of_item _ Hp).
    setoid_rewrite All.MinimalReachableOfReachable.minimal_reachable_from_item__iff__reachable_from_item.
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    apply (fold_nt_correct (G := G) nt ch).
  Qed.
End paren_balanced_correctness.
End helpers.
