Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.Reachable.ParenBalanced.MinimalOfCore.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.MinimalOfCore.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.Refinement.BinOpBrackets.ParenBalanced.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Parsers.Splitters.RDPList.
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
         on_redundant_nonterminal nt level := (0, true);
         on_nil_production level := (level, Compare_dec.zerop level : bool);
         combine_production f1 f2 level
         := let '(level1, b1) := eta (f1 level) in
            let '(level2, b2) := eta (f2 level1) in
            (level2, (b1 && b2)%bool);
         on_nil_productions level := (0, true);
         combine_productions f1 f2 level
         := let '(level1, b1) := eta (f1 0) in
            let '(level2, b2) := eta (f2 0) in
            (0, (b1 && b2)%bool);
         on_nonterminal nt f level := (level, snd (f level)) }.

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
         := (0, true);
         on_nil_production level
         := (level, Compare_dec.zerop level : bool);
         combine_production f1 f2 level
         := let '(level1, b1) := eta (f1 level) in
            let '(level2, b2) := eta (f2 level1) in
            (level2, (b1 && b2)%bool);
         on_nil_productions level := (0, true);
         combine_productions f1 f2 level
         := let '(level1, b1) := eta (f1 0) in
            let '(level2, b2) := eta (f2 0) in
            (0, (b1 && b2)%bool);
         on_nonterminal nt f level
         := (level,
             if Compare_dec.gt_dec level 0
             then is_paren_balanced G nt
             else snd (f level)) }.

  Definition is_paren_balanced_hiding_of : String.string -> paren_balanced_hiding_T
    := @fold_nt _ _ paren_balanced_hiding_fold_data G.
  Definition is_paren_balanced_hiding_of_productions : productions Char -> paren_balanced_hiding_T
    := @fold_productions _ _ paren_balanced_hiding_fold_data G.
  Definition is_paren_balanced_hiding_of_production : production Char -> paren_balanced_hiding_T
    := @fold_production _ _ paren_balanced_hiding_fold_data G.

  Definition is_paren_balanced_hiding (nt : String.string) : bool
    := snd (is_paren_balanced_hiding_of nt 0).
End paren_balanced_hiding.

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
    | _ => progress split_and
    | [ H : is_true true -> _ |- _ ] => specialize (H eq_refl)
    | [ H : is_true false -> _ |- _ ] => clear H
    | [ H : context[is_true ?A] |- _ ] => not constr_eq A true; not constr_eq A false; destruct A eqn:?
    | _ => progress destruct_head iff
    | _ => progress subst
    | _ => reflexivity
    | _ => congruence
    | _ => tauto
    | _ => progress specialize_by assumption
    | _ => progress specialize_by ltac:(constructor; assumption)
    | [ H : context[fst ?x] |- _ ] => destruct x eqn:?; simpl in H
    | [ H : context[snd ?x] |- _ ] => destruct x eqn:?; simpl in H
    | [ |- context[fst ?x] ] => destruct x eqn:?; simpl
    | [ |- context[snd ?x] ] => destruct x eqn:?; simpl
    | [ f : paren_balanced_T, H : forall level : nat, _  |- _ ]
      => match goal with
           | [ |- context[f ?level] ] => specialize (H level)
           | [ H' : context[f ?level] |- _ ] => specialize (H level)
         end
    | [ f : paren_balanced_hiding_T, H : forall level : nat, _  |- _ ]
      => match goal with
           | [ |- context[f ?level] ] => specialize (H level)
           | [ H' : context[f ?level] |- _ ] => specialize (H level)
         end
    | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
    | _ => progress destruct_head or
    | [ |- _ <-> _ ] => split
    | [ |- inhabited _ ] => constructor
    | _ => assumption
    | _ => left; assumption
    | _ => right; assumption
    | [ H : (_ && _)%bool = true |- _ ] => apply Bool.andb_true_iff in H
    | [ H : (_, _) = (_, _) |- _ ] => inversion H; clear H
    | [ H : ?A -> ?B |- ?B ] => apply H; clear H
    | [ H : context[bool_of_sumbool ?e] |- _ ] => destruct e
    | _ => solve [ constructor ]
    | [ H : minimal_pbh'_production _ _ _ _ nil |- _ ] => ddestruction H
    | [ H : minimal_pbh'_production _ _ _ _ (_ :: _)%list |- _ ] => ddestruction H
    | [ H : minimal_pbh'_productions _ _ _ (_ :: _)%list |- _ ] => ddestruction H
    | [ H : minimal_pb'_production _ _ _ nil |- _ ] => ddestruction H
    | [ H : minimal_pb'_production _ _ _ (_ :: _)%list |- _ ] => ddestruction H
    | [ H : minimal_pb'_productions _ _ (_ :: _)%list |- _ ] => ddestruction H
    | [ |- minimal_pbh'_production _ _ _ ?x (NonTerminal _ :: _)%list ]
      => is_var x; destruct x; [ apply PBHProductionConsNonTerminal0 | apply PBHProductionConsNonTerminalS ]
    | [ |- minimal_pbh'_production _ _ _ (S _) (NonTerminal _ :: _)%list ]
      => apply PBHProductionConsNonTerminalS
    | [ |- minimal_pbh'_production _ _ _ 0 (NonTerminal _ :: _)%list ]
      => apply PBHProductionConsNonTerminal0
    | [ |- minimal_pb'_production _ _ _ (NonTerminal _ :: _)%list ]
      => apply PBProductionConsNonTerminal
    | [ |- minimal_pbh'_production _ _ _ _ (Terminal _ :: _)%list ]
      => apply PBHProductionConsTerminal
    | [ |- minimal_pb'_production _ _ _ (Terminal _ :: _)%list ]
      => apply PBProductionConsTerminal
    | [ |- minimal_pbh'_productions _ _ _ (_ :: _)%list ]
      => apply PBHCons
    | [ |- minimal_pb'_productions _ _ (_ :: _)%list ]
      => apply PBCons
    | [ H : ?x = (_, _) |- context[?x] ] => rewrite H
    | [ H : ?x = true |- context[?x] ] => rewrite H
    | [ H : ?x = false |- context[?x] ] => rewrite H
    | [ H : ?x = true, H' : context[?x] |- _ ] => rewrite H in H'
    | [ H : ?x = false, H' : context[?x] |- _ ] => rewrite H in H'
    | [ |- _ /\ _ ] => split
    | [ H : appcontext[if ?e then _ else _] |- _ ] => destruct e eqn:?
  (*| [ H : All.MinimalReachable.minimal_reachable_from_item _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_item _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_production _ _ nil |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_production _ _ (_::_) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_productions _ _ nil |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_productions _ _ (_::_) |- _ ] => ddestruction H*)
  end.

Local Ltac t := repeat first [ t' | left; solve [ t ] | right; solve [ t ] ].

Section paren_balanced_correctness.
  Context {Char : Type} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          (G : grammar Char).
  Local Open Scope string_like_scope.

  Local Existing Instance paren_balanced_fold_data.

  Local Instance paren_balanced_ccdata : @fold_grammar_correctness_computational_data Char paren_balanced_T G
    := { Pnt valid0 nt f
         := forall level : nat,
              (snd (f level) -> fst (f level) = 0)
              /\ (is_valid_nonterminal valid0 nt
                  -> (snd (f level)
                      <-> (inhabited (minimal_pb'_productions G (remove_nonterminal valid0 nt) (Lookup G nt)))));
         Ppat valid0 pat f
         := forall level : nat,
              (snd (f level) -> fst (f level) = 0)
              /\ (snd (f level) <-> inhabited (minimal_pb'_production G valid0 level pat));
         Ppats valid0 pats f
         := forall level : nat, (fst (f level) = 0) /\ (snd (f level) <-> inhabited (minimal_pb'_productions G valid0 pats)) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.

  Local Instance paren_balanced_cdata : @fold_grammar_correctness_data Char _ paren_balanced_fold_data G
    := { fgccd := paren_balanced_ccdata }.
  Proof.
    { simpl. t. }
    { abstract t. }
    { simpl. t. }
    { simpl.
      intros.
      specialize (H0 level).
      specialize (H1 level).
      split; [ solve [ t ] | ].
      split; [ | solve [ t ] ].
      setoid_rewrite Bool.andb_true_iff.
      intros.
      split_and.
      split_iff.
      specialize_by assumption.
      destruct_head inhabited.
      admit. }
    { simpl. t. }
    { simpl. t. }
    { simpl. t. }
  Defined.

  Local Opaque rdp_list_predata.

  Lemma is_paren_balanced_correct
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (Hbalanced : is_paren_balanced G nt)
        (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
  : inhabited (pb'_production G initial_nonterminals_data 0 (NonTerminal nt :: nil)%list).
  Proof.
    unfold is_paren_balanced in *.
    unfold is_paren_balanced_of in *.
    apply (fold_nt_correct (G := G) nt 0) in Hbalanced; [ | assumption.. ].
    destruct_head inhabited.
    apply minimal_pb'_production__iff__pb'_production.
    constructor.
    constructor; [ assumption | assumption | constructor ].
  Qed.
End paren_balanced_correctness.

Section paren_balanced_hiding_correctness.
  Context {Char : Type} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Context {pdata : paren_balanced_hiding_dataT Char}
          (G : grammar Char).
  Local Open Scope string_like_scope.

  Local Existing Instance paren_balanced_hiding_fold_data.

  Local Instance paren_balanced_hiding_ccdata : @fold_grammar_correctness_computational_data Char paren_balanced_hiding_T G
    := { Pnt valid0 nt f
         := forall level : nat,
              (snd (f level) -> fst (f level) = 0)
              /\ (is_valid_nonterminal valid0 nt
                  -> (snd (f level)
                      <-> (inhabited (minimal_pbh'_productions G initial_nonterminals_data (remove_nonterminal valid0 nt) (Lookup G nt)))));
         Ppat valid0 pat f
         := forall level : nat,
              (snd (f level) -> fst (f level) = 0)
              /\ (snd (f level) <-> inhabited (minimal_pbh'_production G initial_nonterminals_data valid0 level pat));
         Ppats valid0 pats f
         := forall level : nat, (fst (f level) = 0) /\ (snd (f level) <-> inhabited (minimal_pbh'_productions G initial_nonterminals_data valid0 pats)) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.
  Local Opaque rdp_list_predata.

  Local Instance paren_balanced_hiding_cdata : @fold_grammar_correctness_data Char _ (paren_balanced_hiding_fold_data G) G
    := { fgccd := paren_balanced_hiding_ccdata }.
  Proof.
    { simpl. t. }
    { abstract t. }
    { simpl. t. }
    { simpl.
      intros.
      specialize (H0 level).
      specialize (H1 level).
      split; [ solve [ t ] | ].
      destruct level; simpl.
      { split; [ | try solve [ t ] ].
        setoid_rewrite Bool.andb_true_iff.
        intros.
        split_and.
        split_iff.
        specialize_by assumption.
        destruct_head inhabited.
        destruct (is_valid_nonterminal valid0 nt) eqn:?;
                 [ solve [ t ] | ].
        admit. }
      { setoid_rewrite Bool.andb_true_iff.
        split; [ | try solve [ t ] ].
        { intros.
          split_and.
          split_iff.
          specialize_by trivial.
          destruct (is_valid_nonterminal valid0 nt) eqn:? .
          { unfold is_paren_balanced, is_paren_balanced_of in *;
            match goal with
              | [ H : snd (fold_nt _ _ _) = true |- _ ]
                =>
                apply (@fold_nt_correct _ _ paren_balanced_fold_data G (paren_balanced_cdata G) nt 0) in H; [ | solve [ eauto with nocore ] ]
            end.
            specialize_by ltac:(exact eq_refl).
            specialize_by assumption.
            destruct_head inhabited.
            constructor.
            constructor; trivial; [].
            eapply expand_generic_pb'_production; [  | reflexivity | reflexivity | constructor; [ | eassumption | constructor ]; solve [ eauto with nocore ] ].
            unfold respectful.
            assert (predata := @rdp_list_predata _ G).
            clear -predata.
            intros; subst.
            rewrite sub_nonterminals_listT_remove; assumption. }
          { admit. } }
        { t;
          unfold is_paren_balanced, is_paren_balanced_of in *;
          match goal with
            | [ H : pb'_production _ _ _ [_]%list |- _ ]
              => apply inhabits in H; apply minimal_pb'_production__iff__pb'_production in H; destruct H as [H]; inversion H; clear H; subst
          end;
          destruct (is_valid_nonterminal valid0 nt) eqn:? ;
          solve [
              match goal with
                | [ |- snd (fold_nt _ _ _) = true ]
                  =>
                  apply (@fold_nt_correct _ _ paren_balanced_fold_data G (paren_balanced_cdata G) nt 0); [ solve [ eauto with nocore ] | ]
              end;
              constructor; assumption
            | congruence ]. } } }
    { simpl. t. }
    { simpl. t. }
    { simpl. t. }
  Defined.

  Lemma is_paren_balanced_hiding_correct
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (Hbalanced : is_paren_balanced_hiding G nt)
        (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
  : inhabited (pbh'_production G initial_nonterminals_data initial_nonterminals_data 0 (NonTerminal nt :: nil)%list).
  Proof.
    unfold is_paren_balanced_hiding in *.
    unfold is_paren_balanced_hiding_of in *.
    apply (@fold_nt_correct _ _ _ _ paren_balanced_hiding_cdata nt) in Hbalanced; [ | assumption.. ].
    destruct_head inhabited.
    apply minimal_pbh'_production__iff__pbh'_production.
    constructor.
    constructor; [ assumption | assumption | constructor ].
  Qed.
End paren_balanced_hiding_correctness.
