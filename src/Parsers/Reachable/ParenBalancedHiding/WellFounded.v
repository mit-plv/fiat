(** * Well-founded relation on [reachable] *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.BaseTypes.

Section rel.
  Context {Char} {HSLM : StringLikeMin Char} {predata : @parser_computational_predataT Char}
          {pdata : paren_balanced_hiding_dataT Char}
          {G : grammar Char}.

  Section size.
    Context {transform_valid : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT}.

    Fixpoint size_of_pbh'_productions {valid n pats} (p : generic_pbh'_productions G transform_valid valid n pats)
    : nat
      := match p with
           | PBHNil _ => 0
           | PBHCons _ _ _ p0 p1 => S (size_of_pbh'_production p0 + size_of_pbh'_productions p1)
         end
    with size_of_pbh'_production {valid0 valid n pat} (p : generic_pbh'_production G transform_valid valid0 valid n pat) : nat
         := match p with
              | PBHProductionNil _ => 0
              | PBHProductionConsNonTerminal0 _ _ _ _ p0 p1 => S (size_of_pbh'_productions p0 + size_of_pbh'_production p1)
              | PBHProductionConsNonTerminalS _ _ _ _ _ p1 => S (size_of_pbh'_production p1)
              | PBHProductionConsTerminal _ _ _ _ _ _ _ p' => S (size_of_pbh'_production p')
            end.
  End size.
End rel.

Ltac simpl_size_of :=
  repeat match goal with
           | [ |- context G[size_of_pbh'_productions (PBHNil _ _ _ _)] ]
             => let G' := context G[0] in change G'
           | [ H : context G[size_of_pbh'_productions (PBHNil _ _ _ _)] |- _ ]
             => let G' := context G[0] in change G' in H
           | [ |- context G[size_of_pbh'_productions (PBHCons ?g0 ?g1)] ]
             => let G' := context G[S (size_of_pbh'_production g0 + size_of_pbh'_productions g1)] in change G'
           | [ H : context G[size_of_pbh'_productions (PBHCons ?g0 ?g1)] |- _ ]
             => let G' := context G[S (size_of_pbh'_production g0 + size_of_pbh'_productions g1)] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionNil _ _ _ _)] ]
             => let G' := context G[0] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionNil _ _ _ _)] |- _ ]
             => let G' := context G[0] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionConsNonTerminal0 _ _ ?g1 ?g2)] ]
             => let G' := context G[S (size_of_pbh'_productions g1 + size_of_pbh'_production g2)] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionConsNonTerminal0 _ _ ?g1 ?g2)] |- _ ]
             => let G' := context G[S (size_of_pbh'_productions g1 + size_of_pbh'_production g2)] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionConsNonTerminalS _ ?g)] ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionConsNonTerminalS _ ?g)] |- _ ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionConsTerminal _ _ _ _ ?g)] ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionConsTerminal _ _ _ _ ?g)] |- _ ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G' in H
           | _ => progress simpl in *
         end.
