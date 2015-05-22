(** * Well-founded relation on [reachable] *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Parsers.BaseTypes.

Section rel.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT}
          {pdata : paren_balanced_hiding_dataT Char}
          {G : grammar Char}.

  Section size.
    Context {transform_valid : nonterminals_listT -> string -> nonterminals_listT}.

    Fixpoint size_of_pbh'_productions {valid n pats} (p : generic_pbh'_productions G transform_valid valid n pats)
    : nat
      := match p with
           | PBHHead _ _ _ _ p' => S (size_of_pbh'_production p')
           | PBHTail _ _ _ _ p' => S (size_of_pbh'_productions p')
         end
    with size_of_pbh'_production {valid n pat} (p : generic_pbh'_production G transform_valid valid n pat) : nat
         := match p with
              | PBHProductionNil _ _ => 0
              | PBHProductionConsNonTerminal _ _ _ _ _ p0 p1 => S (size_of_pbh'_productions p0 + size_of_pbh'_production p1)
              | PBHProductionConsTerminal _ _ _ _ _ p' => S (size_of_pbh'_production p')
            end.
  End size.
End rel.

Ltac simpl_size_of :=
  repeat match goal with
           | [ |- context G[size_of_pbh'_productions (PBHHead _ ?g)] ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G'
           | [ H : context G[size_of_pbh'_productions (PBHHead _ ?g)] |- _ ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G' in H
           | [ |- context G[size_of_pbh'_productions (PBHTail _ ?g)] ]
             => let G' := context G[S (size_of_pbh'_productions g)] in change G'
           | [ H : context G[size_of_pbh'_productions (PBHTail _ ?g)] |- _ ]
             => let G' := context G[S (size_of_pbh'_productions g)] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionNil _ _ _ _)] ]
             => let G' := context G[0] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionNil _ _ _ _)] |- _ ]
             => let G' := context G[0] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionConsNonTerminal _ _ ?g1 ?g2)] ]
             => let G' := context G[S (size_of_pbh'_productions g1 + size_of_pbh'_production g2)] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionConsNonTerminal _ _ ?g1 ?g2)] |- _ ]
             => let G' := context G[S (size_of_pbh'_productions g1 + size_of_pbh'_production g2)] in change G' in H
           | [ |- context G[size_of_pbh'_production (PBHProductionConsTerminal _ _ _ ?g)] ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G'
           | [ H : context G[size_of_pbh'_production (PBHProductionConsTerminal _ _ _ ?g)] |- _ ]
             => let G' := context G[S (size_of_pbh'_production g)] in change G' in H
           | _ => progress simpl in *
         end.
