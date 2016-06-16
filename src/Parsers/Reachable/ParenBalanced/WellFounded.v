(** * Well-founded relation on [reachable] *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.Reachable.ParenBalanced.Core.
Require Import Fiat.Parsers.BaseTypes.

Section rel.
  Context {Char} {HSLM : StringLikeMin Char} {predata : @parser_computational_predataT Char}
          {pdata : paren_balanced_hiding_dataT Char}
          {G : grammar Char}.

  Section size.
    Context {transform_valid : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT}.

    Fixpoint size_of_pb'_productions {valid pats} (p : generic_pb'_productions G transform_valid valid pats)
    : nat
      := match p with
           | PBNil _ => 0
           | PBCons _ _ _ p0 p1 => S (size_of_pb'_production p0 + size_of_pb'_productions p1)
         end
    with size_of_pb'_production {valid n pat} (p : generic_pb'_production G transform_valid valid n pat) : nat
         := match p with
              | PBProductionNil _ => 0
              | PBProductionConsNonTerminal _ _ _ _ _ p0 p1 => S (size_of_pb'_productions p0 + size_of_pb'_production p1)
              | PBProductionConsTerminal _ _ _ _ _ _ _ p' => S (size_of_pb'_production p')
            end.
  End size.
End rel.

Ltac simpl_size_of :=
  repeat match goal with
           | [ |- context G[size_of_pb'_productions (PBNil _ _ _)] ]
             => let G' := context G[0] in change G'
           | [ H : context G[size_of_pb'_productions (PBNil _ _ _)] |- _ ]
             => let G' := context G[0] in change G' in H
           | [ |- context G[size_of_pb'_productions (PBCons ?g0 ?g1)] ]
             => let G' := context G[S (size_of_pb'_production g0 + size_of_pb'_productions g1)] in change G'
           | [ H : context G[size_of_pb'_productions (PBCons ?g0 ?g1)] |- _ ]
             => let G' := context G[S (size_of_pb'_production g0 + size_of_pb'_productions g1)] in change G' in H
           | [ |- context G[size_of_pb'_production (PBProductionNil _ _ _)] ]
             => let G' := context G[0] in change G'
           | [ H : context G[size_of_pb'_production (PBProductionNil _ _ _)] |- _ ]
             => let G' := context G[0] in change G' in H
           | [ |- context G[size_of_pb'_production (PBProductionConsNonTerminal _ _ ?g1 ?g2)] ]
             => let G' := context G[S (size_of_pb'_productions g1 + size_of_pb'_production g2)] in change G'
           | [ H : context G[size_of_pb'_production (PBProductionConsNonTerminal _ _ ?g1 ?g2)] |- _ ]
             => let G' := context G[S (size_of_pb'_productions g1 + size_of_pb'_production g2)] in change G' in H
           | [ |- context G[size_of_pb'_production (PBProductionConsTerminal _ _ _ _ ?g)] ]
             => let G' := context G[S (size_of_pb'_production g)] in change G'
           | [ H : context G[size_of_pb'_production (PBProductionConsTerminal _ _ _ _ ?g)] |- _ ]
             => let G' := context G[S (size_of_pb'_production g)] in change G' in H
           | _ => progress simpl in *
         end.
