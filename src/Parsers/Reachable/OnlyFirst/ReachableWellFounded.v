(** * Well-founded relation on [reachable] *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.Reachable.OnlyFirst.Reachable.
Require Import Fiat.Parsers.BaseTypes.

Section rel.
  Context {Char} {HSLM : StringLikeMin Char} {predata : @parser_computational_predataT Char} {G : grammar Char}.

  Section size.
    Context {ch : Char} {valid : nonterminals_listT}.
    Definition size_of_reachable_from_item'
               (size_of_reachable_from_productions : forall {pats}, reachable_from_productions G ch valid pats -> nat)
               {it} (p : reachable_from_item G ch valid it) : nat
      := match p with
           | ReachableTerminal _ _ => 0
           | ReachableNonTerminal _ _ p' => S (size_of_reachable_from_productions p')
         end.

    Fixpoint size_of_reachable_from_productions {pats} (p : reachable_from_productions G ch valid pats) : nat
      := match p with
           | ReachableHead _ _ p' => S (size_of_reachable_from_production p')
           | ReachableTail _ _ p' => S (size_of_reachable_from_productions p')
         end
    with size_of_reachable_from_production {pat} (p : reachable_from_production G ch valid pat) : nat
         := match p with
              | ReachableProductionHead _ _ p' => S (size_of_reachable_from_item' (@size_of_reachable_from_productions) p')
              | ReachableProductionTail _ _ _ p' => S (size_of_reachable_from_production p')
            end.

    Definition size_of_reachable_from_item
               {it} (p : reachable_from_item G ch valid it) : nat
      := @size_of_reachable_from_item' (@size_of_reachable_from_productions) it p.
  End size.
End rel.
