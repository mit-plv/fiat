(** * Well-founded relation on [reachable] *)
Require Import Fiat.Parsers.ContextFreeGrammar.Core Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Import Fiat.Parsers.BaseTypes.

Section rel.
  Context {Char} {HSLM : StringLikeMin Char} {predata : @parser_computational_predataT Char} {G : grammar Char}.

  Section size.
    Context {ch : Char} {valid : nonterminals_listT}.
    Definition size_of_maybe_empty_item'
               (size_of_maybe_empty_productions : forall {pats}, maybe_empty_productions G valid pats -> nat)
               {it} (p : maybe_empty_item G valid it) : nat
      := match p with
           | MaybeEmptyNonTerminal _ _ p' => S (size_of_maybe_empty_productions p')
         end.


    Fixpoint size_of_maybe_empty_productions {pats} (p : maybe_empty_productions G valid pats) : nat
      := match p with
           | MaybeEmptyHead _ _ p' => S (size_of_maybe_empty_production p')
           | MaybeEmptyTail _ _ p' => S (size_of_maybe_empty_productions p')
         end
    with size_of_maybe_empty_production {pat} (p : maybe_empty_production G valid pat) : nat
         := match p with
              | MaybeEmptyProductionNil => 0
              | MaybeEmptyProductionCons _ _ p0 p1 => S (size_of_maybe_empty_item' (@size_of_maybe_empty_productions) p0 + size_of_maybe_empty_production p1)
            end.

    Definition size_of_maybe_empty_item
               {it} (p : maybe_empty_item G valid it) : nat
      := @size_of_maybe_empty_item' (@size_of_maybe_empty_productions) it p.
  End size.
End rel.
