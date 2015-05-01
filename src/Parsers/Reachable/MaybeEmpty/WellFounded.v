(** * Well-founded relation on [reachable] *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Import Fiat.Parsers.BaseTypes.

Section rel.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT} {G : grammar Char}.

  Section size.
    Context {ch : Char} {valid : nonterminals_listT}.
    Definition size_of_maybe_empty_item'
               (size_of_maybe_empty_productions : forall {pats}, maybe_empty_productions G ch valid pats -> nat)
               {it} (p : maybe_empty_item G ch valid it) : nat
      := match p with
           | MaybeEmptyTerminal => 0
           | MaybeEmptyNonTerminal _ _ p' => S (size_of_maybe_empty_productions p')
         end.

    Fixpoint size_of_maybe_empty_productions {pats} (p : maybe_empty_productions G ch valid pats) : nat
      := match p with
           | MaybeEmptyHead _ _ p' => S (size_of_maybe_empty_production p')
           | MaybeEmptyTail _ _ p' => S (size_of_maybe_empty_productions p')
         end
    with size_of_maybe_empty_production {pat} (p : maybe_empty_production G ch valid pat) : nat
         := match p with
              | MaybeEmptyProductionHead _ _ p' => S (size_of_maybe_empty_item' (@size_of_maybe_empty_productions) p')
              | MaybeEmptyProductionTail _ _ p' => S (size_of_maybe_empty_production p')
            end.

    Definition size_of_maybe_empty_item
               {it} (p : maybe_empty_item G ch valid it) : nat
      := @size_of_maybe_empty_item' (@size_of_maybe_empty_productions) it p.
  End size.
End rel.
