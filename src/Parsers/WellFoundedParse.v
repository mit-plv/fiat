(** * Well-founded relation on [parse_of] *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.

Section rel.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.

  Section size.
    Definition size_of_parse_item'
               (size_of_parse : forall {str pats} (p : parse_of G str pats), nat)
               {str it} (p : parse_of_item G str it) : nat
      := match p with
           | ParseTerminal _ _ => 0
           | ParseNonTerminal _ p' => S (size_of_parse p')
         end.

    Fixpoint size_of_parse {str pats} (p : parse_of G str pats) : nat
      := match p with
           | ParseHead _ _ p' => S (size_of_parse_production p')
           | ParseTail _ _ p' => S (size_of_parse p')
         end
    with size_of_parse_production {str pat} (p : parse_of_production G str pat) : nat
         := match p with
              | ParseProductionNil _ => 0
              | ParseProductionCons _ _ _ p' p''
                => S (size_of_parse_item' (@size_of_parse) p' + size_of_parse_production p'')
            end.

    Definition size_of_parse_item
               {str it} (p : parse_of_item G str it) : nat
      := @size_of_parse_item' (@size_of_parse) str it p.
  End size.

  Definition parse_of_lt {str pats} : relation (parse_of G str pats)
    := ltof _ size_of_parse.
  Definition parse_of_production_lt {str pat} : relation (parse_of_production G str pat)
    := ltof _ size_of_parse_production.
  Definition parse_of_item_lt {str it} : relation (parse_of_item G str it)
    := ltof _ size_of_parse_item.

  Definition parse_of_wf {str pats} : well_founded (@parse_of_lt str pats)
    := well_founded_ltof _ _.
  Definition parse_of_production_wf {str pat} : well_founded (@parse_of_production_lt str pat)
    := well_founded_ltof _ _.
  Definition parse_of_item_wf {str it} : well_founded (@parse_of_item_lt str it)
    := well_founded_ltof _ _.
End rel.
