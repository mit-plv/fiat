(** * Well-founded relation on [parse_of] *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Relations.Relation_Definitions.
Require Import Parsers.ContextFreeGrammar.

Section rel.
  Context {CharType} {String : string_like CharType} {G : grammar CharType}.

  Section height.

    Definition height_of_parse_item'
               (height_of_parse : forall {str pats} (p : parse_of String G str pats), nat)
               {str it} (p : parse_of_item String G str it) : nat
      := match p with
           | ParseTerminal _ => 0
           | ParseNonTerminal _ _ p' => S (height_of_parse p')
         end.

    Fixpoint height_of_parse {str pats} (p : parse_of String G str pats) : nat
      := match p with
           | ParseHead _ _ _ p' => S (height_of_parse_production p')
           | ParseTail _ _ _ p' => S (height_of_parse p')
         end
    with height_of_parse_production {str pat} (p : parse_of_production String G str pat) : nat
         := match p with
              | ParseProductionNil => 0
              | ParseProductionCons _ _ _ _ p' p''
                => max (S (height_of_parse_item' (@height_of_parse) p')) (S (height_of_parse_production p''))
            end.

    Definition height_of_parse_item
               {str it} (p : parse_of_item String G str it) : nat
      := @height_of_parse_item' (@height_of_parse) str it p.
  End height.

  Definition parse_of_lt {str pats} : relation (parse_of String G str pats)
    := ltof _ height_of_parse.
  Definition parse_of_production_lt {str pat} : relation (parse_of_production String G str pat)
    := ltof _ height_of_parse_production.
  Definition parse_of_item_lt {str it} : relation (parse_of_item String G str it)
    := ltof _ height_of_parse_item.

  Definition parse_of_wf {str pats} : well_founded (@parse_of_lt str pats)
    := well_founded_ltof _ _.
  Definition parse_of_production_wf {str pat} : well_founded (@parse_of_production_lt str pat)
    := well_founded_ltof _ _.
  Definition parse_of_item_wf {str it} : well_founded (@parse_of_item_lt str it)
    := well_founded_ltof _ _.
End rel.
