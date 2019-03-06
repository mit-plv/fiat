(** * Well-founded relation on [parse_of] *)
Require Import Coq.Strings.String Coq.Arith.Wf_nat Coq.Relations.Relation_Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.

Section rel.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {G : grammar Char}.

  Section size.
    Definition size_of_parse_item'
               (size_of_parse : forall {str pats} (p : parse_of G str pats), nat)
               {str it} (p : parse_of_item G str it) : nat
      := match p with
           | ParseTerminal _ _ _ _ => 0
           | ParseNonTerminal _ _ p' => S (size_of_parse p')
         end.

    Section bodies.
      Context (size_of_parse : forall {str pats} (p : parse_of G str pats), nat)
              (size_of_parse_production : forall {str pat} (p : parse_of_production G str pat), nat).

      Definition size_of_parse_step {str pats} (p : parse_of G str pats) : nat
        := match p with
             | ParseHead _ _ p' => S (@size_of_parse_production _ _ p')
             | ParseTail _ _ p' => S (@size_of_parse _ _ p')
           end.

      Definition size_of_parse_production_step {str pat} (p : parse_of_production G str pat) : nat
        := match p with
             | ParseProductionNil _ => 0
             | ParseProductionCons _ _ _ p' p''
               => S (size_of_parse_item' (@size_of_parse) p' + @size_of_parse_production _ _ p'')
           end.

      Global Arguments size_of_parse_step _ _ !_ / .
      Global Arguments size_of_parse_production_step _ _ !_ / .
    End bodies.

    Fixpoint size_of_parse {str pats} (p : parse_of G str pats) : nat
      := @size_of_parse_step (@size_of_parse) (@size_of_parse_production) str pats p
    with size_of_parse_production {str pat} (p : parse_of_production G str pat) : nat
         := @size_of_parse_production_step (@size_of_parse) (@size_of_parse_production) str pat p.

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

Ltac simpl_size_of_parse :=
  repeat match goal with
           | [ |- context[@size_of_parse ?Char ?HSLM ?HSL ?G ?str ?pat ?p] ]
             => change (@size_of_parse Char HSLM HSL G str pat p)
                with (@size_of_parse_step Char HSLM HSL G (@size_of_parse Char HSLM HSL G) (@size_of_parse_production Char HSLM HSL G) str pat p);
               simpl @size_of_parse_step
           | [ |- context[@size_of_parse_production ?Char ?HSLM ?HSL ?G ?str ?pat ?p] ]
             => change (@size_of_parse_production Char HSLM HSL G str pat p)
                with (@size_of_parse_production_step Char HSLM HSL G (@size_of_parse Char HSLM HSL G) (@size_of_parse_production Char HSLM HSL G) str pat p);
               simpl @size_of_parse_production_step
         end.
