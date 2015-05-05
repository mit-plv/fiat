(** Refinement rules for disjoint rules *)
Require Import Coq.Lists.List.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.ParserInterface.

Set Implicit Arguments.

Lemma refine_disjoint_search_for {G : grammar Ascii.ascii} {str nt its}
      (H_disjoint : disjoint ascii_beq
                             (possible_terminals_of G nt)
                             (possible_first_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str
             (NonTerminal nt)
             its splits}
         (n <- { n : nat | n <= length str
                           /\ is_first_char_such_that
                                (might_be_empty (possible_first_terminals_of_production G its))
                                str
                                n
                                (fun ch => list_bin ascii_beq ch (possible_first_terminals_of_production G its)) };
          ret [n]).
Proof.
  intros ls H.
  computes_to_inv; subst.
  destruct H as [H0 H1].
  apply PickComputes.
  intros n ? H_reachable pit pits Hpit Hpits.
  left.
  pose proof (terminals_disjoint_search_for _ H_disjoint _ _ H_reachable Hpit Hpits) as H'.
  Locate disjoint.

(first_char_in
            (drop n str)
            (possible_first_terminals_of_production G its)
Lemma terminals_disjoint_search_for {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: forall_chars (take n str)
               (fun ch => negb (list_bin ascii_beq ch (possible_first_terminals_of_production G its)))
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (first_char_in
            (drop n str)
            (possible_first_terminals_of_production G its))).
Proof.

{splits : list nat |
                       ParserInterface.split_list_is_complete
                         plus_expr_grammar (string_of_indexed r_n)
                         (NonTerminal "number")
                         [Terminal "+"%char; NonTerminal "expr"] splits}
