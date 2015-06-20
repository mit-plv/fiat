(** * Properties about Context Free Grammars *)
Require Import Fiat.Parsers.StringLike.Core Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Section convenience.
  Context {Char} {HSL : StringLike Char} {HSLP : @StringLikeProperties Char HSL}
          (G : grammar Char).

  Let predata := rdp_list_predata (G := G).
  Local Existing Instance predata.

  Local Notation iffT A B := ((A -> B) * (B -> A))%type.
  Local Infix "<->" := iffT : type_scope.

  Local Ltac t Forall_parse_of expand_forall_parse_of parse_of_respectful parse_of_respectful_refl :=
    repeat match goal with
             | [ |- context G[@Forall_parse_of _ _ _ ?f _ _ ?p] ]
               => is_var p;
                 replace (@Forall_parse_of _ _ _ f _ _ p) with (@Forall_parse_of _ _ _ f _ _ (@parse_of_respectful _ _ _ _ _ _ (reflexivity _) _ p))
                    by (rewrite parse_of_respectful_refl; reflexivity)
             | [ |- prod _ _ ] => split
             | [ |- _ -> _ ] => eapply expand_forall_parse_of
             | _ => progress simpl
             | _ => progress unfold rdp_list_is_valid_nonterminal
             | _ => progress intros
             | [ H : is_true (list_bin string_beq _ _) |- _ ] => apply (list_in_bl (@string_bl)) in H
             | [ |- is_true (list_bin string_beq _ _) ] => apply (list_in_lb (@string_lb))
             | _ => assumption
           end.

  Definition expand_forall_parse_of_default {str pats} (p : parse_of G str pats)
  : Forall_parse_of (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt) p
    <-> Forall_parse_of (fun _ nt => List.In nt (Valid_nonterminals G)) p.
  Proof.
    t (@Forall_parse_of) (@expand_forall_parse_of) (@parse_of_respectful) (@parse_of_respectful_refl).
  Qed.

  Definition expand_forall_parse_of_item_default {str x} (p : parse_of_item G str x)
  : Forall_parse_of_item (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt) p
    <-> Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) p.
  Proof.
    t (@Forall_parse_of_item) (@expand_forall_parse_of_item) (@parse_of_item_respectful) (@parse_of_item_respectful_refl).
  Qed.

  Definition expand_forall_parse_of_production_default {str x} (p : parse_of_production G str x)
  : Forall_parse_of_production (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt) p
    <-> Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) p.
  Proof.
    t (@Forall_parse_of_production) (@expand_forall_parse_of_production) (@parse_of_production_respectful) (@parse_of_production_respectful_refl).
  Qed.
End convenience.
