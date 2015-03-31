(** * Properties about well-founded relation on [parse_of] *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program Coq.Program.Wf Coq.Arith.Wf_nat Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.Morphisms.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.ContextFreeGrammarProperties.
Require Import ADTSynthesis.Parsers.WellFoundedParse.

Set Implicit Arguments.

Local Notation "R ==> R'" := (@respectful_hetero _ _ _ _ R R')
                               (at level 55, right associativity)
                             : dep_signature_scope.
Delimit Scope dep_signature_scope with signatureD.

Section rel.
  Context {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.

  Fixpoint size_of_parse_respectful {str str' pats} (H : str =s str') (p : parse_of G str pats)
  : size_of_parse p = size_of_parse (parse_of_respectful H p)
    := match p return size_of_parse p = size_of_parse (parse_of_respectful H p) with
         | ParseHead _ _ p' => f_equal S (size_of_parse_production_respectful H p')
         | ParseTail _ _ p' => f_equal S (size_of_parse_respectful H p')
       end
  with size_of_parse_production_respectful {str str' pat} (H : str =s str') (p : parse_of_production G str pat)
       : size_of_parse_production p = size_of_parse_production (parse_of_production_respectful H p)
       := match p return size_of_parse_production p = size_of_parse_production (parse_of_production_respectful H p) with
            | ParseProductionNil _ => eq_refl
            | ParseProductionCons _ _ _ _ _ => f_equal2 (fun x y => S (x + y))
                                                        (size_of_parse_item_respectful _ _)
                                                        (size_of_parse_production_respectful _ _)
          end
  with size_of_parse_item_respectful {str str' it} (H : str =s str') (p : parse_of_item G str it)
       : size_of_parse_item p = size_of_parse_item (parse_of_item_respectful H p)
       := match p with
            | ParseTerminal _ _ => eq_refl
            | ParseNonTerminal _ p' => f_equal S (size_of_parse_respectful H p')
          end.

  Global Instance size_of_parse_ProperD {pats}
  : Proper (beq ==> (fun str str' => (fun p p' => forall H, p = parse_of_respectful H p') ==> (fun _ _ => @eq nat)))%signatureD
           (fun str => @size_of_parse Char _ G str pats).
  Proof.
    intros ?? H p p' H'.
    rewrite (H' (symmetry H)).
    rewrite <- size_of_parse_respectful; reflexivity.
  Qed.

  Global Instance size_of_parse_Proper {pats} {P : _ -> Prop}
  : Proper (beq ==> impl)
           (fun str =>
              forall p : parse_of G str pats,
                P (size_of_parse p)).
  Proof.
    repeat intro.
    erewrite size_of_parse_respectful.
    apply H0.
    Grab Existential Variables.
    symmetry; assumption.
  Qed.
End rel.
