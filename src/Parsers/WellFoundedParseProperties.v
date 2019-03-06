(** * Properties about well-founded relation on [parse_of] *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.WellFoundedParse.

Set Implicit Arguments.

Local Notation "R ==> R'" := (@respectful_hetero _ _ _ _ R R')
                               (at level 55, right associativity)
                             : dep_signature_scope.
Delimit Scope dep_signature_scope with signatureD.

Section rel.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.

  Fixpoint size_of_parse_respectful {str str' pats pats'} (Hpats : productions_code pats pats') (H : str =s str') (p : parse_of G str pats)
  : size_of_parse p = size_of_parse (parse_of_respectful H Hpats p)
  with size_of_parse_production_respectful {str str' pat pat'} (Hpat : production_code pat pat') (H : str =s str') (p : parse_of_production G str pat)
       : size_of_parse_production p = size_of_parse_production (parse_of_production_respectful H Hpat p)
  with size_of_parse_item_respectful {str str' it it'} (Hit : item_code it it') (H : str =s str') (p : parse_of_item G str it)
       : size_of_parse_item p = size_of_parse_item (parse_of_item_respectful H Hit p).
  Proof.
    { refine (match p, pats' return forall Hpats : productions_code _ pats', size_of_parse p = size_of_parse (parse_of_respectful H Hpats p) with
                | ParseHead _ _ p', _::_ => fun Hpats' => _ (*f_equal S (@size_of_parse_production_respectful _ _ _ _ _ H p')*)
                | ParseTail _ _ p', _::_ => fun Hpats' => _ (*f_equal S (size_of_parse_respectful H p')*)
                | _, nil => fun Hpats' => match _ : False with end
              end Hpats);
      try solve [ simpl in *; clear -Hpats'; abstract inversion Hpats' ];
      simpl_parse_of_respectful;
      simpl_size_of_parse;
      apply (f_equal S).
      { apply size_of_parse_production_respectful. }
      { apply size_of_parse_respectful. } }
    { refine (match p, pat' return forall Hpat : production_code _ pat', size_of_parse_production p = size_of_parse_production (parse_of_production_respectful H Hpat p) with
                | ParseProductionNil _, nil => fun Hpat' => eq_refl
                | ParseProductionCons _ _ _ _ _, _::_
                  => fun Hpat'
                     => f_equal2 (fun x y => S (x + y))
                                 (@size_of_parse_item_respectful _ _ _ _ _ _ _)
                                 (@size_of_parse_production_respectful _ _ _ _ _ _ _)
                | _, _ => fun Hpat' => match _ : False with end
              end Hpat);
      try solve [ simpl in *; clear -Hpat'; abstract inversion Hpat' ]. }
    { refine (match p, it' return forall Hit : item_code _ it', size_of_parse_item p = size_of_parse_item (parse_of_item_respectful H Hit p)  with
                | ParseTerminal _ _ _ _, Terminal _ => fun Hit' => eq_refl
                | ParseNonTerminal _ H' p', NonTerminal _ => fun Hit' => f_equal S (@size_of_parse_respectful _ _ _ _ _ H p')
                | _, _ => fun Hit' => match _ : False with end
              end Hit);
      try solve [ simpl in *; clear -Hit'; abstract inversion Hit' ]. }
  Defined.

  Global Instance size_of_parse_ProperD {pats}
  : Proper (beq ==> (fun str str' => (fun p p' => forall H Hpat, p = parse_of_respectful H Hpat p') ==> (fun _ _ => @eq nat)))%signatureD
           (fun str => @size_of_parse Char _ _ G str pats).
  Proof.
    intros ?? H p p' H'.
    rewrite (H' (symmetry H) (reflexivity _)).
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
    reflexivity.
  Qed.
End rel.
