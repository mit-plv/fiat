(** * Equivalence on syntax *)
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.

Section has_parse_term_equiv.
  Context (var1 var2 : TypeCode -> Type).

  Inductive has_parse_term_equiv : ctxt var1 var2 -> has_parse_term var1 -> has_parse_term var2 -> Prop :=
  | EqFix2
      (G_length : nat) (up_to_G_length : list nat)
      (valid_len : nat)
      (valids : list nat)
      (nt_idx : nat)
    : forall G f1 f2,
      Term_equiv G f1 f2
      -> has_parse_term_equiv
           G
           (RFix2 G_length up_to_G_length f1 valid_len valids nt_idx)
           (RFix2 G_length up_to_G_length f2 valid_len valids nt_idx)
  | EqRefl' : forall (E : polyhas_parse_term),
      has_parse_term_equiv nil (E var1) (E var2).
End has_parse_term_equiv.
