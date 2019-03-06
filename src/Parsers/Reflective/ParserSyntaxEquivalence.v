(** * Equivalence on syntax *)
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.SyntaxEquivalence.

Section has_parse_term_equiv.
  Context (var1 var2 : TypeCode -> Type).

  Inductive has_parse_term_equiv {T} : ctxt var1 var2 -> has_parse_term var1 T -> has_parse_term var2 T -> Prop :=
  | EqFix2
      (G_length : nat) (up_to_G_length : list nat)
      (valid_len : nat)
      (valids : list nat)
      (nt_idx : nat)
    : forall G f1 f2 default1 default2,
      Term_equiv G f1 f2
      -> Term_equiv G default1 default2
      -> has_parse_term_equiv
           G
           (RFix2 G_length up_to_G_length f1 default1 valid_len valids nt_idx)
           (RFix2 G_length up_to_G_length f2 default2 valid_len valids nt_idx).
End has_parse_term_equiv.
