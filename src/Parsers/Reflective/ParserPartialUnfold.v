Require Import Coq.Strings.String Coq.Strings.Ascii.
Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.PartialUnfold.

Section normalization_by_evaluation.
  Context (var : TypeCode -> Type).

  Definition pnormalize (term : has_parse_term (normalized_of var)) : has_parse_term var
    := match term with
       | RFix2 G_length up_to_G_length f valid_len valids nt_idx
         => RFix2 G_length up_to_G_length
                  (normalize f)
                  valid_len valids nt_idx
       end.
End normalization_by_evaluation.

Definition polypnormalize (term : polyhas_parse_term) : polyhas_parse_term
  := fun var => pnormalize (term _).
