Require Import Fiat.Parsers.Reflective.Syntax Fiat.Parsers.Reflective.ParserSyntax.
Require Import Fiat.Parsers.Reflective.PartialUnfold.

Section normalization_by_evaluation.
  Context (var : TypeCode -> Type).

  Definition pnormalize {T} (term : has_parse_term (normalized_of var) T) : has_parse_term var T
    := match term with
       | RFix2 G_length up_to_G_length f default valid_len valids nt_idx
         => RFix2 G_length up_to_G_length
                  (normalize f)
                  (normalize default)
                  valid_len valids nt_idx
       end.
End normalization_by_evaluation.

Definition polypnormalize {T} (term : polyhas_parse_term T) : polyhas_parse_term T
  := fun var => pnormalize (term _).
