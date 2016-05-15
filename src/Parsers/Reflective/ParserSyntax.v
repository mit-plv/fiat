Require Import Fiat.Parsers.Reflective.Syntax.

Local Notation rcStepT cbool retT :=
  ((*Rchar_at_matches_interp*)
    (cnat --> crchar_expr_ascii --> cbool)
      --> (*Rsplit_string_for_production*)
      (cnat * (cnat * cnat) --> cnat --> cnat --> (clist cnat))
      --> cnat --> cnat --> (cnat --> cnat --> cnat --> retT) --> clist cnat --> cnat --> cnat --> cnat --> retT)%typecode
                                                                                                                   (only parsing).

Inductive has_parse_term var (T : SimpleTypeCode) : Type :=
| RFix2
    (G_length : nat) (up_to_G_length : list nat)
    (f : Term var (rcStepT cbool T))
    (default : Term var T)
    (valid_len : nat)
    (valids : list nat)
    (nt_idx : nat).

Definition polyhas_parse_term T := forall var, has_parse_term var T.
