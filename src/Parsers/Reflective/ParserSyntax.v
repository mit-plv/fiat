Require Import Fiat.Parsers.Reflective.Syntax.

Local Notation rcStepT cbool :=
  ((*Rchar_at_matches_interp*)
    (cnat --> crchar_expr_ascii --> cbool)
      --> (*Rsplit_string_for_production*)
      (cnat * (cnat * cnat) --> cnat --> cnat --> (clist cnat))
      --> cnat --> cnat --> (cnat --> cnat --> cnat --> cbool) --> clist cnat --> cnat --> cnat --> cnat --> cbool)%typecode
                                                                                                                   (only parsing).

Inductive has_parse_term var : Type :=
| RFix2
    (G_length : nat) (up_to_G_length : list nat)
    (f : Term var (rcStepT cbool))
    (valid_len : nat)
    (valids : list nat)
    (nt_idx : nat).

Definition polyhas_parse_term := forall var, has_parse_term var.
