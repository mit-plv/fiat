(** * Definition of a [comp]-based specification of a CFG parser-recognizer *)
Require Import Fiat.Computation.Core Fiat.Parsers.ContextFreeGrammar.Core.

Set Implicit Arguments.

Definition parser_spec `{StringLike Char}
           (G : grammar Char)
: String -> Comp bool
  := fun str => { b : bool | b = true <-> inhabited (parse_of_grammar str G) }%comp.
