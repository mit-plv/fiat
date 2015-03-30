(** * Definition of a [comp]-based specification of a CFG parser-recognizer *)
Require Import ADTSynthesis.Computation.Core ADTSynthesis.Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Definition parser_spec {string} `{StringLike string}
           (G : grammar string)
: String -> Comp bool
  := fun str => { b : bool | b = true <-> inhabited (parse_of_grammar str G) }%comp.
