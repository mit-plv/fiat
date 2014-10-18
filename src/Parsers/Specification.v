(** * Definition of a [comp]-based specification of a CFG parser-recognizer *)
Require Import Computation.Core Parsers.StringLike Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Module ParserSpecification (S : StringLike).
  Import S.
  Module Import G0 := ContextFreeGrammar S.

  Definition parser_spec
             (G : grammar)
  : t -> Comp bool
    := fun str => { b : bool | b = true <-> inhabited (parse_of_grammar str G) }%comp.
End ParserSpecification.
