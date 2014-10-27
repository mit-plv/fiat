(** * Definition of a [comp]-based specification of a CFG parser-recognizer *)
Require Import Computation.Core Parsers.ContextFreeGrammar.

Set Implicit Arguments.

Definition parser_spec CharType (String : string_like CharType)
           (G : grammar CharType)
: String -> Comp bool
  := fun str => { b : bool | b = true <-> inhabited (parse_of_grammar String str G) }%comp.
