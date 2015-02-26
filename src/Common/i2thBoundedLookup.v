Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith ADTSynthesis.Common.ilist ADTSynthesis.Common.i2list ADTSynthesis.Common.StringBound.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)
