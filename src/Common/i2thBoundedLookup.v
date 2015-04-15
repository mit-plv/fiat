Require Import Coq.Lists.List Coq.Strings.String Coq.Arith.Arith Fiat.Common.ilist Fiat.Common.i2list Fiat.Common.StringBound.

(* Typeclasses for ensuring that a string is included
   in a list (i.e. a set of method names). This allows
   us to omit a default case (method not found) for method
   lookups. *)
