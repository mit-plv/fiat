open Hint_db_extra_tactics
open API
open Stdarg
open Ltac_plugin
open Tacarg

DECLARE PLUGIN "hint_db_extra_plugin"

TACTIC EXTEND foreach_db
  | [ "foreach" "[" ne_preident_list(l) "]" "run" tactic(k) ]  ->
     [ WITH_DB.with_hint_db l k ]
       END

TACTIC EXTEND addto_db
  | [ "add" constr(name) "to" ne_preident_list(l) ]  ->
     [ WITH_DB.add_resolve_to_db (Hints.IsConstr (name, Univ.ContextSet.empty)) l]
       END;;
