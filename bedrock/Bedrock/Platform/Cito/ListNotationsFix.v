Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Notation " [ ] " := (@nil _) : list_scope.
Notation " [ x , .. , y ] " := (cons x .. (cons y nil) ..) : list_scope.
Notation " [[ ]] " := (@nil _) : list_scope.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..) : list_scope.
