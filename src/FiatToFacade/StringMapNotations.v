Require Export Fiat.Common.Coq__8_4__8_5__Compat.
Require Export Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Platform.Cito.StringMap.

Notation "table [ key >> value ]" := (StringMap.MapsTo key value table) (at level 0) : map_scope.
Notation "∅" := (StringMap.empty _) : map_scope.

Notation "[ k >sca> v ] :: m" :=
  (StringMap.add k (SCA _ v) m) (at level 22, right associativity) : map_scope.
Notation "[ k >adt> v ] :: m" :=
  (StringMap.add k (ADT v) m) (at level 22, right associativity) : map_scope.
Notation "[ k >> v ] :: m" :=
  (StringMap.add k v m) (at level 22, right associativity) : map_scope.

Delimit Scope map_scope with map.
Open Scope map_scope.
