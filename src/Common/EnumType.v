Require Import
        Coq.Vectors.Vector
        Coq.Vectors.VectorDef.

Require Import
        Fiat.Common.BoundedLookup.

Import Vectors.VectorDef.VectorNotations.
Local Open Scope vector_scope.
Local Open Scope string_scope.

Definition EnumType
           {len : nat}
           {A : Type}
           (ta : t A (S len)) := Fin.t (S len).

Definition EnumType_inj_BoundedIndex {len} {A} {ta}
           (e : @EnumType len A ta) : BoundedIndex ta :=
   {| indexb := {| ibound := e; boundi := eq_refl |} |}.

Definition BoundedIndex_inj_EnumType {len} {A} {ta}
           (idx : BoundedIndex ta) : @EnumType len A ta :=
  idx.(indexb).(ibound).

Coercion EnumType_inj_BoundedIndex : EnumType >-> BoundedIndex.

Notation "``` idx" := (BoundedIndex_inj_EnumType ``idx) (at level 0).

Global Arguments EnumType {len} {A} ta%vector_scope.
