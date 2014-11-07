Require Import StringMap.
Require Import Facade.
        
Definition Superset
           {elt wrapped_elt}
           (state bindings: StringMap.t wrapped_elt)
           (wrapper: elt -> wrapped_elt) :=
  forall k v, StringMap.MapsTo k (wrapper v) bindings -> StringMap.MapsTo k (wrapper v) state.

Definition SomeSCAs {av} (state : State av) bindings :=
  Superset state bindings (SCA av).

Definition AllADTs {av} (state: State av) bindings  :=
  Superset state bindings (@ADT av) /\
  Superset bindings state (@ADT av).

Lemma AllADTs_equiv :
  forall {av} (state bindings: State av),
    AllADTs state bindings <->
    (forall k v, StringMap.MapsTo k (ADT v) bindings <-> StringMap.MapsTo k (ADT v) state).
Proof.
  firstorder.
Qed.
