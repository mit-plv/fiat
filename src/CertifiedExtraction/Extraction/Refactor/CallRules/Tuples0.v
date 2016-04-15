Require Export Fiat.Computation.Notations. (* FIXME remove *)
Require Import Refactor.CallRules.Core.

Lemma CompileTuples0_new :
  forall vret vsize fpointer (env: Env ADTValue) ext tenv N,
    GLabelMap.find fpointer env = Some (Axiomatic Tuples0_new) ->
    Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    vret ∉ ext ->
    ~ Word.wlt (Word.natToWord 32 N) (Word.natToWord 32 2) ->
    {{ tenv }}
      Call vret fpointer (vsize :: nil)
    {{ [[ `vret <-- @FiatEmpty N as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  repeat f_equal; facade_eauto. (* Uses Empty_lift *)
  facade_eauto.
Qed.

(* Lemma CompileTuples0_insert : *)
(*   forall vret vtable vtuple fpointer (env: Env ADTValue) ext tenv N idx *)
(*     (table: FiatBag N) (tuple: FiatTuple N), *)
(*     GLabelMap.find fpointer env = Some (Axiomatic Tuples0_insert) -> *)
(*     Lifted_MapsTo ext tenv vtable (wrap table) -> *)
(*     Lifted_MapsTo ext tenv vtuple (wrap tuple) -> *)
(*     Lifted_not_mapsto_adt ext tenv vret -> *)
(*     NoDuplicates [[[vret; vtable; vtuple]]] -> *)
(*     vret ∉ ext -> *)
(*     vtable ∉ ext -> *)
(*     vtuple ∉ ext -> *)
(*     BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) -> *)
(*     minFreshIndex (IndexedEnsemble_TupleToListW table) idx -> *)
(*     {{ tenv }} *)
(*       Call vret fpointer (vtable :: vtuple :: nil) *)
(*     {{ [[ `vret <-- SCAZero as _ ]] *)
(*          :: [[ `vtable <-- table as _ ]] *)
(*          :: DropName vtable (DropName vret (DropName vtuple tenv)) }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t). *)

(* Definition FiatBagFunctional {N} (fiatBag: FiatBag N) := *)
(*   forall t1 t2, *)
(*     fiatBag t1 -> fiatBag t2 -> *)
(*     IndexedEnsembles.elementIndex t1 = IndexedEnsembles.elementIndex t2 -> *)
(*     t1 = t2. *)

(* Definition FiatBagMinFreshIndex {N} (fiatBag: FiatBag N) idx := *)
(*   IndexedEnsembles.UnConstrFreshIdx fiatBag idx /\ *)
(*   (forall idx' : nat, (lt idx' idx) -> ~ IndexedEnsembles.UnConstrFreshIdx fiatBag idx'). *)

(* Record FiatBag' {N} := *)
(*   { fiatBag : FiatBag N; *)
(*     bagFunctional : FiatBagFunctional fiatBag; *)
(*     idx: nat; *)
(*     idxIsFresh: FiatBagMinFreshIndex fiatBag idx }. *)

(* Lemma minFreshIndex_Lift: *)
(*   forall (N : nat) (table : FiatBag N) (idx : nat), *)
(*     FiatBagMinFreshIndex table idx -> *)
(*     minFreshIndex (IndexedEnsemble_TupleToListW table) idx. *)
(* Proof. *)
(*   unfold FiatBagMinFreshIndex, minFreshIndex. *)
(*   repeat cleanup. *)

(*   Lemma UnconstrFreshIdx_Lift: *)
(*     forall (N : nat) (table : FiatBag N) (idx : nat), *)
(*       IndexedEnsembles.UnConstrFreshIdx table idx <-> UnConstrFreshIdx (IndexedEnsemble_TupleToListW table) idx. *)
(*   Proof. *)
(*     unfold IndexedEnsembles.UnConstrFreshIdx, UnConstrFreshIdx; *)
(*     repeat cleanup. *)
(*     rewrite <- IndexedElement_RoundTrip in H0. *)
(*     pose (IndexedEnsemble_TupleToListW_inj_helpe _ table (IndexedElement_ListWToTuple element)). H0). *)
(*   Admitted. *)

(*   apply UnconstrFreshIdx_Lift; assumption. *)
(*   rewrite <- UnconstrFreshIdx_Lift. *)
(*   eauto. *)
(* Qed. *)

(*   facade_eauto. *)
(*   facade_eauto. *)
(*   facade_eauto. *)
(*   admit. *)
(*   repeat apply DropName_remove; eauto 1. *)
(* Qed. *)

(* Lemma CompileTuples0_enumerate : *)
(*   forall vret vtable fpointer (env: Env ADTValue) ext tenv N *)
(*     (table: FiatBag N) (tuple: FiatTuple N), *)
(*     GLabelMap.find fpointer env = Some (Axiomatic Tuples0_enumerate) -> *)
(*     Lifted_MapsTo ext tenv vtable (wrap table) -> *)
(*     Lifted_not_mapsto_adt ext tenv vret -> *)
(*     NoDuplicates [[[vret; vtable]]] -> *)
(*     vret ∉ ext -> *)
(*     BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) -> *)
(*     {{ tenv }} *)
(*       Call vret fpointer (vtable :: nil) *)
(*     {{ [[ `vret <-- @nil (FiatTuple N) as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t). *)
(*   facade_eauto. *)
(*   admit.                      (* FIXME *) *)
(*   rewrite <- remove_add_comm by congruence. *)
(*   rewrite <- add_redundant_cancel by eassumption. *)
(*   facade_eauto. *)
(* Qed. *)
