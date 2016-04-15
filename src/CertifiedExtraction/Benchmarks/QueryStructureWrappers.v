Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import CertifiedExtraction.Core.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.TuplesF.

Require Import CertifiedExtraction.Utils.

Require Import Bedrock.Memory.
Require Import Refactor.TupleToListW.

Ltac Wrapper_t :=
  abstract (intros * H; inversion H; subst; clear H; f_equal;
            eauto with inj_db).

Instance QS_WrapTuple {N} : FacadeWrapper ADTValue (@RawTuple (MakeWordHeading N)).
Proof.
  refine {| wrap tp := Tuple (TupleToListW tp);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapTupleList {N} : FacadeWrapper ADTValue (list (@RawTuple (MakeWordHeading N))).
Proof.
  refine {| wrap tl := TupleList (List.map TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapWordList : FacadeWrapper ADTValue (list W).
Proof.
  refine {| wrap tl := WordList tl;
            wrap_inj := _ |}; Wrapper_t.
Defined.


Instance QS_WrapBag0 {N} : FacadeWrapper ADTValue (FiatBag N).
Proof.
  refine {| wrap tl := Tuples0 (Word.natToWord 32 N) (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBag1 {N} (M: Word.word 32) : FacadeWrapper ADTValue (FiatBag N).
Proof.
  refine {| wrap tl := Tuples1 (Word.natToWord 32 N) M (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Instance QS_WrapBag2 {N} (M: Word.word 32) (M': Word.word 32) : FacadeWrapper ADTValue (FiatBag N).
Proof.
  refine {| wrap tl := Tuples2 (Word.natToWord 32 N) M M' (IndexedEnsemble_TupleToListW tl);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Require Import CertifiedExtraction.Extraction.External.Core.
Require Import Bedrock.Platform.Facade.examples.QsADTs.

Section TupleLists.
  Lemma CompileTupleList_new :
    forall vret fpointer (env: Env ADTValue) ext tenv N,
      GLabelMap.find fpointer env = Some (Axiomatic TupleList_new) ->
      vret ∉ ext ->
      Lifted_not_mapsto_adt ext tenv vret ->
      {{ tenv }}
        Call vret fpointer nil
      {{ [[ `vret <-- @nil (FiatTuple N) as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    change (ADT (TupleList [])) with (wrap (FacadeWrapper := WrapInstance (H := @QS_WrapTupleList N)) []).
    facade_eauto.
  Qed.

  Lemma CompileTupleList_delete :
    forall vret vlst fpointer (env: Env ADTValue) ext tenv N,
      GLabelMap.find fpointer env = Some (Axiomatic TupleList_delete) ->
      Lifted_MapsTo ext tenv vlst (wrap (@nil (FiatTuple N))) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret <> vlst ->
      vlst ∉ ext ->
      vret ∉ ext ->
      {{ tenv }}
        Call vret fpointer (vlst :: nil)
      {{ [[ `vret <-- SCAZero as _ ]] :: DropName vret (DropName vlst tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    facade_eauto.
    facade_eauto.
  Qed.

  Lemma CompileTupleList_pop :
    forall vret vlst fpointer (env: Env ADTValue) ext tenv N
      h (t: list (FiatTuple N)),
      GLabelMap.find fpointer env = Some (Axiomatic TupleList_pop) ->
      Lifted_MapsTo ext tenv vlst (wrap (h :: t)) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret <> vlst ->
      vlst ∉ ext ->
      vret ∉ ext ->
      {{ tenv }}
        Call vret fpointer (vlst :: nil)
        {{ [[ `vret <-- h as _ ]] :: [[ `vlst <-- t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    facade_eauto.
    facade_eauto.
    facade_eauto.
  Qed.

  Lemma CompileTupleList_push :
    forall vret vhd vlst fpointer (env: Env ADTValue) ext tenv N
      h (t: list (FiatTuple N)),
      GLabelMap.find fpointer env = Some (Axiomatic TupleList_push) ->
      Lifted_MapsTo ext tenv vhd (wrap h) ->
      Lifted_MapsTo ext tenv vlst (wrap t) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret <> vlst ->
      vret <> vhd ->
      vhd <> vlst ->
      vhd ∉ ext ->
      vlst ∉ ext ->
      vret ∉ ext ->
      {{ tenv }}
        Call vret fpointer (vlst :: vhd :: nil)
        {{ [[ `vret <-- SCAZero as _ ]] :: [[ `vlst <-- h :: t as _ ]] :: DropName vlst (DropName vret (DropName vhd tenv)) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    facade_eauto.
    facade_eauto.
    facade_eauto.
    repeat apply DropName_remove; congruence.
  Qed.
End TupleLists.

Hint Resolve Empty_lift : call_helpers_db.
Hint Resolve TupleToListW_length : call_helpers_db.

Section Tuples0.
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
    repeat f_equal; facade_eauto.
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
End Tuples0.

Section Tuples2.
  Lemma CompileTuples2_new :
    forall vret vsize vkey1 vkey2 fpointer (env: Env ADTValue) ext tenv N (k1 k2: W),
      GLabelMap.find fpointer env = Some (Axiomatic Tuples2_new) ->
      Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
      Lifted_MapsTo ext tenv vkey1 (wrap k1) ->
      Lifted_MapsTo ext tenv vkey2 (wrap k2) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      vret ∉ ext ->
      Word.wlt k1 (Word.natToWord 32 N) ->
      Word.wlt k2 (Word.natToWord 32 N) ->
      ~ Word.wlt (Word.natToWord 32 N) (Word.natToWord 32 2) ->
      {{ tenv }}
        Call vret fpointer (vsize :: vkey1 :: vkey2 :: nil)
      {{ [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vret) <-- @FiatEmpty N as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    facade_eauto.
    repeat f_equal; facade_eauto.
    facade_eauto.
  Qed.
End Tuples2.