Require Import CertifiedExtraction.Extraction.QueryStructures.CallRules.Core.

Module Type BagOfTuples0TupleCompilationParams (Params: BagOfTuples0ADTSpecParams).
  Import Params.
  Parameter FiatBag : nat -> Type.
  (* Parameter FiatEmpty : forall N: nat, FiatBag N. *)
  Parameter FiatBagToBedrockBag : forall {N}, FiatBag N -> GenericTuples FieldType.
  Axiom FiatBagToBedrockBag_inj : forall {N}, Injective (@FiatBagToBedrockBag N).
  (* Axiom FiatEmptyIsEmpty : forall {N}, FiatBagToBedrockBag FiatEmpty. *)
End BagOfTuples0TupleCompilationParams.

Module BagOfTuples0Compilation
       (Params: BagOfTuples0ADTSpecParams)
       (CompilationParams: BagOfTuples0TupleCompilationParams Params).
  Module Import Specs := (BagOfTuples0ADTSpec Params).
  Export CompilationParams.

  (* FIXME Hint Resolve doesn't work: Why? *)
  Hint Extern 1 (_ = _) => simple apply FiatBagToBedrockBag_inj : inj_db.
  Hint Extern 1 (_ = _) => simple eapply TreeConstructor_inj : inj_db.

  Instance FiatWrapper {N} : FacadeWrapper ADTValue (FiatBag N).
  Proof.
    refine {| wrap tp := TreeConstructor N (FiatBagToBedrockBag tp);
              wrap_inj := _ |}; eauto with inj_db.
  Defined.

  Lemma CompileNew_helper :
    forall vret vsize fpointer (env: Env ADTValue) ext tenv N,
      GLabelMap.find fpointer env = Some (Axiomatic New) ->
      Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
      Lifted_not_mapsto_adt ext (tenv: Telescope ADTValue) vret ->
      vret ∉ ext ->
      ~ Word.wlt (Word.natToWord 32 N) (Word.natToWord 32 2) ->
      {{ tenv }}
        Call vret fpointer (vsize :: nil)
      {{ [[ `vret ->> TreeConstructor N Empty as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
    facade_eauto.
    facade_eauto.
  Qed.
End BagOfTuples0Compilation.

Module WBagOfTuples0TupleCompilationParams <: BagOfTuples0TupleCompilationParams (WBagOfTuples0ADTSpecParams).
  Definition FiatBag N := FiatWBag N.
  Definition FiatBagToBedrockBag {N} (bag: FiatBag N) :=
    IndexedEnsemble_TupleToListW bag.
  Lemma FiatBagToBedrockBag_inj :
    forall {N}, Injective (@FiatBagToBedrockBag N).
  Proof.
    red; intros;
    apply IndexedEnsemble_TupleToListW_inj; assumption.
  Qed.
End WBagOfTuples0TupleCompilationParams.

Module WBagOfTuples0Compilation.
  Include (BagOfTuples0Compilation WBagOfTuples0ADTSpecParams WBagOfTuples0TupleCompilationParams).

  Lemma TelEq_chomp_head_heterogeneous :
    forall {av A B} {WA: FacadeWrapper (Value av) A} {WB: FacadeWrapper (Value av) B}
      k (a: A) (b: B) (tenv tenv': Telescope av) ext,
      wrap a = wrap b ->
      TelEq ext tenv tenv' ->
      TelEq ext ([[ ` k ->> a as _]] :: tenv) ([[ ` k ->> b as _]] :: tenv).
  Proof.
    intros.
    unfold TelEq; SameValues_Fiat_t.
  Qed.

  Lemma CompileNew :
    forall vret vsize fpointer (env: Env ADTValue) ext tenv N,
      GLabelMap.find fpointer env = Some (Axiomatic WBagOfTuples0ADTSpec.New) ->
      Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
      Lifted_not_mapsto_adt ext (tenv: Telescope ADTValue) vret ->
      vret ∉ ext ->
      ~ Word.wlt (Word.natToWord 32 N) (Word.natToWord 32 2) ->
      {{ tenv }}
        Call vret fpointer (vsize :: nil)
      {{ [[ `vret ->> FiatWBagEmpty N as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
  Proof.
    intros.
    apply generalized CompileNew_helper; try eassumption.
    eapply TelEq_chomp_head_heterogeneous;
      repeat unfold wrap, WrapInstance, FiatWrapper, FacadeWrapper_Self, WBagOfTuples0ADTSpecParams.FieldType;
      try erewrite Empty_lift;
      reflexivity.
  Qed.

  (* Lemma CompileInsert : *)
  (*   forall vret vtable vtuple fpointer (env: Env ADTValue) ext tenv N idx *)
  (*     (table: FiatWBag N) (tuple: FiatWTuple N), *)
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
  (*     {{ [[ `vret ->> SCAZero as _ ]] *)
  (*          :: [[ `vtable ->> table as _ ]] *)
  (*          :: DropName vtable (DropName vret (DropName vtuple tenv)) }} ∪ {{ ext }} // env. *)
  (* Proof. *)
  (*   repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t). *)

  (* Definition FiatWBagFunctional {N} (fiatBag: FiatWBag N) := *)
  (*   forall t1 t2, *)
  (*     fiatBag t1 -> fiatBag t2 -> *)
  (*     IndexedEnsembles.elementIndex t1 = IndexedEnsembles.elementIndex t2 -> *)
  (*     t1 = t2. *)

  (* Definition FiatWBagMinFreshIndex {N} (fiatBag: FiatWBag N) idx := *)
  (*   IndexedEnsembles.UnConstrFreshIdx fiatBag idx /\ *)
  (*   (forall idx' : nat, (lt idx' idx) -> ~ IndexedEnsembles.UnConstrFreshIdx fiatBag idx'). *)

  (* Record FiatWBag' {N} := *)
  (*   { fiatBag : FiatWBag N; *)
  (*     bagFunctional : FiatWBagFunctional fiatBag; *)
  (*     idx: nat; *)
  (*     idxIsFresh: FiatWBagMinFreshIndex fiatBag idx }. *)

  (* Lemma minFreshIndex_Lift: *)
  (*   forall (N : nat) (table : FiatWBag N) (idx : nat), *)
  (*     FiatWBagMinFreshIndex table idx -> *)
  (*     minFreshIndex (IndexedEnsemble_TupleToListW table) idx. *)
  (* Proof. *)
  (*   unfold FiatWBagMinFreshIndex, minFreshIndex. *)
  (*   repeat cleanup. *)

  (*   Lemma UnconstrFreshIdx_Lift: *)
  (*     forall (N : nat) (table : FiatWBag N) (idx : nat), *)
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

  (* Lemma CompileInumerate : *)
  (*   forall vret vtable fpointer (env: Env ADTValue) ext tenv N *)
  (*     (table: FiatWBag N) (tuple: FiatWTuple N), *)
  (*     GLabelMap.find fpointer env = Some (Axiomatic Tuples0_enumerate) -> *)
  (*     Lifted_MapsTo ext tenv vtable (wrap table) -> *)
  (*     Lifted_not_mapsto_adt ext tenv vret -> *)
  (*     NoDuplicates [[[vret; vtable]]] -> *)
  (*     vret ∉ ext -> *)
  (*     BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) -> *)
  (*     {{ tenv }} *)
  (*       Call vret fpointer (vtable :: nil) *)
  (*     {{ [[ `vret ->> @nil (FiatWTuple N) as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env. *)
  (* Proof. *)
  (*   repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t). *)
  (*   facade_eauto. *)
  (*   admit.                      (* FIXME *) *)
  (*   rewrite <- remove_add_comm by congruence. *)
  (*   rewrite <- add_redundant_cancel by eassumption. *)
  (*   facade_eauto. *)
  (* Qed. *)
End WBagOfTuples0Compilation.