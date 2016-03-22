Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import CertifiedExtraction.Core.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.TuplesF.

Require Import CertifiedExtraction.Utils.

Require Import Bedrock.Memory.

Fixpoint MakeVectorOfW N : Vector.t Type N :=
  match N with
  | O => Vector.nil Type
  | S x => Vector.cons Type W x (MakeVectorOfW x)
  end.

Definition MakeWordHeading (N: nat) :=
  {| NumAttr := N;
     AttrList := MakeVectorOfW N |}.

Fixpoint ilist2ToListW {N} {struct N} : ilist2.ilist2 (B := fun x => x) (MakeVectorOfW N) -> list W :=
  match N as N0 return (@ilist2.ilist2 Type (fun x : Type => x) N0 (MakeVectorOfW N0) -> list W) with
  | 0 => fun _ => nil
  | S x => fun il => ilist2.ilist2_hd il :: ilist2ToListW (ilist2.ilist2_tl il)
  end.

Notation BedrockElement := (@TuplesF.IndexedElement (list W)).
Notation BedrockBag := (@TuplesF.IndexedEnsemble (list W)).

Notation FiatTuple N := (@RawTuple (MakeWordHeading N)).
Notation FiatElement N := (@IndexedEnsembles.IndexedElement (FiatTuple N)).
Notation FiatBag N := (@IndexedEnsembles.IndexedEnsemble (FiatTuple N)).

Definition TupleToListW {N} (tuple: @RawTuple (MakeWordHeading N)) :=
  ilist2ToListW tuple.

Definition IndexedElement_TupleToListW {N} (element: FiatElement N) : BedrockElement :=
  {| elementIndex := element.(IndexedEnsembles.elementIndex);
     indexedElement := TupleToListW element.(IndexedEnsembles.indexedElement) |}.

Fixpoint ListWToilist2 (l : list W) : ilist2.ilist2 (B := fun x => x) (MakeVectorOfW (List.length l)) :=
  match l as l0 return (ilist2.ilist2 (MakeVectorOfW (Datatypes.length l0))) with
  | nil => ilist2.inil2
  | x :: x0 => ilist2.icons2 x (ListWToilist2 x0)
  end.

Definition ListWToTuple (l: list W) : @RawTuple (MakeWordHeading (List.length l)) :=
  ListWToilist2 l.

Definition IndexedElement_ListWToTuple (element: @IndexedElement (list W)) : FiatElement (List.length (indexedElement element)) :=
  {| IndexedEnsembles.elementIndex := element.(elementIndex);
     IndexedEnsembles.indexedElement := ListWToTuple element.(indexedElement) |}.

Lemma IndexedElement_RoundTrip :
  forall l, IndexedElement_TupleToListW (IndexedElement_ListWToTuple l) = l.
Proof.
  destruct l.
  induction indexedElement; simpl.
  - reflexivity.
  - unfold IndexedElement_ListWToTuple, IndexedElement_TupleToListW in *. simpl in *.
    f_equal. inversion IHindexedElement. rewrite H0. unfold TupleToListW in *.
    simpl. f_equal. compute in *. rewrite H0. reflexivity.
Qed.

Definition RelatedIndexedTupleAndListW {N} (l: BedrockElement) (tup: FiatElement N) :=
  l.(elementIndex) = tup.(IndexedEnsembles.elementIndex) /\
  l.(indexedElement) = TupleToListW tup.(IndexedEnsembles.indexedElement).

Definition IndexedEnsemble_TupleToListW {N} (ensemble: FiatBag N) : BedrockBag :=
  fun listW => exists tup, ensemble tup /\ RelatedIndexedTupleAndListW listW tup.

Lemma TupleToListW_inj {N}:
  forall (t1 t2: @RawTuple (MakeWordHeading N)),
    TupleToListW t1 = TupleToListW t2 ->
    t1 = t2.
Proof.
  induction N; simpl; destruct t1, t2; simpl; intros.
  - reflexivity.
  - inversion H; f_equal; eauto.
Qed.

Hint Resolve TupleToListW_inj : inj_db.

Ltac Wrapper_t :=
  abstract (intros * H; inversion H; subst; clear H; f_equal;
            eauto with inj_db).

Instance QS_WrapTuple {N} : FacadeWrapper ADTValue (@RawTuple (MakeWordHeading N)).
Proof.
  refine {| wrap tp := Tuple (TupleToListW tp);
            wrap_inj := _ |}; Wrapper_t.
Defined.

Lemma map_TupleToListW_inj {N}:
  forall (t1 t2: list (@RawTuple (MakeWordHeading N))),
    map TupleToListW t1 = map TupleToListW t2 ->
    t1 = t2.
Proof.
  induction t1; simpl; destruct t2; simpl; intros; try discriminate.
  - reflexivity.
  - inversion H; f_equal; eauto with inj_db.
Qed.

Hint Resolve map_TupleToListW_inj : inj_db.

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

Lemma lift_eq {A} (f g: A -> Prop) :
  f = g -> (forall x, f x <-> g x).
Proof.
  intros; subst; reflexivity.
Qed.

Lemma IndexedElement_TupleToListW_inj :
  forall {N} (e1 e2: FiatElement N),
    IndexedElement_TupleToListW e1 = IndexedElement_TupleToListW e2 ->
    e1 = e2.
Proof.
  unfold IndexedElement_TupleToListW; destruct e1, e2; simpl; intros * H; inversion H; subst; clear H; f_equal.
  apply TupleToListW_inj; eauto.
Qed.

Lemma IndexedEnsemble_TupleToListW_inj_helper:
  forall (N : nat) (e : FiatBag N) (x : FiatElement N),
    (IndexedEnsemble_TupleToListW e (IndexedElement_TupleToListW (N := N) x)) <-> e x.
Proof.
  unfold IndexedEnsemble_TupleToListW, RelatedIndexedTupleAndListW;
  repeat match goal with
         | _ => cleanup
         | _ => eassumption
         | _ => progress subst
         | [ x: FiatElement _ |- _ ] => destruct x
         | [ H: TupleToListW _ = TupleToListW _ |- _ ] => apply TupleToListW_inj in H
         | _ => eexists
         | _ => simpl in *
         end.
Qed.

Lemma IndexedEnsemble_TupleToListW_inj :
  forall {N} (e1 e2: FiatBag N),
    IndexedEnsemble_TupleToListW e1 = IndexedEnsemble_TupleToListW e2 ->
    e1 = e2.
Proof.
  intros * H; pose proof (lift_eq H); clear H.
  apply Ensembles.Extensionality_Ensembles; unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In.
  repeat cleanup; repeat match goal with
                         | [ H: forall _, _ |- _ ?x ] => specialize (H (IndexedElement_TupleToListW x)); cbv beta in H
                         | [ H: _ |- _ ] => setoid_rewrite IndexedEnsemble_TupleToListW_inj_helper in H
                         end; tauto.
Qed.

Hint Resolve IndexedEnsemble_TupleToListW_inj : inj_db.

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

Definition FiatEmpty N : FiatBag N := fun _ => False.

Lemma Empty_lift:
  forall N : nat,
    Empty = IndexedEnsemble_TupleToListW (FiatEmpty N).
Proof.
  intros; apply Ensembles.Extensionality_Ensembles.
  unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In, FiatEmpty, Empty, IndexedEnsemble_TupleToListW; split; intros.
  - exfalso; assumption.
  - repeat cleanup.
Qed.

Hint Resolve Empty_lift : call_helpers_db.

Ltac _PreconditionSet_t_in H :=
  cbv beta iota zeta delta [PreconditionSet PreconditionSet NoDuplicates NoDuplicates_helper] in H; destruct_ands H.

Ltac _PreconditionSet_t :=
  cbv beta iota zeta delta [PreconditionSet PreconditionSet_helper NoDuplicates NoDuplicates_helper];
  repeat match goal with
         | |- _ /\ _ => split
         end.

Ltac PreconditionSet_t ::=
     repeat
     match goal with
     | [ H: PreconditionSet _ _ _ |- _ ] => _PreconditionSet_t_in H
     | [ H: PreconditionSet_helper _ _ _ |- _ ] => _PreconditionSet_t_in H
     | [ H: NoDuplicates _ |- _ ] => _PreconditionSet_t_in H
     | [ H: NoDuplicates_helper _ _ |- _ ] => _PreconditionSet_t_in H
     | [  |- PreconditionSet _ _ _ ] => _PreconditionSet_t
     | [  |- PreconditionSet_helper _ _ _ ] => _PreconditionSet_t
     | [  |- NoDuplicates _ ] => _PreconditionSet_t
     | [  |- NoDuplicates_helper _ _ ] => _PreconditionSet_t
     end.

Lemma TupleToListW_length:
  forall (N : nat) (tuple : FiatTuple N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    Datatypes.length (TupleToListW tuple) = Word.wordToNat (Word.natToWord 32 N).
Proof.
  intros; rewrite Word.wordToNat_natToWord_idempotent by assumption.
  clear H.
  induction N; intros.
  - destruct tuple; reflexivity.
  - simpl; f_equal; apply IHN.
Qed.

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