Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import CertifiedExtraction.Core.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.TuplesF.

(* Inductive ADTValue := *)
(* | Tuple (t : tupl) *)
(* | List (ts : list tupl) *)
(* | Tuples0 (len : W) (ts : tuples) *)
(* | Tuples1 (len key : W) (ts : tuples). *)

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

(* Fixpoint ListWToilist2 (l : list W) : ilist2.ilist2 (B := fun x => x) (MakeVectorOfW (List.length l)) := *)
(*   match l as l0 return (ilist2.ilist2 (MakeVectorOfW (Datatypes.length l0))) with *)
(*   | nil => ilist2.inil2 *)
(*   | x :: x0 => ilist2.icons2 x (ListWToilist2 x0) *)
(*   end. *)

(* Definition ListWToTuple (l: list W) : @RawTuple (MakeWordHeading (List.length l)) := *)
(*   ListWToilist2 l. *)

(* Definition IndexedElement_ListWToTuple (element: @IndexedElement (list W)) := *)
(*   {| elementIndex := element.(elementIndex); *)
(*      indexedElement := ListWToTuple element.(indexedElement) |}. *)

Definition RelatedIndexedTupleAndListW {N} (l: BedrockElement) (tup: FiatElement N) :=
  l.(elementIndex) = tup.(IndexedEnsembles.elementIndex) /\
  l.(indexedElement) = TupleToListW tup.(IndexedEnsembles.indexedElement).

Definition IndexedEnsemble_TupleToListW {N} (ensemble: FiatBag N) : BedrockBag :=
  fun listW => exists tup, ensemble tup /\ RelatedIndexedTupleAndListW listW tup.

(* Definition IndexedEnsemble_TupleToListW' {N} (ensemble: FiatBag) *)
(*   : @IndexedEnsemble (list W) := *)
(*   fun listW => *)
(*     exists pr: List.length listW.(indexedElement) = N, *)
(*       ensemble match pr in _ = N with *)
(*                | eq_refl => IndexedElement_ListWToTuple listW *)
(*                end. *)

(* Definition IndexedEnsemble_TupleToListW' {N} (ensemble: FiatBag) *)
(*   : @IndexedEnsemble (list W). *)
(*       refine (fun listW => _). *)
(*       refine (match EqNat.beq_nat (List.length listW.(indexedElement)) N as b *)
(*                     return EqNat.beq_nat (List.length listW.(indexedElement)) N = b -> Prop with *)
(*                 | true => fun pr => ensemble match (EqNat.beq_nat_true _ _ pr) in _ = N with *)
(*                                         | eq_refl => IndexedElement_ListWToTuple listW *)
(*                                         end *)
(*                 | false => fun _ => False *)
(*               end eq_refl). *)
(* Defined. *)

(* Definition IndexedEnsemble_TupleToListW' {N} (ensemble: FiatBag) *)
(*   : @IndexedEnsemble (list W). *)
(*       refine (fun listW => _). *)
(*       refine (match Peano_dec.eq_nat_dec (List.length listW.(indexedElement)) N with *)
(*               | left pr => ensemble match pr in _ = N with *)
(*                                    | eq_refl => IndexedElement_ListWToTuple listW *)
(*                                    end *)
(*               | in_right => False *)
(*               end). *)
(* Defined. *)

(* Definition IndexedEnsemble_ListWToTuple {N} (ensemble : @IndexedEnsemble (list W)) *)
(*   : FiatBag := *)
(*   fun tup => exists listW, ensemble listW /\ RelatedIndexedTupleAndListW listW tup. *)

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

Instance QS_WrapTup {N} : FacadeWrapper ADTValue (@RawTuple (MakeWordHeading N)).
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

Instance QS_WrapList {N} : FacadeWrapper ADTValue (list (@RawTuple (MakeWordHeading N))).
Proof.
  refine {| wrap tl := List (List.map TupleToListW tl);
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

Require Import Bedrock.Platform.Facade.examples.QsADTs.

Print Tuple.
Print TuplesF.tupl.

Print TuplesF.tupl.

Require Import CertifiedExtraction.Extraction.External.Core.
Require Import Bedrock.Platform.Facade.examples.QsADTs.

Lemma CompileList_new :
  forall vret fpointer (env: Env ADTValue) ext tenv N,
    GLabelMap.find fpointer env = Some (Axiomatic List_new) ->
    vret ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vret ->
    {{ tenv }}
      Call vret fpointer nil
    {{ [[ `vret <-- @nil (FiatTuple N) as _ ]] :: DropName vret tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  change (ADT (List [])) with (wrap (FacadeWrapper := WrapInstance (H := @QS_WrapList N)) []).
  facade_eauto.
Qed.

Lemma CompileList_delete :
  forall vret vlst fpointer (env: Env ADTValue) ext tenv N,
    GLabelMap.find fpointer env = Some (Axiomatic List_delete) ->
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

Lemma CompileList_pop :
  forall vret vlst fpointer (env: Env ADTValue) ext tenv N
    h (t: list (FiatTuple N)),
    GLabelMap.find fpointer env = Some (Axiomatic List_pop) ->
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

Lemma CompileList_push :
  forall vret vhd vlst fpointer (env: Env ADTValue) ext tenv N
    h (t: list (FiatTuple N)),
    GLabelMap.find fpointer env = Some (Axiomatic List_push) ->
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

Lemma CompileTuple_new :
  forall vret varg fpointer w (env: Env ADTValue) ext tenv,
    Lifted_MapsTo ext tenv varg w ->
    {{ tenv }}
      Call vret fpointer (varg :: nil)
    {{ [[ vret <-- tuple as _ ]] :: DropName vret tenv }} ∪ {{ext}} // env.
Proof.

        (* {{ tenv }} *)
    (*   InitArgs *)
    (* {{ [[`varg <-- N]] :: tenv }} ∪ {{ ext }} // env -> *)
