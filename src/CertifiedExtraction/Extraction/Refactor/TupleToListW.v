(* Require Import Fiat.Examples.QueryStructure.ProcessScheduler. *)
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
(* Require Import Fiat.Common.i3list. *)
Require Import Fiat.ADT.Core.

(* Require Import CertifiedExtraction.Core. *)

(* Require Import Bedrock.Platform.Facade.examples.QsADTs. *)
Require Import Bedrock.Platform.Facade.examples.TuplesF.
Require Import CertifiedExtraction.Utils.
Require Import Bedrock.Memory.

Notation BedrockElement := (@TuplesF.IndexedElement (list W)).
Notation BedrockBag := (@TuplesF.IndexedEnsemble (list W)).

Fixpoint MakeVectorOfW N : Vector.t Type N :=
  match N with
  | O => Vector.nil Type
  | S x => Vector.cons Type W x (MakeVectorOfW x)
  end.

Definition MakeWordHeading (N: nat) :=
  {| NumAttr := N;
     AttrList := MakeVectorOfW N |}.

Notation FiatTuple N := (@RawTuple (MakeWordHeading N)).
Notation FiatElement N := (@IndexedEnsembles.IndexedElement (FiatTuple N)).
Notation FiatBag N := (@IndexedEnsembles.IndexedEnsemble (FiatTuple N)).

Fixpoint ilist2ToListW {N} {struct N} : ilist2.ilist2 (B := fun x => x) (MakeVectorOfW N) -> list W :=
  match N as N0 return (@ilist2.ilist2 Type (fun x : Type => x) N0 (MakeVectorOfW N0) -> list W) with
  | 0 => fun _ => nil
  | S x => fun il => ilist2.ilist2_hd il :: ilist2ToListW (ilist2.ilist2_tl il)
  end.

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

Fixpoint TruncateList {A} (a: A) n l :=
  match n, l with
  | 0, _ => nil
  | S n, nil => a :: TruncateList a n nil
  | S n, h :: t => h :: TruncateList a n t
  end.

Lemma TruncateList_length {A} n :
  forall (a: A) (l: list A),
    List.length (TruncateList a n l) = n.
Proof.
  induction n, l; simpl; intuition.
Defined.

Lemma TruncateList_id {A} :
  forall (a: A) (l: list A),
    TruncateList a (List.length l) l = l.
Proof.
  induction l; simpl; auto using f_equal.
Qed.

Require Import Fiat.ADT.Core.

Definition ListWToTuple_Truncated n l : FiatTuple n :=
  @eq_rect nat _ (fun n => FiatTuple n)
           (ListWToTuple (TruncateList (Word.natToWord 32 0) n l))
           n (TruncateList_length n _ _).

Definition ListWToTuple_Truncated' n (l: list W) : FiatTuple n :=
  match (TruncateList_length n (Word.natToWord 32 0) l) in _ = n0 return FiatTuple n0 with
  | eq_refl => (ListWToTuple (TruncateList (Word.natToWord 32 0) n l))
  end.

Lemma ListWToTuple_Truncated_id n l :
  List.length l = n ->
  l = TupleToListW (ListWToTuple_Truncated' n l).
Proof.
  intros; subst.
  unfold ListWToTuple_Truncated'.
  induction l.
  trivial.
  simpl.

  destruct (TruncateList_length (Datatypes.length l) (Word.natToWord 32 0) l).
  rewrite IHl at 1.
  reflexivity.
Qed.

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

Lemma TupleToListW_length':
  forall (N : nat) (tuple : FiatTuple N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    Datatypes.length (TupleToListW tuple) = N.
Proof.
  cleanup;
  erewrite <- Word.wordToNat_natToWord_idempotent;
  eauto using TupleToListW_length.
Qed.

