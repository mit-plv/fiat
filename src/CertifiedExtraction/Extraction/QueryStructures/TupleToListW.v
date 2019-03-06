Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.ADT.Core.

Require Import Bedrock.Platform.Facade.examples.TuplesF.
Require Import CertifiedExtraction.Utils.
Require Import Bedrock.Memory.

Require Import CertifiedExtraction.Extraction.QueryStructures.Basics.

(** [TupleToListW] *)

Fixpoint ilist2ToListW {N} {struct N} : ilist2.ilist2 (B := fun x => x) (MakeVectorOfW N) -> list W :=
  match N as N0 return (@ilist2.ilist2 Type (fun x : Type => x) N0 (MakeVectorOfW N0) -> list W) with
  | 0 => fun _ => nil
  | S x => fun il => ilist2.ilist2_hd il :: ilist2ToListW (ilist2.ilist2_tl il)
  end.

Lemma ilist2ToListW_inj :
  forall n el el',
    ilist2ToListW (N := n) el = ilist2ToListW el'
    -> el = el'.
Proof.
  induction n; simpl; eauto.
  - destruct el; destruct el'; reflexivity.
  - destruct el; destruct el'; simpl; intros.
    unfold ilist2.ilist2_tl, ilist2.ilist2_hd in *; simpl in *.
    injections; f_equal.
    eapply IHn; eassumption.
Qed.

Definition TupleToListW {N} (tuple: @RawTuple (MakeWordHeading N)) :=
  ilist2ToListW tuple.

Definition IndexedElement_TupleToListW {N} (element: FiatWElement N) : BedrockWElement :=
  {| elementIndex := element.(IndexedEnsembles.elementIndex);
     indexedElement := TupleToListW element.(IndexedEnsembles.indexedElement) |}.

Fixpoint ListWToilist2 (l : list W) : ilist2.ilist2 (B := fun x => x) (MakeVectorOfW (List.length l)) :=
  match l as l0 return (ilist2.ilist2 (MakeVectorOfW (Datatypes.length l0))) with
  | nil => ilist2.inil2
  | x :: x0 => ilist2.icons2 x (ListWToilist2 x0)
  end.

Definition RelatedIndexedTupleAndListW {N} (l: BedrockWElement) (tup: FiatWElement N) :=
  l.(elementIndex) = tup.(IndexedEnsembles.elementIndex) /\
  l.(indexedElement) = TupleToListW tup.(IndexedEnsembles.indexedElement).

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

Lemma IndexedElement_TupleToListW_inj :
  forall {N} (e1 e2: FiatWElement N),
    IndexedElement_TupleToListW e1 = IndexedElement_TupleToListW e2 ->
    e1 = e2.
Proof.
  unfold IndexedElement_TupleToListW; destruct e1, e2; simpl; intros * H; inversion H; subst; clear H; f_equal.
  apply TupleToListW_inj; eauto.
Qed.

Lemma TupleToListW_length:
  forall (N : nat) (tuple : FiatWTuple N),
    Datatypes.length (TupleToListW tuple) = N.
Proof.
  induction N; intros.
  - destruct tuple; reflexivity.
  - simpl; f_equal; apply IHN.
Qed.

Lemma TupleToListW_length':
  forall (N : nat) (tuple : FiatWTuple N),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    Datatypes.length (TupleToListW tuple) = Word.wordToNat (Word.natToWord 32 N).
Proof.
  intros; rewrite Word.wordToNat_natToWord_idempotent by assumption.
  auto using TupleToListW_length.
Qed.

Definition TupleToListW_indexed {N} (tup: FiatWElement N) :=
  {| TuplesF.elementIndex := IndexedEnsembles.elementIndex tup;
     TuplesF.indexedElement := (TupleToListW (IndexedEnsembles.indexedElement tup)) |}.

Lemma RelatedIndexedTupleAndListW_refl :
  forall {N} tup,
    @RelatedIndexedTupleAndListW N (TupleToListW_indexed tup) tup.
Proof.
  cleanup; red; intuition.
Qed.

Lemma TupleToListW_indexed_inj {N}:
  forall (t1 t2: FiatWElement N),
    TupleToListW_indexed t1 = TupleToListW_indexed t2 ->
    t1 = t2.
Proof.
  destruct t1, t2; unfold TupleToListW_indexed; simpl.
  intro eq; inversion eq; subst; clear eq.
  f_equal; intuition.
Qed.

(** [ListWToTuple] *)

Definition ListWToTuple (l: list W) : @RawTuple (MakeWordHeading (List.length l)) :=
  ListWToilist2 l.

Definition IndexedElement_ListWToTuple (element: @IndexedElement (list W)) : FiatWElement (List.length (indexedElement element)) :=
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

Definition ListWToTuple_Truncated n l : FiatWTuple n :=
  @eq_rect nat _ (fun n => FiatWTuple n)
           (ListWToTuple (TruncateList (Word.natToWord 32 0) n l))
           n (TruncateList_length n _ _).

Definition ListWToTuple_Truncated' n (l: list W) : FiatWTuple n :=
  match (TruncateList_length n (Word.natToWord 32 0) l) in _ = n0 return FiatWTuple n0 with
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

