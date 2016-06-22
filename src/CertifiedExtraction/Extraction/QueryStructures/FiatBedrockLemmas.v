Require Import CertifiedExtraction.Extraction.QueryStructures.Basics.
Require Import CertifiedExtraction.Extraction.QueryStructures.BinNatUtils.
Require Import CertifiedExtraction.Extraction.QueryStructures.TupleToListW.
Require Import CertifiedExtraction.Extraction.QueryStructures.EnsemblesOfTuplesAndListW.

Require Import
        Fiat.QueryStructure.Specification.Representation.Tuple
        Bedrock.Memory
        Coq.Lists.List.

Require Import CertifiedExtraction.Utils.

Opaque BinNat.N.of_nat.
Lemma nth_error_GetAttributeRaw:
  forall {N} (tup: @RawTuple (MakeWordHeading N)) (idx: Fin.t N),
    let n := (projT1 (Fin.to_nat idx)) in
    BinNat.N.lt (BinNat.N.of_nat n) (Word.Npow2 32) ->
    let k1 := Word.natToWord 32 n in
    nth_error (TupleToListW tup) (Word.wordToNat k1) =
    @Some W match MakeWordHeading_allWords idx with
            | eq_refl => (GetAttributeRaw tup idx)
            end.
Proof.
  induction idx; simpl in *.
  - reflexivity.
  - destruct (Fin.to_nat idx).
    unfold TupleToListW in *; simpl in *; apply lt_BinNat_lt in l.
    intros.
    rewrite Word.wordToNat_natToWord_idempotent in *
      by auto using BinNat_lt_of_nat_S.
    simpl; rewrite IHidx by auto using BinNat_lt_of_nat_S; reflexivity.
Qed.
Transparent BinNat.N.of_nat.

Lemma Same_set_pointwise :
  forall A s1 s2,
    Ensembles.Same_set A s1 s2 <-> (forall x, s1 x <-> s2 x).
Proof.
  firstorder.
Qed.

Lemma minFresh_UnConstrFresh :
  forall n table idx,
    TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW (N := n) table) idx ->
    IndexedEnsembles.UnConstrFreshIdx table idx.
Proof.
  unfold TuplesF.minFreshIndex, IndexedEnsembles.UnConstrFreshIdx; intros.
  intuition.
  unfold TuplesF.UnConstrFreshIdx in *.
  assert (IndexedEnsemble_TupleToListW table
                                       {| TuplesF.elementIndex := IndexedEnsembles.elementIndex element;
                                          TuplesF.indexedElement := TupleToListW (IndexedEnsembles.indexedElement element)
                                       |}).
  unfold IndexedEnsemble_TupleToListW; intros; eexists; split; eauto.
  unfold RelatedIndexedTupleAndListW; simpl; intuition.
  apply H1 in H; eauto.
Qed.

Lemma minFreshIndex_unique:
  forall {table : BedrockWBag} {x y : nat},
    TuplesF.minFreshIndex table x ->
    TuplesF.minFreshIndex table y ->
    x = y.
Proof.
  intros ** [x_ok x_minimal] [y_ok y_minimal].
  specialize (x_minimal y).
  specialize (y_minimal x).
  destruct (Compare_dec.lt_eq_lt_dec x y) as [ [ ? | ? ] | ? ]; intuition.
Qed.


Lemma Ensembles_Union_Or:
  forall {A} s1 s2 x,
    @Ensembles.Union A s1 s2 x <-> s1 x \/ s2 x.
Proof.
  split; intros ** H.
  inversion H; firstorder.
  destruct H; [ apply Ensembles.Union_introl | apply Ensembles.Union_intror ]; firstorder.
Qed.

Lemma Ensembles_Singleton_Eq:
  forall {A} x x',
    @Ensembles.Singleton A x x' <-> x = x'.
Proof.
  split; intros ** H; inversion H; firstorder.
Qed.

Lemma Fiat_Bedrock_Filters_Equivalence:
  forall (N : nat) (table : FiatWBag N) (key : W) (x9 : list TuplesF.tupl)
         (idx1: Fin.t N)
         (k1 := (Word.natToWord 32 (projT1 (Fin.to_nat idx1)))),
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    TuplesF.EnsembleIndexedListEquivalence (TuplesF.keepEq eq (Word.wzero _) (IndexedEnsemble_TupleToListW table) k1 key) x9 ->
    IndexedEnsembles.EnsembleIndexedListEquivalence
      (IndexedEnsembles.IndexedEnsemble_Intersection
         table
         (fun x0 : FiatWTuple N =>
            ((if Word.weq match MakeWordHeading_allWords idx1 in _ = W return W with
                          | eq_refl => GetAttributeRaw x0 idx1
                          end key then true else false) && true)%bool = true))
      (map (ListWToTuple_Truncated N) x9).
Proof.
  intros.
  apply EnsembleIndexedListEquivalence_TupleToListW.
  erewrite <- ListWToTuple_Truncated_map_keepEq by eassumption.

  rewrite TuplesF_EnsembleIndexedListEquivalence_EquivEnsembles; try eassumption.

  unfold IndexedEnsemble_TupleToListW, TuplesF.keepEq, Ensembles.Included,
  Ensembles.In, IndexedEnsembles.IndexedEnsemble_Intersection, Array.sel in *.

  rewrite Same_set_pointwise;
    repeat match goal with
           | _ => cleanup
           | _ => eassumption
           | _ => progress unfold RelatedIndexedTupleAndListW, TuplesF.tupl in *
           | [  |- exists _, _ ] => eexists
           | [ H: exists _, _ |- _ ] => destruct H
           | [  |- context[andb _ true] ] => rewrite Bool.andb_true_r
           | [ H: context[andb _ true] |- _ ] => rewrite Bool.andb_true_r in H
           | [ H: (if ?cond then true else false) = _ |- _ ] => destruct cond; try discriminate; [idtac]
           end.

  - setoid_rewrite H4.
    set (IndexedEnsembles.indexedElement x0).

    clear H0.

    unfold k1.
    rewrite nth_error_GetAttributeRaw; eauto using BinNat.N.lt_trans, BinNat_lt_Fin_to_nat.
  - unfold W, k1 in *; rewrite H3.
    unfold k1 in *; rewrite nth_error_GetAttributeRaw
      by eauto using BinNat.N.lt_trans, BinNat_lt_Fin_to_nat; simpl.
    destruct (Word.weq _ _); (reflexivity || exfalso; eauto).
Qed.

Lemma Fiat_Bedrock_Insert:
  forall (N : nat) (table : FiatWBag N) (tuple : FiatWTuple N) (x : nat),
    Ensembles.Same_set TuplesF.IndexedElement
                       (TuplesF.insertAt (IndexedEnsemble_TupleToListW table) x (TupleToListW tuple))
                       (IndexedEnsemble_TupleToListW
                          (Ensembles.Add (FiatWElement N) table
                                         {| IndexedEnsembles.elementIndex := x; IndexedEnsembles.indexedElement := tuple |})).
Proof.
  intros; rewrite Same_set_pointwise.

  unfold IndexedEnsemble_TupleToListW, TuplesF.insertAt, TuplesF.EnsembleInsert, Ensembles.Add.
  setoid_rewrite Ensembles_Union_Or.
  setoid_rewrite Ensembles_Singleton_Eq.

  unfold RelatedIndexedTupleAndListW.
  repeat match goal with
         | _ => cleanup
         | _ => eassumption
         | [ H: _ \/ _ |- _ ] => destruct H
         | [ H: exists _, _ |- _ ] => destruct H
         | _ => solve [eauto]
                      (* | [  |- exists _, _ ] => solve [eexists; firstorder] *)
         end.

  simpl in *; subst.
  destruct x0; simpl in *; subst; eauto.
Qed.

