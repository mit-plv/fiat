Set Implicit Arguments.

(* there is a name conflict on tactic 'unfolder' between GeneralTactics and MakeADT *)
Require Import Bedrock.Platform.Cito.GeneralTactics.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Import Adt.
Require Import Bedrock.Platform.Cito.WordMap.
Require Import Bedrock.Platform.Cito.RepInv Bedrock.Platform.Cito.MakeADT.

Require Import Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.ListSeqF Bedrock.Platform.Facade.examples.ArrayTupleF Bedrock.Platform.Facade.examples.TupleListF Bedrock.Platform.Facade.examples.Tuples0F Bedrock.Platform.Facade.examples.Tuples1F Bedrock.Platform.Facade.examples.Tuples2F Bedrock.Platform.Facade.examples.ByteString.
Require Import Bedrock.Platform.Facade.examples.QsRepInv.

Module Import Made := MakeADT.Make(QsADTs.Adt)(Ri).

Import Semantics.

Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.SemanticsMake.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake2.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.

Definition hints : TacPackage.
  prepare (store_pair_inl_fwd, store_pair_inr_fwd)
  (store_pair_inl_bwd, store_pair_inr_bwd).
Defined.

Arguments SCA {ADTValue} _.
Arguments ADT {ADTValue} _.

Require Bedrock.Platform.Cito.AxSpec.
Import AxSpec.ConformTactic.

Definition m0 := bimport [[ "sys"!"abort" @ [abortS],

                            "ArrayTuple"!"new" @ [ArrayTupleF.newS],
                            "ArrayTuple"!"delete" @ [ArrayTupleF.deleteS],
                            "ArrayTuple"!"copy" @ [ArrayTupleF.copyS],
                            "ArrayTuple"!"get" @ [ArrayTupleF.getS],
                            "ArrayTuple"!"set" @ [ArrayTupleF.setS],

                            "ListSeq"!"new" @ [ListSeqF.newS],
                            "ListSeq"!"delete" @ [ListSeqF.deleteS],
                            "ListSeq"!"pop" @ [ListSeqF.popS],
                            "ListSeq"!"empty" @ [ListSeqF.emptyS],
                            "ListSeq"!"push" @ [ListSeqF.pushS],
                            "ListSeq"!"copy" @ [ListSeqF.copyS],
                            "ListSeq"!"rev" @ [ListSeqF.revS],
                            "ListSeq"!"length" @ [ListSeqF.lengthS],

                            "TupleList"!"new" @ [TupleListF.newS],
                            "TupleList"!"delete" @ [TupleListF.deleteS],
                            "TupleList"!"pop" @ [TupleListF.popS],
                            "TupleList"!"empty" @ [TupleListF.emptyS],
                            "TupleList"!"push" @ [TupleListF.pushS],
                            "TupleList"!"copy" @ [TupleListF.copyS],
                            "TupleList"!"rev" @ [TupleListF.revS],
                            "TupleList"!"length" @ [TupleListF.lengthS],

                            "Tuples0"!"new" @ [Tuples0F.newS],
                            "Tuples0"!"insert" @ [Tuples0F.insertS],
                            "Tuples0"!"enumerate" @ [Tuples0F.enumerateS],

                            "Tuples1"!"new" @ [Tuples1F.newS],
                            "Tuples1"!"insert" @ [Tuples1F.insertS],
                            "Tuples1"!"find" @ [Tuples1F.findS],
                            "Tuples1"!"enumerate" @ [Tuples1F.enumerateS],

                            "Tuples2"!"new" @ [Tuples2F.newS],
                            "Tuples2"!"insert" @ [Tuples2F.insertS],
                            "Tuples2"!"findBoth" @ [Tuples2F.findBothS],
                            "Tuples2"!"findFirst" @ [Tuples2F.findFirstS],
                            "Tuples2"!"findSecond" @ [Tuples2F.findSecondS],
                            "Tuples2"!"enumerate" @ [Tuples2F.enumerateS],

                            "ByteString"!"new" @ [ByteString.newS],
                            "ByteString"!"delete" @ [ByteString.deleteS],
                            "ByteString"!"copy" @ [ByteString.copyS],
                            "ByteString"!"push" @ [ByteString.pushS],
                            "ByteString"!"put" @ [ByteString.putS],
                            "ByteString"!"get" @ [ByteString.getS] ]]
  fmodule "ADT" {{
    ffunction "Tuple_new" reserving 7 [WTupleADTSpec.New] := "ArrayTuple"!"new"
    with ffunction "Tuple_delete" reserving 6 [WTupleADTSpec.Delete] := "ArrayTuple"!"delete"
    with ffunction "Tuple_copy" reserving 11 [WTupleADTSpec.Copy] := "ArrayTuple"!"copy"
    with ffunction "Tuple_get" reserving 0 [WTupleADTSpec.Get] := "ArrayTuple"!"get"
    with ffunction "Tuple_set" reserving 0 [WTupleADTSpec.Put] := "ArrayTuple"!"set"

    with ffunction "WordList_new" reserving 8 [WordListADTSpec.New] := "ListSeq"!"new"
    with ffunction "WordList_delete" reserving 7 [WordListADTSpec.Delete] := "ListSeq"!"delete"
    with ffunction "WordList_pop" reserving 8 [WordListADTSpec.Pop] := "ListSeq"!"pop"
    with ffunction "WordList_empty" reserving 0 [WordListADTSpec.Empty] := "ListSeq"!"empty"
    with ffunction "WordList_push" reserving 8 [WordListADTSpec.Push] := "ListSeq"!"push"
    with ffunction "WordList_copy" reserving 10 [WordListADTSpec.Copy] := "ListSeq"!"copy"
    with ffunction "WordList_rev" reserving 2 [WordListADTSpec.Rev] := "ListSeq"!"rev"
    with ffunction "WordList_length" reserving 1 [WordListADTSpec.Length] := "ListSeq"!"length"

    with ffunction "TupleList_new" reserving 8 [WTupleListADTSpec.New] := "TupleList"!"new"
    with ffunction "TupleList_delete" reserving 6 [WTupleListADTSpec.Delete] := "TupleList"!"delete"
    with ffunction "TupleList_copy" reserving 18 [WTupleListADTSpec.Copy] := "TupleList"!"copy"
    with ffunction "TupleList_pop" reserving 8 [WTupleListADTSpec.Pop] := "TupleList"!"pop"
    with ffunction "TupleList_empty" reserving 0 [WTupleListADTSpec.Empty] := "TupleList"!"empty"
    with ffunction "TupleList_push" reserving 8 [WTupleListADTSpec.Push] := "TupleList"!"push"
    with ffunction "TupleList_rev" reserving 2 [WTupleListADTSpec.Rev] := "TupleList"!"rev"
    with ffunction "TupleList_length" reserving 1 [WTupleListADTSpec.Length] := "TupleList"!"length"

    with ffunction "Tuples0_new" reserving 11 [WBagOfTuples0ADTSpec.New] := "Tuples0"!"new"
    with ffunction "Tuples0_insert" reserving 12 [WBagOfTuples0ADTSpec.Insert] := "Tuples0"!"insert"
    with ffunction "Tuples0_enumerate" reserving 22 [WBagOfTuples0ADTSpec.Enumerate] := "Tuples0"!"enumerate"

    with ffunction "Tuples1_new" reserving 7 [WBagOfTuples1ADTSpec.New] := "Tuples1"!"new"
    with ffunction "Tuples1_insert" reserving 21 [WBagOfTuples1ADTSpec.Insert] := "Tuples1"!"insert"
    with ffunction "Tuples1_find" reserving 34 [WBagOfTuples1ADTSpec.Find] := "Tuples1"!"find"
    with ffunction "Tuples1_enumerate" reserving 34 [WBagOfTuples1ADTSpec.Enumerate] := "Tuples1"!"enumerate"

    with ffunction "Tuples2_new" reserving 7 [WBagOfTuples2ADTSpec.New] := "Tuples2"!"new"
    with ffunction "Tuples2_insert" reserving 31 [WBagOfTuples2ADTSpec.Insert] := "Tuples2"!"insert"
    with ffunction "Tuples2_findBoth" reserving 38 [WBagOfTuples2ADTSpec.FindBoth] := "Tuples2"!"findBoth"
    with ffunction "Tuples2_findFirst" reserving 37 [WBagOfTuples2ADTSpec.FindFirst] := "Tuples2"!"findFirst"
    with ffunction "Tuples2_findSecond" reserving 36 [WBagOfTuples2ADTSpec.FindSecond] := "Tuples2"!"findSecond"
    with ffunction "Tuples2_enumerate" reserving 36 [WBagOfTuples2ADTSpec.Enumerate] := "Tuples2"!"enumerate"

    with ffunction "ByteString_new" reserving 7 [BytesADTSpec.New] := "ByteString"!"new"
    with ffunction "ByteString_delete" reserving 6 [BytesADTSpec.Delete] := "ByteString"!"delete"
    with ffunction "ByteString_copy" reserving 13 [BytesADTSpec.Copy] := "ByteString"!"copy"
    with ffunction "ByteString_push" reserving 0 [BytesADTSpec.Push] := "ByteString"!"push"
    with ffunction "ByteString_put" reserving 0 [BytesADTSpec.Put] := "ByteString"!"put"
    with ffunction "ByteString_get" reserving 0 [BytesADTSpec.Get] := "ByteString"!"get"
  }}.

Ltac peel := repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.

Lemma is_heap_eat : forall w v,
  is_heap heap_empty
  ===> is_heap (WordMap.remove w (heap_upd heap_empty w v)).
Proof.
  intros; apply is_heap_Equal.
  apply Properties.F.Equal_mapsto_iff; intuition.
  apply Properties.F.empty_mapsto_iff in H; tauto.
  apply Properties.F.remove_mapsto_iff in H; intuition.
  apply Properties.F.add_mapsto_iff in H1; intuition.
Qed.

Lemma get_rval : forall specs st P Q (R : Prop) S T Z,
  (R -> interp specs (![P * Q * S * T] st ---> Z)%PropX)
  -> interp specs (![P * ((Q * [|R|]) * S) * T] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|R|] * (P * Q * S * T)]st)%PropX.
  assert (P * (Q * [|R|] * S) * T ===> [|R|] * (P * Q * S * T)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|R|] /\ ![P * Q * S * T]st)%PropX.
  rewrite sepFormula_eq.
  do 2 (apply existsL; intro).
  apply andL; apply injL; intro.
  apply andL.
  apply andL.
  apply injL; intro.
  apply injL; intro.
  apply split_semp in H0; auto; subst.
  apply andR.
  apply injR; auto.
  apply Imply_refl.
  apply andL.
  apply injL; auto.
Qed.

Lemma get_rval' : forall specs st P (Q : Prop) R S Z,
  (Q -> interp specs (![P * R * S ] st ---> Z)%PropX)
  -> interp specs (![P * ([|Q|] * R) * S] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S)]st)%PropX.
  assert (P * ([|Q|] * R) * S ===> [|Q|] * (P * R * S)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * R * S]st)%PropX.
  rewrite sepFormula_eq.
  do 2 (apply existsL; intro).
  apply andL; apply injL; intro.
  apply andL.
  apply andL.
  apply injL; intro.
  apply injL; intro.
  apply split_semp in H0; auto; subst.
  apply andR.
  apply injR; auto.
  apply Imply_refl.
  apply andL.
  apply injL; auto.
Qed.

Lemma contra2 : forall len len',
  (natToW len < $2 -> False)
  -> len' < natToW 2
  -> len = wordToNat len'
  -> False.
Proof.
  intros; subst.
  pre_nomega.
  unfold natToW in H.
  rewrite natToWord_wordToNat in H.
  change (wordToNat (natToW 2)) with 2 in *.
  change (wordToNat (natToWord 32 2)) with 2 in *.
  omega.
Qed.

Hint Immediate contra2.

Require Import Bedrock.Platform.Cito.SemanticsFacts5.
Require Import Bedrock.Platform.Cito.LayoutHintsUtil.

Lemma readd_Tuple : forall c rv rv',
  tuple rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (WTuple rv') (heap_upd heap_empty c (WTuple rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, WTuple rv') (heap_elements (WordMap.add c (WTuple rv') (heap_upd heap_empty c (WTuple rv))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma readd_TupleList : forall c rv rv',
  lseq rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (WTupleList rv') (heap_upd heap_empty c (WTupleList rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, WTupleList rv') (heap_elements (WordMap.add c (WTupleList rv') (heap_upd heap_empty c (WTupleList rv))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma readd_WordList : forall c rv rv',
  ListSeqF.Adt.lseq rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (WordList rv') (heap_upd heap_empty c (WordList rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, WordList rv') (heap_elements (WordMap.add c (WordList rv') (heap_upd heap_empty c (WordList rv))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma readd_Tuples0 : forall c len rv rv',
  tuples0 len rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (WBagOfTuples0 len rv') (heap_upd heap_empty c (WBagOfTuples0 len rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, WBagOfTuples0 len rv') (heap_elements (WordMap.add c (WBagOfTuples0 len rv') (heap_upd heap_empty c (WBagOfTuples0 len rv))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma readd_Tuples1 : forall c len key rv rv',
  tuples1 len key rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (WBagOfTuples1 len key rv') (heap_upd heap_empty c (WBagOfTuples1 len key rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, WBagOfTuples1 len key rv') (heap_elements (WordMap.add c (WBagOfTuples1 len key rv') (heap_upd heap_empty c (WBagOfTuples1 len key rv))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma readd_Tuples2 : forall c len key1 key2 rv rv',
  tuples2 len key1 key2 rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (WBagOfTuples2 len key1 key2 rv') (heap_upd heap_empty c (WBagOfTuples2 len key1 key2 rv))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, WBagOfTuples2 len key1 key2 rv') (heap_elements (WordMap.add c (WBagOfTuples2 len key1 key2 rv') (heap_upd heap_empty c (WBagOfTuples2 len key1 key2 rv))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Lemma get_rval'' : forall specs st P (Q : Prop) R S T Z,
  (Q -> interp specs (![P * R * S * T ] st ---> Z)%PropX)
  -> interp specs (![P * (([|Q|] * R) * S) * T] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S * T)]st)%PropX.
  assert (P * (([|Q|] * R) * S) * T===> [|Q|] * (P * R * S * T)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * R * S * T]st)%PropX.
  rewrite sepFormula_eq.
  do 2 (apply existsL; intro).
  apply andL; apply injL; intro.
  apply andL.
  apply andL.
  apply injL; intro.
  apply injL; intro.
  apply split_semp in H0; auto; subst.
  apply andR.
  apply injR; auto.
  apply Imply_refl.
  apply andL.
  apply injL; auto.
Qed.

Lemma readd_TupleList' : forall c rv rv' c' ov,
  c <> c'
  -> lseq rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (WTupleList rv')
            (WordMap.add c' ov
               (WordMap.add c (WTupleList rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, WTupleList rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Theorem insert_bounded : forall A ts idx t,
  TuplesF.minFreshIndex (A := A) ts idx
  -> TuplesF.insert ts t (TuplesF.insertAt ts idx t).
Proof.
  unfold TuplesF.insert, TuplesF.insertAt, TuplesF.UnConstrFreshIdx.
  destruct 1.
  exists idx.
  intuition.
Qed.

Hint Immediate insert_bounded.

Lemma really_zero : forall (st : state) (r : reg),
  Regs st r = $0
  -> SCA ((let (Regs, _) := st in Regs) r) = @SCAZero ADTValue.
Proof.
  intros.
  unfold SCAZero.
  f_equal.
  auto.
Qed.

Hint Immediate really_zero.

Lemma readd_Tuples0' : forall c rv rv' c' ov len,
  c <> c'
  -> tuples0 len rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (WBagOfTuples0 len rv')
            (WordMap.add c' ov
               (WordMap.add c (WBagOfTuples0 len rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, WBagOfTuples0 len rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Lemma readd_Tuples1' : forall c rv rv' c' ov len key,
  c <> c'
  -> tuples1 len key rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (WBagOfTuples1 len key rv')
            (WordMap.add c' ov
               (WordMap.add c (WBagOfTuples1 len key rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, WBagOfTuples1 len key rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Lemma readd_Tuples2' : forall c rv rv' c' ov len key1 key2,
  c <> c'
  -> tuples2 len key1 key2 rv' c * is_heap heap_empty
  ===> is_heap
      (WordMap.remove c'
         (WordMap.add c (WBagOfTuples2 len key1 key2 rv')
            (WordMap.add c' ov
               (WordMap.add c (WBagOfTuples2 len key1 key2 rv)
                  heap_empty)))).
Proof.
  intros.
  unfold is_heap at 2.
  match goal with
  | [ |- context[Bags.starL _ ?x] ] => assert (List.In (c, WBagOfTuples2 len key1 key2 rv') x)
  end.
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.remove_2; auto.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H0; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H0; intuition idtac.
  eapply Himp_trans; [ | apply H1 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H3 in H2; intuition.
  apply In_InA' in H5.
  apply WordMap.elements_2 in H5.
  apply Properties.F.remove_mapsto_iff in H5; intuition.
  apply Properties.F.add_mapsto_iff in H6; intuition.
  apply Properties.F.add_mapsto_iff in H7; intuition.
  apply Properties.F.add_mapsto_iff in H8; intuition.
  apply Properties.F.empty_mapsto_iff in H9; tauto.
Qed.

Lemma get_rval''' : forall specs st P (Q : Prop) R S Z,
  (Q -> interp specs (![P * R * S ] st ---> Z)%PropX)
  -> interp specs (![((P * [|Q|]) * R) * S] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S)]st)%PropX.
  assert (((P * [|Q|]) * R) * S ===> [|Q|] * (P * R * S)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * R * S]st)%PropX.
  rewrite sepFormula_eq.
  do 2 (apply existsL; intro).
  apply andL; apply injL; intro.
  apply andL.
  apply andL.
  apply injL; intro.
  apply injL; intro.
  apply split_semp in H0; auto; subst.
  apply andR.
  apply injR; auto.
  apply Imply_refl.
  apply andL.
  apply injL; auto.
Qed.

Lemma get_rval'''' : forall specs st P (Q : Prop) S Z,
  (Q -> interp specs (![P * S ] st ---> Z)%PropX)
  -> interp specs (![(P * [|Q|]) * S] st ---> Z)%PropX.
Proof.
  intros.
  apply Imply_trans with (![[|Q|] * (P * S)]st)%PropX.
  assert ((P * [|Q|])* S ===> [|Q|] * (P * S)).
  sepLemma.
  rewrite sepFormula_eq.
  apply H0.
  apply Imply_trans with ([|Q|] /\ ![P * S]st)%PropX.
  rewrite sepFormula_eq.
  do 2 (apply existsL; intro).
  apply andL; apply injL; intro.
  apply andL.
  apply andL.
  apply injL; intro.
  apply injL; intro.
  apply split_semp in H0; auto; subst.
  apply andR.
  apply injR; auto.
  apply Imply_refl.
  apply andL.
  apply injL; auto.
Qed.

Lemma readd_ByteString : forall c capacity bs capacity' bs',
  ByteString.bytes capacity' bs' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (ByteString capacity' bs') (heap_upd heap_empty c (ByteString capacity bs))).
Proof.
  intros.
  unfold is_heap at 2.
  assert (List.In (c, ByteString capacity' bs') (heap_elements (WordMap.add c (ByteString capacity' bs') (heap_upd heap_empty c (ByteString capacity bs))))).
  apply InA_In.
  apply WordMap.elements_1.
  apply WordMap.add_1.
  auto.
  eapply starL_in in H; try (apply NoDupA_NoDup; apply WordMap.elements_3w).
  destruct H; intuition idtac.
  eapply Himp_trans; [ | apply H0 ].
  simpl.
  apply Himp_star_frame; try apply Himp_refl.
  apply starL_permute; auto.
  apply NoDupA_NoDup; apply WordMap.elements_3w.
  intuition.
  apply H2 in H1; intuition.
  apply In_InA' in H4.
  apply WordMap.elements_2 in H4.
  apply Properties.F.add_mapsto_iff in H4; intuition.
  apply Properties.F.add_mapsto_iff in H5; intuition.
  apply Properties.F.empty_mapsto_iff in H6; tauto.
Qed.

Theorem ok0 : moduleOk m0.
Proof.
  vcgen.


  (* ArrayTuple *)

  (* new *)

  do_abort ("len" :: nil).
  do_abort ("len" :: nil).
  do_abort ("len" :: nil).

  do_delegate1 ("len" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval; intro.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: nil).

  (* delete *)

  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).

  do_delegate1 ("self" :: "len" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval'; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: "len" :: nil).

  (* copy *)

  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_delegate1 ("self" :: "len" :: nil) hints.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: "len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuple ] ].
  do_delegate2 ("self" :: "len" :: nil).

  (* get *)

  do_abort ("self" :: "pos" :: nil).
  do_abort ("self" :: "pos" :: nil).
  do_abort ("self" :: "pos" :: nil).

  do_delegate1 ("self" :: "pos" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "pos" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuple ] ].
  do_delegate2 ("self" :: "pos" :: nil).

  (* set *)

  do_abort ("self" :: "pos" :: "val" :: nil).
  do_abort ("self" :: "pos" :: "val" :: nil).
  do_abort ("self" :: "pos" :: "val" :: nil).

  do_delegate1 ("self" :: "pos" :: "val" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "pos" :: "val" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuple ] ].
  do_delegate2 ("self" :: "pos" :: "val" :: nil).


  (* WordList *)

  (* new *)

  do_abort (@nil string).
  do_abort (@nil string).
  do_abort (@nil string).

  do_delegate1 (@nil string) hints.
  do 2 (descend; step auto_ext).
  2: returnAdt.
  simpl.
  make_toArray (@nil string).
  step auto_ext.
  etransitivity; [ | apply himp_star_frame; [ apply (@is_state_in x4) | reflexivity ] ].
  unfolder.
  do_delegate2 (@nil string).

  (* delete *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval'; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* pop *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_WordList ] ].
  do_delegate2 ("self" :: nil).

  (* empty *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_WordList ] ].
  do_delegate2 ("self" :: nil).

  (* push *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  descend; step hints.
  simpl.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_WordList ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* copy *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_WordList ] ].
  do_delegate2 ("self" :: nil).

  (* rev *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  simpl.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_WordList ] ].
  do_delegate2 ("self" :: nil).

  (* length *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_WordList ] ].
  do_delegate2 ("self" :: nil).


  (* TupleList *)

  (* new *)

  do_abort (@nil string).
  do_abort (@nil string).
  do_abort (@nil string).

  do_delegate1 (@nil string) hints.
  do 2 (descend; step auto_ext).
  2: returnAdt.
  simpl.
  make_toArray (@nil string).
  step auto_ext.
  etransitivity; [ | apply himp_star_frame; [ apply (@is_state_in x4) | reflexivity ] ].
  unfolder.
  do_delegate2 (@nil string).

  (* delete *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step auto_ext.
  peel.
  apply get_rval'; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* copy *)

  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).
  do_abort ("self" :: "len" :: nil).

  do_delegate1 ("self" :: "len" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: "len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_TupleList ] ].
  do_delegate2 ("self" :: "len" :: nil).

  (* pop *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_TupleList ] ].
  do_delegate2 ("self" :: nil).

  (* empty *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval''; intro.
  step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_TupleList ] ].
  do_delegate2 ("self" :: nil).

  (* push *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  simpl.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_TupleList' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* rev *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  simpl.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_TupleList ] ].
  do_delegate2 ("self" :: nil).

  (* length *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  peel.
  apply get_rval''; intro.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_TupleList ] ].
  do_delegate2 ("self" :: nil).


  (* Tuples0 *)

  (* new *)

  do_abort ("len" :: nil).
  do_abort ("len" :: nil).
  do_abort ("len" :: nil).

  do_delegate1 ("len" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: nil).

  (* insert *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl; step hints.
  peel.
  apply get_rval''; intro.
  descend; step hints.
  descend; step hints.
  2: returnScalar; eauto 7.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples0' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* enumerate *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval'''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 7.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples0 ] ].
  do_delegate2 ("self" :: nil).


  (* Tuples1 *)

  (* new *)

  do_abort ("len" :: "key" :: nil).
  do_abort ("len" :: "key" :: nil).
  do_abort ("len" :: "key" :: nil).

  do_delegate1 ("len" :: "key" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: "key" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: "key" :: nil).

  (* insert *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl; step hints.
  peel.
  apply get_rval''; intro.
  descend; step hints.
  descend; step hints.
  2: returnScalar; eauto 8.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples1' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* find *)

  do_abort ("self" :: "k" :: nil).
  do_abort ("self" :: "k" :: nil).
  do_abort ("self" :: "k" :: nil).

  do_delegate1 ("self" :: "k" :: nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 8.
  simpl.
  make_toArray ("self" :: "k" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples1 ] ].
  do_delegate2 ("self" :: "k" :: nil).

  (* enumerate *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 8.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples1 ] ].
  do_delegate2 ("self" :: nil).


  (* Tuples1 *)

  (* new *)

  do_abort ("len" :: "key1" :: "key2" :: nil).
  do_abort ("len" :: "key1" :: "key2" :: nil).
  do_abort ("len" :: "key1" :: "key2" :: nil).

  do_delegate1 ("len" :: "key1" :: "key2" :: nil) hints.
  descend; step auto_ext.
  peel.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("len" :: "key1" :: "key2" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("len" :: "key1" :: "key2" :: nil).

  (* insert *)

  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).
  do_abort ("self" :: "tup" :: nil).

  do_delegate1 ("self" :: "tup" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl; step hints.
  peel.
  apply get_rval''; intro.
  descend; step hints.
  descend; step hints.
  2: returnScalar; eauto 9.
  simpl.
  make_toArray ("self" :: "tup" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples2' ] ].
  do_delegate2 ("self" :: "tup" :: nil).
  congruence.

  (* findBoth *)

  do_abort ("self" :: "k1" :: "k2" :: nil).
  do_abort ("self" :: "k1" :: "k2" :: nil).
  do_abort ("self" :: "k1" :: "k2" :: nil).

  do_delegate1 ("self" :: "k1" :: "k2" :: nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 10.
  simpl.
  make_toArray ("self" :: "k1" :: "k2" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples2 ] ].
  do_delegate2 ("self" :: "k1" :: "k2" :: nil).

  (* findFirst *)

  do_abort ("self" :: "k1" ::  nil).
  do_abort ("self" :: "k1" ::  nil).
  do_abort ("self" :: "k1" ::  nil).

  do_delegate1 ("self" :: "k1" ::  nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 10.
  simpl.
  make_toArray ("self" :: "k1" ::  nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples2 ] ].
  do_delegate2 ("self" :: "k1" ::  nil).

  (* findSecond *)

  do_abort ("self" :: "k2" ::  nil).
  do_abort ("self" :: "k2" ::  nil).
  do_abort ("self" :: "k2" ::  nil).

  do_delegate1 ("self" :: "k2" ::  nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 10.
  simpl.
  make_toArray ("self" :: "k2" ::  nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples2 ] ].
  do_delegate2 ("self" :: "k2" ::  nil).

  (* enumerate *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  peel.
  apply get_rval''''; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnAdt; eauto 8.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_Tuples2 ] ].
  do_delegate2 ("self" :: nil).


  (* ByteString *)

  (* new *)

  do_abort ("capacity" :: nil).
  do_abort ("capacity" :: nil).
  do_abort ("capacity" :: nil).

  do_delegate1 ("capacity" :: nil) hints.
  do 2 (descend; step auto_ext).
  2: returnAdt.
  simpl.
  make_toArray ("capacity" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  do_delegate2 ("capacity" :: nil).

  (* delete *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval'; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* copy *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  2: returnAdt.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_ByteString ] ].
  do_delegate2 ("self" :: nil).

  (* push *)

  do_abort ("self" :: "byte" :: nil).
  do_abort ("self" :: "byte" :: nil).
  do_abort ("self" :: "byte" :: nil).

  do_delegate1 ("self" :: "byte" :: nil) hints.
  descend; step hints.
  simpl.
  peel.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "byte" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_ByteString ] ].
  fold (@app B).
  erewrite BtoW_WtoB by eassumption.
  do_delegate2 ("self" :: "byte" :: nil).

  (* put *)

  do_abort ("self" :: "index" :: "byte" :: nil).
  do_abort ("self" :: "index" :: "byte" :: nil).
  do_abort ("self" :: "index" :: "byte" :: nil).

  do_delegate1 ("self" :: "index" :: "byte" :: nil) hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  step auto_ext.
  2: returnScalar; eauto 10.
  simpl.
  make_toArray ("self" :: "index" :: "byte" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_ByteString ] ].
  erewrite BtoW_WtoB by eassumption.
  do_delegate2 ("self" :: "index" :: "byte" :: nil).

  (* get *)

  do_abort ("self" :: "index" :: nil).
  do_abort ("self" :: "index" :: nil).
  do_abort ("self" :: "index" :: nil).

  do_delegate1 ("self" :: "index" :: nil) hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  step auto_ext.
  2: returnScalar; eauto 10.
  simpl.
  make_toArray ("self" :: "index" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_ByteString ] ].
  do_delegate2 ("self" :: "index" :: nil).


  (* Grabby time *)
  Grab Existential Variables.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
  exact 0.
Qed.

Definition m1 := link ArrayTupleF.m m0.
Definition m2 := link ListSeqF.m m1.
Definition m3 := link TupleListF.m m2.
Definition m4 := link Tuples0F.m m3.
Definition m5 := link Tuples1F.m m4.
Definition m6 := link Tuples2F.m m5.
Definition m7 := link ByteString.m m6.
Definition m := link Malloc.m m7.

Theorem ok1 : moduleOk m1.
Proof.
  link ArrayTupleF.ok ok0.
Qed.

Theorem ok2 : moduleOk m2.
Proof.
  link ListSeqF.ok ok1.
Qed.

Theorem ok3 : moduleOk m3.
Proof.
  link TupleListF.ok ok2.
Qed.

Theorem ok4 : moduleOk m4.
Proof.
  link Tuples0F.ok ok3.
Qed.

Theorem ok5 : moduleOk m5.
Proof.
  link Tuples1F.ok ok4.
Qed.

Theorem ok6 : moduleOk m6.
Proof.
  link Tuples2F.ok ok5.
Qed.

Theorem ok7 : moduleOk m7.
Proof.
  link ByteString.ok ok6.
Qed.

Theorem ok : moduleOk m.
Proof.
  link Malloc.ok ok7.
Qed.
