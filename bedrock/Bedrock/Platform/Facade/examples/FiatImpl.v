Set Implicit Arguments.

(* there is a name conflict on tactic 'unfolder' between GeneralTactics and MakeADT *)
Require Import Bedrock.Platform.Cito.GeneralTactics.

Require Import Bedrock.Platform.Facade.examples.FiatADTs.
Import Adt.
Require Import Bedrock.Platform.Cito.WordMap.
Require Import Bedrock.Platform.Cito.RepInv Bedrock.Platform.Cito.MakeADT.

Require Import Bedrock.Platform.AutoSep.

Require Import Bedrock.Platform.Facade.examples.ListSetF Bedrock.Platform.Facade.examples.ListSeqF Bedrock.Platform.Facade.examples.FiatRepInv.

Module Import Made := MakeADT.Make(FiatADTs.Adt)(Ri).

Import Semantics.

Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.SemanticsMake.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake2.
Import LinkMake.StubsMake.StubMake.CompileFuncSpecMake.InvMake.

Lemma is_heap_eat : forall w v,
  is_heap heap_empty
  ===> is_heap (WordMap.remove w (heap_upd heap_empty w v)).
  intros; apply is_heap_Equal.
  apply Properties.F.Equal_mapsto_iff; intuition.
  apply Properties.F.empty_mapsto_iff in H; tauto.
  apply Properties.F.remove_mapsto_iff in H; intuition.
  apply Properties.F.add_mapsto_iff in H1; intuition.
Qed.
Require Import Bedrock.Platform.Cito.SemanticsFacts5.
Require Import Bedrock.Platform.Cito.LayoutHintsUtil.

Lemma readd_FEnsemble : forall c rv rv',
  lset rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (FEnsemble rv') (heap_upd heap_empty c (FEnsemble rv))).
  intros.
  unfold is_heap at 2.
  assert (List.In (c, FEnsemble rv') (heap_elements (WordMap.add c (FEnsemble rv') (heap_upd heap_empty c (FEnsemble rv))))).
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
Import LayoutHintsUtil.

Lemma readd_List : forall c rv rv',
  lseq rv' c * is_heap heap_empty
  ===> is_heap (WordMap.add c (List rv') (heap_upd heap_empty c (List rv))).
  intros.
  unfold is_heap at 2.
  assert (List.In (c, List rv') (heap_elements (WordMap.add c (List rv') (heap_upd heap_empty c (List rv))))).
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

Lemma get_rval : forall specs st P (Q : Prop) R S T Z,
  (Q -> interp specs (![P * R * S * T] st ---> Z)%PropX)
  -> interp specs (![P * (([|Q|] * R) * S) * T] st ---> Z)%PropX.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S * T)]st)%PropX.
  assert (P * ([|Q|] * R * S) * T ===> [|Q|] * (P * R * S * T)).
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

Lemma get_rval' : forall specs st P (Q : Prop) R S T Z,
  (Q -> interp specs (![P * R * S * T] st ---> Z)%PropX)
  -> interp specs (![P * ((R * [|Q|]) * S) * T] st ---> Z)%PropX.
  intros.
  apply Imply_trans with (![[|Q|] * (P * R * S * T)]st)%PropX.
  assert (P * (R * [|Q|] * S) * T ===> [|Q|] * (P * R * S * T)).
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

Lemma get_rval'' : forall specs st P (Q : Prop) R S Z,
  (Q -> interp specs (![P * R * S] st ---> Z)%PropX)
  -> interp specs (![P * ([|Q|] * R) * S] st ---> Z)%PropX.
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

Definition hints : TacPackage.
  prepare (store_pair_inl_fwd, store_pair_inr_fwd)
  (store_pair_inl_bwd, store_pair_inr_bwd).
Defined.

Arguments SCA {ADTValue} _.
Arguments ADT {ADTValue} _.

Require Bedrock.Platform.Cito.AxSpec.
Import AxSpec.ConformTactic.

Definition m0 := bimport [[ "sys"!"abort" @ [abortS],

                            "ListSet"!"new" @ [ListSetF.newS],
                            "ListSet"!"delete" @ [ListSetF.deleteS],
                            "ListSet"!"mem" @ [ListSetF.memS],
                            "ListSet"!"add" @ [ListSetF.addS],
                            "ListSet"!"remove" @ [ListSetF.removeS],
                            "ListSet"!"size" @ [ListSetF.sizeS],

                            "ListSeq"!"new" @ [ListSeqF.newS],
                            "ListSeq"!"delete" @ [ListSeqF.deleteS],
                            "ListSeq"!"pop" @ [ListSeqF.popS],
                            "ListSeq"!"empty" @ [ListSeqF.emptyS],
                            "ListSeq"!"push" @ [ListSeqF.pushS],
                            "ListSeq"!"copy" @ [ListSeqF.copyS],
                            "ListSeq"!"rev" @ [ListSeqF.revS],
                            "ListSeq"!"length" @ [ListSeqF.lengthS] ]]
  fmodule "ADT" {{
    ffunction "sEmpty" reserving 8 [FEnsemble_sEmpty] := "ListSet"!"new"
    with ffunction "sDelete" reserving 7 [FEnsemble_sDelete] := "ListSet"!"delete"
    with ffunction "sAdd" reserving 9 [FEnsemble_sAdd] := "ListSet"!"add"
    with ffunction "sRemove" reserving 7 [FEnsemble_sRemove] := "ListSet"!"remove"
    with ffunction "sIn" reserving 1 [FEnsemble_sIn] := "ListSet"!"mem"
    with ffunction "sSize" reserving 1 [FEnsemble_sSize] := "ListSet"!"size"
    with ffunction "new" reserving 8 [List_new] := "ListSeq"!"new"
    with ffunction "delete" reserving 7 [List_delete] := "ListSeq"!"delete"
    with ffunction "pop" reserving 8 [List_pop] := "ListSeq"!"pop"
    with ffunction "empty" reserving 0 [List_empty] := "ListSeq"!"empty"
    with ffunction "push" reserving 8 [List_push] := "ListSeq"!"push"
    with ffunction "copy" reserving 10 [List_copy] := "ListSeq"!"copy"
    with ffunction "rev" reserving 2 [List_rev] := "ListSeq"!"rev"
    with ffunction "length" reserving 1 [List_length] := "ListSeq"!"length"
  }}.

Theorem ok0 : moduleOk m0.
  vcgen.


  (* ListSet *)

  (* sEmpty *)

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

  (* sDelete *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval''; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply is_heap_eat ] ].
  do_delegate2 ("self" :: nil).

  (* sAdd *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  simpl.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FEnsemble ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* sRemove *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  simpl.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FEnsemble ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* sIn *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  step auto_ext.
  descend; step auto_ext.
  2: rewrite FiniteSetF.Has.has_eq in *; returnSomething; eauto 6.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FEnsemble ] ].
  do_delegate2 ("self" :: "n" :: nil).

  (* sSize *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  destruct H0 as [ ? [ ] ].
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_FEnsemble ] ].
  do_delegate2 ("self" :: nil).


  (* ListSeq *)

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
  apply get_rval''; intro.
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
  apply get_rval; intro.
  descend; step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* empty *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  step auto_ext.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* push *)

  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).
  do_abort ("self" :: "n" :: nil).

  do_delegate1 ("self" :: "n" :: nil) hints.
  add_side_conditions.
  descend; step hints.
  simpl.
  descend; step auto_ext.
  descend; step auto_ext.
  simpl.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: "n" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
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
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* rev *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  simpl.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  descend; step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).

  (* length *)

  do_abort ("self" :: nil).
  do_abort ("self" :: nil).
  do_abort ("self" :: nil).

  do_delegate1 ("self" :: nil) hints.
  descend; step hints.
  repeat (apply andL || (apply injL; intro) || (apply existsL; intro)); reduce.
  apply get_rval; intro.
  step auto_ext.
  2: returnScalar.
  simpl.
  make_toArray ("self" :: nil).
  step auto_ext.
  etransitivity; [ | apply (@is_state_in x2) ].
  unfolder.
  etransitivity; [ | apply himp_star_frame; [ reflexivity | apply readd_List ] ].
  do_delegate2 ("self" :: nil).


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
Qed.

Definition m1 := link ListSetF.m m0.
Definition m2 := link ListSeqF.m m1.
Definition m := link Malloc.m m2.

Theorem ok1 : moduleOk m1.
  link ListSetF.ok ok0.
Qed.

Theorem ok2 : moduleOk m2.
  link ListSeqF.ok ok1.
Qed.

Theorem ok : moduleOk m.
  link Malloc.ok ok2.
Qed.
