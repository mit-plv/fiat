Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper Bedrock.Platform.Cito.examples.ExampleADT Bedrock.Platform.Cito.examples.ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Bedrock.Platform.Cito.Notations4.

Require Import Coq.Arith.Arith.

Open Scope nat.

Require Import Bedrock.Platform.Cito.examples.ExampleImpl.

Notation value := 42.

Require Import Bedrock.Platform.Cito.WordMap.

Infix "==" := WordMap.Equal.
Notation addw := WordMap.add.
Notation Inw := WordMap.In.

Definition disj_add elt h' k v h := h' == @addw elt k v h /\ ~ Inw k h.

Notation "h1 === k --> v ** h" := (disj_add h1 k v h) (at level 60).

Definition body := (
  "c" <-- DCall "ADT"!"SimpleCell_new" ();;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' === (V' "c") --> (Cell 0) ** h ];;
  DCall "ADT"!"SimpleCell_write"("c", value);;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' === (V' "c") --> (Cell value) ** h];;
  "ret" <-- DCall "ADT"!"SimpleCell_read"("c");;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' === (V' "c") --> (Cell value) ** h /\ V' "ret" = value];;
  DCall "ADT"!"SimpleCell_delete"("c");;
  Assert [
    BEFORE(V, h)
    AFTER(V', h')
    h' == h /\ V' "ret" = value]
  )%stmtex.

Require Import ProgramLogic2.

Definition f := (
  cfunction "use_cell"()
    body
  end
)%Citofuncs.

Definition m := cmodule "use_cell" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Import LinkSpecMake2.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].
Definition imports := of_list [[
                                  "ADT"!"SimpleCell_new" @ [SimpleCell_newSpec],
                                  "ADT"!"SimpleCell_write" @ [SimpleCell_writeSpec],
                                  "ADT"!"SimpleCell_read" @ [SimpleCell_readSpec],
                                  "ADT"!"SimpleCell_delete" @ [SimpleCell_deleteSpec]
                              ]].

Definition fspec := func_spec modules imports ("use_cell"!"use_cell")%stmtex f.

Notation extra_stack := 20.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Notation input := 5.

Definition top := bimport [[ ("use_cell"!"use_cell", fspec), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "use_cell"!"use_cell"(extra_stack)
      [PREonly[_, R] [| R = value |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition dummy_gf : GoodFunction.
  refine (to_good_function f _).
  good_module.
Defined.

Definition spec_op := hd dummy_gf (Functions gm).

Definition specs := add ("use_cell", "use_cell") (Internal spec_op) (map Foreign imports).

Import LinkSpecMake.
Require Import Bedrock.Platform.Cito.LinkSpecFacts.
Import LinkSpecMake.
Require Import Bedrock.Platform.Cito.GeneralTactics2.

Lemma specs_good : specs_equal specs modules imports.
  split; intros.

  unfold label_mapsto, specs in *.
  eapply find_mapsto_iff in H.
  eapply add_mapsto_iff in H.
  openhyp.
  subst; simpl in *.
  left; descend; eauto.
  unfold spec_op, gm; simpl; eauto.

  eapply map_mapsto_iff in H0.
  openhyp.
  subst; simpl in *.
  right; descend; eauto.
  eapply find_mapsto_iff; eauto.

  unfold label_mapsto, specs in *.
  eapply find_mapsto_iff.
  eapply add_mapsto_iff.
  openhyp.
  subst; simpl in *.
  openhyp.
  2 : intuition.
  subst.
  left.
  unfold spec_op, gm, to_good_module in *; simpl in *.
  openhyp.
  2 : intuition.
  subst; simpl in *.
  eauto.

  subst; simpl in *.
  right; descend; eauto.
  nintro.
  subst; simpl in *.
  compute in H0.
  intuition.
  eapply map_mapsto_iff.
  descend; eauto.
  eapply find_mapsto_iff; eauto.
Qed.

Definition empty_precond : assert ADTValue := fun _ v0 v => v0 = v.

Require Import Bedrock.Platform.Cito.WordFacts2 Bedrock.Platform.Cito.WordFacts5.
Require Import Bedrock.Platform.Cito.WordMapFacts.

Lemma map_add_same_key : forall elt m k v1 v2, @addw elt k v2 (addw k v1 m) == addw k v2 m.
  unfold WordMap.Equal; intros.
  repeat rewrite add_o.
  destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
Qed.

Lemma add_remove : forall elt m k v, ~ @Inw elt k m -> WordMap.remove k (addw k v m) == m.
  unfold WordMap.Equal; intros.
  rewrite remove_o.
  rewrite add_o.
  destruct (UWFacts.WFacts.P.F.eq_dec k y); intuition.
  subst.
  symmetry; eapply not_find_in_iff; eauto.
Qed.

Ltac destruct_state :=
  repeat match goal with
           | [ x : Semantics.State ADTValue |- _ ] => destruct x; simpl in *
         end.
Import Transit.
Require Import Bedrock.Platform.Cito.BedrockTactics.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Import SemanticsMake.

Lemma vcs_good : and_all (vc body empty_precond) specs.
  unfold empty_precond, body; simpl; unfold imply_close, and_lift; simpl.
  split.
  {
    intros.
    subst.
    unfold SafeDCall.
    simpl.
    intros.
    unfold TransitSafe.
    descend.
    instantiate (1 := nil).
    eauto.
    repeat econstructor.
    simpl; eauto.
  }
  split.
  {
    intros.
    openhyp.
    subst.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct v'; simpl in *.
    rewrite H0.
    subst.
    split.
    {
      sel_upd_simpl.
      destruct x3; simpl in *; try discriminate.
      inject H7.
      eauto.
    }
    unfold separated, Semantics.separated in *; simpl in *.
    openhyp; subst; simpl in *; intuition.
  }
  split.
  {
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct v'; simpl in *.
    unfold TransitSafe.
    descend.
    {
      instantiate (1 := [[ ADT (Cell 0), SCA ($42) ]]).
      eauto.
    }
    {
      unfold good_inputs.
      split.
      {
        unfold Semantics.word_adt_match.
        repeat econstructor.
        simpl.
        destruct H.
        rewrite H.
        eapply find_mapsto_iff.
        eapply add_mapsto_iff.
        eauto.
      }
      unfold Semantics.disjoint_ptrs.
      NoDup.
    }
    descend; eauto.
  }
  split.
  {
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    subst; simpl in *.
    unfold store_out, Semantics.store_out in *; simpl in *.
    destruct H.
    split.
    {
      sel_upd_simpl.
      destruct x0; simpl in *; try discriminate.
      destruct x0; simpl in *; try discriminate.
      destruct o; simpl in *; try discriminate.
      destruct x2; simpl in *; try discriminate.
      inject H8.
      inject H5.
      rewrite H7.
      rewrite H.
      eapply map_add_same_key.
    }
    unfold separated, Semantics.separated in *; simpl in *.
    openhyp; subst; simpl in *; intuition.
  }
  split.
  {
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    unfold TransitSafe.
    descend.
    {
      sel_upd_simpl.
      instantiate (1 := [[ ADT (Cell 42) ]]).
      eauto.
    }
    split.
    {
      unfold Semantics.word_adt_match.
      repeat econstructor.
      simpl.
      destruct H.
      rewrite H.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      eauto.
    }
    {
      NoDup.
    }
    descend; eauto.
  }
  split.
  {
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x0; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H5.
    inject H8.
    unfold good_inputs, Semantics.good_inputs in *.
    openhyp.
    unfold Semantics.word_adt_match in *.
    inversion_Forall; simpl in *.
    unfold store_out, Semantics.store_out in *; simpl in *.
    destruct H.
    rewrite H in H8.
    eapply find_mapsto_iff in H8.
    eapply add_mapsto_iff in H8.
    sel_upd_simpl.
    openhyp; intuition.
    inject H5.
    split.
    {
      rewrite H7.
      rewrite H.
      eapply map_add_same_key.
    }
    eauto.
  }
  split.
  {
    intros.
    unfold SafeDCall.
    simpl.
    intros.
    destruct_state.
    unfold TransitSafe.
    descend.
    {
      sel_upd_simpl.
      instantiate (1 := [[ ADT (Cell 42) ]]).
      eauto.
    }
    split.
    {
      unfold Semantics.word_adt_match.
      repeat econstructor.
      simpl.
      openhyp.
      destruct H.
      rewrite H.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      eauto.
    }
    {
      NoDup.
    }
    descend; eauto.
  }
  split.
  {
    intros.
    openhyp.
    destruct_state.
    unfold RunsToDCall in *.
    simpl in *.
    openhyp.
    unfold TransitTo in *.
    openhyp.
    unfold PostCond in *; simpl in *.
    openhyp.
    subst; simpl in *.
    destruct x0; simpl in *; try discriminate.
    destruct x2; simpl in *; try discriminate.
    inject H6.
    inject H9.
    unfold store_out, Semantics.store_out in *; simpl in *.
    destruct H.
    split.
    {
      rewrite H8.
      rewrite H.
      eapply add_remove; eauto.
    }
    eauto.
  }
  eauto.
Qed.

Local Hint Immediate vcs_good.

Hint Resolve specs_good.

Lemma body_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  cito_safe f empty_precond vcs_good; eauto.
  eapply specs_equal_agree; eauto.
Qed.

Lemma body_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = value /\ snd v' == snd v.
  cito_runsto f empty_precond vcs_good; eauto.
  eapply specs_equal_agree; eauto.
Qed.

Require Import Bedrock.Platform.Cito.Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.
Import Made.
Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
Require Import Bedrock.Platform.Cito.GeneralTactics3.

Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  call_cito 20 (@nil string).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd x2 "extra_stack" 20)).
  autorewrite with sepFormula.
  clear H7.
  hiding ltac:(step auto_ext).
  apply body_safe; eauto.
  hiding ltac:(step auto_ext).
  repeat ((apply existsL; intro) || (apply injL; intro) || apply andL); reduce.
  apply swap; apply injL; intro.
  openhyp.
  match goal with
    | [ x : State |- _ ] => destruct x; simpl in *
  end.
  eapply_in_any body_runsto; simpl in *; intuition subst.
  eapply replace_imp.
  change 20 with (wordToNat (sel (upd x2 "extra_stack" 20) "extra_stack")).
  apply is_state_out'''''.
  NoDup.
  NoDup.
  NoDup.
  eauto.

  clear H7.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.
Qed.

Definition all := link top (compile_to_bedrock modules imports).

Theorem all_ok : moduleOk all.
  link0 top_ok.
Qed.
