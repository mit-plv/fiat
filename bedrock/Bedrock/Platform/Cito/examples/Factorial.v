Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper Bedrock.Platform.Cito.examples.ExampleADT Bedrock.Platform.Cito.examples.ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Bedrock.Platform.Cito.Notations4.

Open Scope nat.

Require Import Coq.Arith.Arith.

Definition fact_w (w : W) := natToW (fact (wordToNat w)).

Require Import ProgramLogic2.

Definition body : StmtEx ADTValue := (
    "ret" <- 1;;
    [BEFORE(V, h)
     AFTER(V', h')
       fact_w (V "n") = V' "ret" ^* fact_w (V' "n")
       /\ h' = h]
    While (0 < "n") {
      "ret" <- "ret" * "n";;
      "n" <- "n" - 1
    }
  )%stmtex.

Definition f := (
  cfunction "fact"("n")
    body
  end
)%Citofuncs.

Definition m := cmodule "fact" {{
  f
}}.

Lemma good : IsGoodModule m.
  good_module.
Qed.

Definition gm := to_good_module good.

Definition fspec :=
  cimport "fact"!"fact"
  cmodules [[ gm ]]
  definition f.

Notation extra_stack := 40.

Definition topS := SPEC reserving (4 + extra_stack)
  PREonly[_] mallocHeap 0.

Notation input := 5.

Definition top := bimport [[ ("fact"!"fact", fspec), "sys"!"printInt" @ [printIntS],
                             "sys"!"abort" @ [abortS] ]]
  bmodule "top" {{
    bfunction "top"("R") [topS]
      "R" <-- Call "fact"!"fact"(extra_stack, input)
      [PREonly[_, R] [| R = fact input |] ];;

      Call "sys"!"printInt"("R")
      [PREonly[_] Emp ];;

      Call "sys"!"abort"()
      [PREonly[_] [| False |] ]
    end
  }}.

Definition empty_precond : assert ADTValue := fun _ v0 v => v0 = v.

Require Import Bedrock.Platform.Cito.WordFacts2 Bedrock.Platform.Cito.WordFacts5.

Lemma fact_step : forall n,
  ($0 < n)%word
  -> fact_w n = n ^* fact_w (n ^- $1).
  intros.
  unfold fact_w.
  rewrite wordToNat_positive by assumption.
  unfold fact at 1; fold fact.
  rewrite <- wordToNat_positive by assumption.
  unfold natToW; rewrite natToWord_mult.
  rewrite natToWord_wordToNat.
  reflexivity.
Qed.

Hint Rewrite fact_step using solve [ eauto 2 ] : sepFormula.

Definition dummy_gf : GoodFunction.
  refine (to_good_function f _).
  good_module.
Defined.

Definition spec_op := hd dummy_gf (Functions gm).

Definition specs := add ("fact", "fact") (Internal spec_op) (empty _).

Definition modules := gm :: nil.
Definition imports := empty ForeignFuncSpec.

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

  eapply empty_mapsto_iff in H0; intuition.

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
  rewrite empty_o in H0; intuition.
Qed.

Hint Immediate lt0_false lt0_true.

Lemma vcs_good : and_all (vc body empty_precond) specs.
  unfold empty_precond; cito_vcs body; words.
Qed.

Local Hint Immediate vcs_good.

Theorem final : forall n x r,
  ($0 >= n)%word
  -> x = r ^* fact_w n
  -> r = x.
  intros; subst.
  assert (n = $0) by (apply wordToNat_inj; nomega).
  subst.
  change (fact_w $0) with (natToW 1).
  words.
Qed.

Local Hint Resolve final.

Import LinkSpecMake.

Hint Resolve specs_good.

Lemma body_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' = snd v.
  cito_runsto f empty_precond vcs_good; eauto.
  eapply specs_equal_agree; eauto.
Qed.

Lemma body_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  cito_safe f empty_precond vcs_good.
  eapply specs_equal_agree; eauto.
Qed.

Require Import Bedrock.Platform.Cito.Inv.
Module Import InvMake := Make ExampleADT.
Module Import InvMake2 := Make ExampleRepInv.
Import Made.
Import LinkSpecMake2.CompileFuncSpecMake.InvMake.SemanticsMake.
Require Import Bedrock.Platform.Cito.GeneralTactics3.
Require Import Bedrock.Platform.Cito.BedrockTactics.

Theorem top_ok : moduleOk top.
  vcgen.

  sep_auto.
  sep_auto.
  sep_auto.
  sep_auto.

  post.
  call_cito 40 ("n" :: nil).
  hiding ltac:(evaluate auto_ext).
  unfold name_marker.
  hiding ltac:(step auto_ext).
  unfold spec_without_funcs_ok.
  post.
  descend.
  eapply CompileExprs.change_hyp.
  Focus 2.
  apply (@is_state_in''' (upd (upd x2 "extra_stack" 40) "n" input)).
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
  change 40 with (wordToNat (sel (upd (upd x2 "extra_stack" 40) "n" 5) "extra_stack")).
  apply is_state_out''''.
  NoDup.
  NoDup.
  NoDup.
  clear H7.
  hiding ltac:(step auto_ext).
  hiding ltac:(step auto_ext).
  sel_upd_simpl.
  rewrite H9.
  rewrite H11.
  reflexivity.

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
