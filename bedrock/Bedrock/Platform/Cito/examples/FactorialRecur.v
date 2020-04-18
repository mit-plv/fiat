Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.MakeWrapper Bedrock.Platform.Cito.examples.ExampleADT Bedrock.Platform.Cito.examples.ExampleRepInv.

Module Import Wrp := Make(ExampleADT)(ExampleRepInv).
Export Wrp.

Require Import Bedrock.Platform.Cito.Notations4.

Require Import Coq.Arith.Arith.

Open Scope nat.

Definition fact_w (w : W) := natToW (fact (wordToNat w)).

Require Import ProgramLogic2.

Definition body : StmtEx ADTValue := (
  If (0 < "n") {
    "ret" <-- DCall "fact"!"fact" ("n" - 1);;
    "ret" <- "n" * "ret"
  } else {
    "ret" <- 1
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

Import LinkSpecMake2.

Notation " [[ ]] " := nil.
Notation " [[ x , .. , y ]] " := (cons x .. (cons y nil) ..).

Notation "name @ [ p ]" := (name%stmtex, p) (only parsing).

Definition modules := [[ gm ]].
Definition imports := empty ForeignFuncSpec.

Definition fspec := func_spec modules imports ("fact"!"fact")%stmtex f.

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

Import LinkSpecMake.

Require Import Bedrock.Platform.Cito.SemanticsFacts4.

Require Bedrock.Platform.Cito.AxSpec.
Import AxSpec.ConformTactic.

Arguments SCA {ADTValue} _.
Arguments ADT {ADTValue} _.

Definition fact_spec : ForeignFuncSpec.
  refine
    {|
      PreCond := fun args => exists n, args = SCA n :: nil;
      PostCond := fun args ret => exists n, args = (SCA n, None) :: nil
                                            /\ ret = SCA (fact_w n)
    |}.
  conform.
Defined.

Definition specs := add ("fact", "fact") (Foreign fact_spec) (empty _).

Definition change_fs (fs : settings -> W -> option Callee) : settings -> W -> option Callee :=
  fun stn w =>
    match fs stn w with
      | Some (Semantics.Internal _) => Some (Foreign fact_spec)
      | other => other
    end.
Lemma in_specs_label_in : forall lbl, In lbl specs -> label_in modules imports lbl.
  intros.
  unfold specs in *.
  eapply add_in_iff in H.
  openhyp.
  subst; simpl in *.
  left.
  unfold gm, to_good_module in *; simpl in *.
  descend.
  eauto.
  simpl; eauto.
  simpl; eauto.
  eapply empty_in_iff in H; intuition.
Qed.
Require Import Bedrock.Platform.Cito.Option.
Lemma Some_not_None : forall A o (v : A), o = Some v -> o <> None.
  intuition.
Qed.

Lemma change_fs_agree : forall fs stn, env_good_to_use modules imports stn fs -> specs_env_agree specs (from_bedrock_label_map (Labels stn), change_fs fs stn).
  intros.
  split.
  simpl.
  unfold labels_in_scope.
  intros.
  eapply H.
  eapply in_specs_label_in; eauto.

  split.
  Focus 2.
  unfold specs_fs_agree; simpl in *.
  unfold change_fs.
  intros.
  destruct (option_dec (fs stn p)).
  destruct s; rewrite e in *.
  destruct x; simpl in *.
  eapply H in e.
  unfold label_mapsto in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  discriminate.
  intuition.
  intuition.
  injection H1; intros; subst.
  unfold imports in H2; simpl in *.
  compute in H2; intuition.
  split; intros.
  injection H0; intros; subst.
  eapply H in e.
  unfold label_mapsto in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  openhyp.
  subst; simpl in *.
  injection H2; intros; subst; simpl in *; clear H2.
  descend.
  eauto.
  reflexivity.
  intuition.
  intuition.
  compute in H3; intuition.
  openhyp.
  unfold specs in H1.
  eapply find_mapsto_iff in H1.
  eapply add_mapsto_iff in H1.
  openhyp.
  subst; eauto.
  eapply empty_mapsto_iff in H2; intuition.
  rewrite e in *.
  split; intros.
  discriminate.
  openhyp.
  unfold specs in H1.
  eapply find_mapsto_iff in H1.
  eapply add_mapsto_iff in H1.
  openhyp.
  subst; simpl in *.
  contradict e.
  eapply Some_not_None.
  eapply H.
  descend.
  eauto.
  left.
  unfold gm, to_good_module in *; simpl in *.
  descend.
  eauto.
  eauto.
  simpl; eauto.
  eauto.
  simpl; eauto.
  eapply empty_mapsto_iff in H2; intuition.

  unfold specs_stn_injective; simpl in *.
  unfold change_fs.
  intros.
  eapply H; eauto.
  eapply in_specs_label_in; eauto.
  eapply in_specs_label_in; eauto.
Qed.

Ltac destruct_state :=
  repeat match goal with
           | [ x : Semantics.State ADTValue |- _ ] => destruct x; simpl in *
         end.

Hint Immediate lt0_false lt0_true.
Ltac cito_vcs body := unfold body; simpl;
  unfold imply_close, and_lift, interp; simpl.
Require Import Bedrock.Platform.Cito.BedrockTactics.

Lemma vcs_good : and_all (vc body empty_precond) specs.

  unfold empty_precond.

  cito_vcs body.

  split.
  intros.
  openhyp.
  subst.
  unfold SafeDCall.
  simpl.
  intros.
  destruct_state.
  unfold Transit.TransitSafe.
  descend.
  sel_upd_simpl.
  instantiate (1 := [[ (SCA (sel v "n" ^- $1)) ]]).
  eauto.
  repeat constructor.
  descend; eauto.

  eauto.
Qed.

Local Hint Immediate vcs_good.

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

Theorem final : forall n,
  ($0 >= n)%word
  -> $1 = fact_w n.
  intros; subst.
  assert (n = $0) by (apply wordToNat_inj; nomega).
  subst.
  change (fact_w $0) with (natToW 1).
  words.
Qed.

Local Hint Resolve final.

Infix "==" := WordMap.WordMap.Equal.
Require Import Bedrock.Platform.Cito.GeneralTactics4.

Lemma body_runsto' : forall env v v', specs_env_agree specs env -> RunsTo env (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' == snd v.
  cito_runsto f empty_precond vcs_good.
  3 : eauto.
  Focus 2.
  subst; simpl in *.
  split.
  eauto.
  reflexivity.

  subst; simpl in *.
  sel_upd_simpl.
  destruct_state.
  unfold RunsToDCall in *.
  simpl in *.
  openhyp.
  unfold Transit.TransitTo in *.
  openhyp.
  unfold PostCond in *; simpl in *.
  openhyp.
  subst; simpl in *.
  destruct x0; simpl in *; try discriminate.
  destruct x0; simpl in *; try discriminate.
  destruct x2; simpl in *; try discriminate.
  inject H6.
  inject H9.
  subst; simpl in *.
  unfold store_out, Semantics.store_out in *; simpl in *.
  unfold good_inputs, Semantics.good_inputs in *.
  openhyp.
  unfold Semantics.word_adt_match in *.
  inversion_Forall; simpl in *.
  subst; simpl in *.
  sel_upd_simpl.
  split.
  symmetry; eapply fact_step; eauto.
  eapply lt0_true in H3.
  eauto.
  eauto.

Qed.

Lemma body_safe' : forall env v, specs_env_agree specs env -> Safe env (Body f) v.
  cito_safe f empty_precond vcs_good.
Qed.

Lemma change_fs_strengthen : forall fs stn, env_good_to_use modules imports stn fs ->strengthen (from_bedrock_label_map (Labels stn), fs stn) (from_bedrock_label_map (Labels stn), change_fs fs stn).
  unfold modules, imports.
  intros.
  generalize H; intro.
  unfold strengthen, strengthen_op_ax.
  split.
  {
    eauto.
  }
  unfold change_fs at 1.
  unfold change_fs at 1.
  simpl.
  intros.
  destruct (option_dec (fs stn w)); simpl in *.
  {
    destruct s; rewrite e in *; simpl in *.
    destruct x; simpl in *.
    {
      eauto.
    }
    eapply H0 in e.
    unfold label_mapsto in *.
    openhyp.
    {
      subst; simpl in *.
      openhyp; try contradiction.
      subst; simpl in *.
      openhyp; try contradiction.
      subst; simpl in *.
      injection H2; intros; subst; simpl in *; clear H2.
      right; descend.
      { eauto. }
      { eauto. }
      {
        instantiate (1 := fun words _ _ => List.map (fun _ => None) words).
        unfold outputs_gen_ok; intros.
        simpl.
        rewrite map_length.
        eauto.
      }
      {
        unfold strengthen_op_ax'.
        descend.
        {
          simpl in *.
          openhyp.
          rewrite H2.
          eauto.
        }
        {
          simpl in *.
          eapply body_safe'; eauto.
          eapply change_fs_agree; eauto.
        }
        {
          eapply body_runsto' in H2; eauto.
          Focus 2.
          eapply change_fs_agree; eauto.
          simpl.
          openhyp.
          unfold Transit.TransitTo.
          unfold Transit.TransitSafe in *.
          openhyp; simpl in *.
          openhyp; simpl in *.
          subst; simpl in *.
          descend.
          { eauto. }
          { eauto. }
          {
            unfold Semantics.good_inputs in *.
            openhyp.
            unfold Semantics.word_adt_match in *.
            inversion_Forall; simpl in *.
            subst.
            instantiate (1 := fun _ _ => None); simpl.
            f_equal.
            eauto.
          }
          {
            repeat econstructor.
          }
          {
            simpl.
            unfold store_out, Semantics.store_out; simpl; eauto.
          }
        }
      }
    }
    {
      descend; eauto.
    }
  }
  {
    rewrite e.
    left; eauto.
  }
Qed.

Lemma body_safe : forall stn fs v, env_good_to_use modules imports stn fs -> Safe (from_bedrock_label_map (Labels stn), fs stn) (Body f) v.
  intros.
  eapply strengthen_safe.
  eapply body_safe'; eauto.
  eapply change_fs_agree; eauto.
  eapply change_fs_strengthen; eauto.
Qed.

Lemma body_runsto : forall stn fs v v', env_good_to_use modules imports stn fs -> RunsTo (from_bedrock_label_map (Labels stn), fs stn) (Body f) v v' -> sel (fst v') (RetVar f) = fact_w (sel (fst v) "n") /\ snd v' == snd v.
  intros.
  eapply strengthen_runsto with (env_ax := (from_bedrock_label_map (Labels stn), change_fs fs stn)) in H0.
  eapply body_runsto'; eauto.
  eapply change_fs_agree; eauto.
  eapply change_fs_strengthen; eauto.
  eapply body_safe'; eauto.
  eapply change_fs_agree; eauto.
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
  apply is_state_out'''''.
  NoDup.
  NoDup.
  NoDup.
  eauto.
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
