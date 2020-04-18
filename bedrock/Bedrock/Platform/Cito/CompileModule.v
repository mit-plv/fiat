Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.
Require Import Bedrock.Platform.Cito.RepInv.

Module Make (Import E : ADT) (Import M : RepInv E).

  Require Import Bedrock.Platform.Cito.CompileFunc.
  Module Import CompileFuncMake := Make E M.
  Import CompileFuncImplMake.
  Require Import Bedrock.Platform.Cito.GoodOptimizer.
  Import GoodOptimizerMake.

  Require Import Bedrock.Platform.Cito.GoodFunc.

  Require Import Coq.Lists.List.
  Require Import Bedrock.Platform.Cito.GoodModule.
  Require Import Bedrock.StructuredModule.
  Require Import Bedrock.Platform.Cito.NameDecoration.
  Require Import Bedrock.Platform.Cito.GoodFunction.
  Require Import Bedrock.Structured.
  Require Import Bedrock.Platform.Wrap.
  Require Import Bedrock.Platform.Cito.NameVC.

  Section TopSection.

    Variable module : GoodModule.

    Definition imports : list import := nil.

    Variable optimizer : Optimizer.

    Hypothesis good_optimizer : GoodOptimizer optimizer.

    Definition mod_name := impl_module_name (GoodModule.Name module).

    Definition compile_func' (f : Func) (good_func : GoodFunc f) := CompileFuncMake.compile mod_name f good_func good_optimizer.

    Definition compile_func (f : GoodFunction) := compile_func' f (to_func_good f).

    Definition compiled_funcs := map compile_func (Functions module).

    Lemma good_vcs : forall ls, vcs (makeVcs imports compiled_funcs (map compile_func ls)).
      induction ls; simpl; eauto; destruct a; simpl; unfold CompileFuncSpecMake.imply; wrap0.
    Qed.

    Definition compile := StructuredModule.bmodule_ imports compiled_funcs.

    Lemma module_name_not_in_imports : NameNotInImports mod_name imports.
      unfold NameNotInImports; eauto.
    Qed.

    Lemma no_dup_func_names : NoDupFuncNames compiled_funcs.
      eapply NoDup_NoDupFuncNames.
      unfold compiled_funcs.
      erewrite map_map.
      unfold compile_func.
      unfold compile_func'.
      unfold CompileFuncMake.compile; simpl.
      destruct module; simpl.
      eauto.
    Qed.

    Theorem compileOk : XCAP.moduleOk compile.
      eapply bmoduleOk.
      eapply module_name_not_in_imports.
      eapply no_dup_func_names.
      eapply good_vcs.
    Qed.

  End TopSection.

End Make.
