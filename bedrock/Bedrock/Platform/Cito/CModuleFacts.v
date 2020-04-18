Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.CModule.
Require Import Bedrock.Platform.Cito.GoodModuleDec.
Require Import Bedrock.Platform.Cito.GoodModule.
Require Import Bedrock.Platform.Cito.GoodFunction.
Require Import Bedrock.Platform.Cito.GoodModuleDecFacts.

Definition cfun_to_gfun (name : string) (f : CFun) : GoodFunction.
  refine (Build_GoodFunction (Build_Func name f) _).
  destruct f; simpl in *.
  eapply is_good_func_sound; eauto.
Defined.

Require Import Bedrock.Platform.Cito.StringMap.
Require Import Bedrock.Platform.Cito.StringMapFacts.

Definition cfuns_to_gfuns (fs : StringMap.t CFun) : list GoodFunction := List.map (uncurry cfun_to_gfun) (StringMap.elements fs).

Require Import Bedrock.Platform.Cito.NameDecoration.

Lemma cfuns_to_gfuns_nodup fs : NoDup (List.map (fun (f : GoodFunction) => SyntaxFunc.Name f) (cfuns_to_gfuns fs)).
Proof.
  unfold cfuns_to_gfuns.
  rewrite map_map.
  simpl.
  eapply NoDup_elements; eauto.
Qed.

Definition cmodule_to_gmodule name (H : is_good_module_name name = true) (m : CModule) : GoodModule.GoodModule.
  refine (@Build_GoodModule name _ (cfuns_to_gfuns (Funs m)) _).
  eapply is_good_module_name_sound; eauto.
  eapply cfuns_to_gfuns_nodup.
Defined.
Require Import Bedrock.Platform.Cito.GoodModuleDecFacts.

Lemma NoDup_ArgVars (f : CFun) : NoDup (ArgVars f).
Proof.
  destruct f; simpl.
  eapply is_good_func_sound in good_func.
  destruct good_func.
  eauto.
  eapply ListFacts3.is_no_dup_sound; eauto.
Qed.
