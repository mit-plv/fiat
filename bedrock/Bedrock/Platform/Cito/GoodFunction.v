Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.GoodFunc.
Require Import Bedrock.Platform.Cito.SyntaxFunc.
Export SyntaxFunc.

Record GoodFunction :=
  {
    Fun : Func;
    IsGoodFunc : GoodFunc Fun
  }.

Coercion Fun : GoodFunction >-> Func.

Definition to_good_function (f : Func) : GoodFunc f -> GoodFunction.
  intros.
  econstructor.
  eauto.
Defined.

Lemma to_good_function_fun : forall (f : Func) (H : GoodFunc f), Fun (to_good_function f H) = f.
  eauto.
Qed.

Lemma to_good_function_name : forall (f : Func) (H : GoodFunc f), Name (to_good_function f H) = Name f.
  eauto.
Qed.

Lemma to_func_good : forall (f : GoodFunction), GoodFunc f.
  intros; destruct f; eauto.
Qed.

Require Import Bedrock.Platform.Cito.Semantics.

Definition to_internal_func_spec (f : GoodFunction) : InternalFuncSpec :=
  {|
    Semantics.Fun := f;
    Semantics.NoDupArgVars := proj1 (IsGoodFunc f)
  |}.

Coercion to_internal_func_spec : GoodFunction >-> InternalFuncSpec.
