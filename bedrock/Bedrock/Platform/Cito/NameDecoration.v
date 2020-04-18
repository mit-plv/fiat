Set Implicit Arguments.

Require Import Coq.Strings.String.
Local Open Scope string_scope.

Definition cito_module_impl_prefix := "__cmod_impl_".
Local Notation CMI := cito_module_impl_prefix.
Definition impl_module_name s := (CMI ++ s)%string.

Local Open Scope bool_scope.
Local Notation "! b" := (negb b) (at level 35).

Definition is_good_module_name s := ! (prefix CMI s).
Definition IsGoodModuleName (s : string) := is_good_module_name s = true.

Lemma is_good_module_name_sound : forall s, is_good_module_name s = true -> IsGoodModuleName s.
  eauto.
Qed.

Require Import Bedrock.Platform.Cito.GeneralTactics.

Lemma IsGoodModuleName_not_impl_module_name : forall s, IsGoodModuleName s -> ~ exists s', impl_module_name s' = s.
  unfold IsGoodModuleName, impl_module_name.
  intros.
  intuition.
  openhyp.
  rewrite <- H0 in *.
  simpl in *.
  destruct x; simpl in *; discriminate.
Qed.

Lemma cito_module_impl_prefix_not_empty : cito_module_impl_prefix <> "".
Proof.
  unfold cito_module_impl_prefix; discriminate.
Qed.
