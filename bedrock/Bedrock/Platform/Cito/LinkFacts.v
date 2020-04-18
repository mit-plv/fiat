Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.Semantics.
  Module Import SemanticsMake := Make E.

  Section TopSection.

    Require Import Bedrock.Platform.Cito.GoodModule.
    Require Import Bedrock.Platform.Cito.GLabelMap.
    Import GLabelMap.

    Open Scope bool_scope.
    Notation "! b" := (negb b) (at level 35).

    Require Import Coq.Arith.Compare_dec.

    Definition to_bool A B (b : {A} + {B}) := if b then true else false.

    Notation fst2 := (fun x => @fst _ _ (@fst _ _ x)).

    Require Import Bedrock.Platform.Cito.ListFacts3.
    Require Import Bedrock.Platform.Cito.NameDecoration.

    Definition GoodToLink_bool (modules : list GoodModule) (imports : t ForeignFuncSpec) :=
      let imported_module_names := List.map fst2 (elements imports) in
      let module_names := List.map Name modules in
      ! sumbool_to_bool (zerop (length modules)) &&
        is_no_dup module_names &&
        forallb (fun s => ! sumbool_to_bool (in_dec string_dec s module_names)) imported_module_names &&
        forallb is_good_module_name imported_module_names.

    Require Import Bedrock.Platform.Cito.GeneralTactics.
    Require Import Bedrock.Platform.Cito.ListFacts1.
    Require Import Bedrock.Platform.Cito.GeneralTactics.
    Require Import Coq.Bool.Bool.
    Require Import Bedrock.Platform.Cito.GLabelMapFacts.

    Lemma GoodToLink_bool_sound :
      forall modules imports,
        GoodToLink_bool modules imports = true ->
        modules <> nil /\
        List.NoDup (List.map Name modules) /\
        ListFacts1.Disjoint (List.map Name modules) (List.map fst2 (elements imports)) /\
        forall l, In l imports -> IsGoodModuleName (fst l).
    Proof.
      intros.
      unfold GoodToLink_bool in *; simpl in *.
      repeat (eapply andb_true_iff in H; openhyp).
      split.
      eapply negb_true_iff in H.
      unfold sumbool_to_bool in *.
      destruct (zerop _); intuition.
      subst; simpl in *; intuition.
      split.
      eapply is_no_dup_sound; eauto.
      split.
      unfold ListFacts1.Disjoint; intuition.
      eapply forallb_forall in H1; eauto.
      eapply negb_true_iff in H1.
      unfold sumbool_to_bool in *.
      destruct (in_dec _ _ _); intuition.
      intros.
      eapply forallb_forall in H0; eauto.
      rewrite <- map_map.
      eapply in_map.
      eapply In_fst_elements_In; eauto.
    Qed.

  End TopSection.
(*
  Require Import RepInv.

  Module Make (Import M : RepInv E).

    Require Import Link.
    Module Import LinkMake := Make E M.
    Require Import GoodOptimizer.
    Module Import GoodOptimizerMake := Make E.
    Require Import AutoSep.

    Lemma result_ok_2 :
      forall modules imports,
        GoodToLink_bool modules imports = true ->
        forall opt (opt_g: GoodOptimizer opt),
          moduleOk (result modules imports opt_g).
    Proof.
      intros.
      eapply GoodToLink_bool_sound in H.
      Require Import GeneralTactics.
      openhyp.
      eapply result_ok; eauto.
    Qed.

  End Make.
*)
End Make.
