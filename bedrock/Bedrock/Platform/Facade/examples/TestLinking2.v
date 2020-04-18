Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.QsRepInv.

Require Import Bedrock.Platform.Facade.DFacadeToBedrock2.

Module Import M := DFacadeToBedrock2.Make QsADTs.Adt QsRepInv.Ri.

Require Import AxSpec.

Definition export : AxiomaticSpec ADTValue.
  refine 
    ({|
        PreCond := fun _ => False;
        PostCond := fun _ ret => exists w, ret = SCA _ w
      |}).
  unfold type_conforming; intros; openhyp; subst; try reflexivity.
  intuition.
Defined.    

Definition exports := StringMapFacts.of_list (("foo", export) :: nil).

Require Import DFModule.
Require Import DFacade.

Definition foo : DFFun :=
  {|
    Core := 
      {|
        ArgVars := nil ;
        RetVar := "ret";
        Body := DFacade.Assign "ret" (Const $0);
        args_no_dup := eq_refl;
        ret_not_in_args := eq_refl;
        no_assign_to_args := eq_refl;
        args_name_ok := eq_refl;
        ret_name_ok := eq_refl;
        syntax_ok := eq_refl
      |};
    compiled_syntax_ok := eq_refl
  |}.

Definition funs := StringMapFacts.of_list (("foo", foo) :: nil).
Definition imports := GLabelMapFacts.of_list (
                          (("ADT", "Tuple_new"), Tuple_new) ::
                          (("ADT", "TupleList_empty"), TupleList_empty) ::
                          nil).

Definition exam : DFModule ADTValue :=
  {|
      Imports := imports;
      Funs := funs;
      import_module_names_good := eq_refl 
  |}.

Require Import Bedrock.Platform.Facade.CompileUnit2.

Definition input : CompileUnit exports.
  refine (@Build_CompileUnit _ exports exam "exam" "internal" eq_refl eq_refl eq_refl eq_refl _).
  simpl.
  unfold funs.
  simpl.
  unfold ops_refines_axs.
  unfold exports.
  Require Import Bedrock.Platform.Cito.StringMap.
  Import StringMap.
  Require Import Bedrock.Platform.Cito.StringMapFacts.
  Import FMapNotations.
  intros x ax Hx.
  eapply find_mapsto_iff in Hx.
  eapply MapsTo_to_map_elim in Hx.
  Focus 2.
  {
    unfold WFacts.NoDupKey.
    econstructor; intuition.
    inversion H.
  }
  Unfocus.
  inversion Hx; subst; try intuition.
  Require Import GeneralTactics4.
  inject H.
  eexists.
  split.
  {
    reflexivity.
  }
  simpl.
  unfold op_refines_ax.
  simpl.
  split.
  {
    exists false.
    intros; eauto.
  }
  split.
  {
    intuition.
  }
  split.
  {
    intros.
    unfold AxSafe in *.
    openhyp.
    simpl in *.
    intuition.
  }
  {
    intros.
    unfold AxSafe in *.
    openhyp.
    simpl in *.
    intuition.
  }
Defined.

Import CompileOut2Make.

Definition output := compile input.
Definition m1 := bedrock_module output.
Definition m1_ok := bedrock_module_ok output.
Definition m2 := bedrock_module_impl output.
Definition m2_ok := bedrock_module_impl_ok output.

(* link together the two modules contained in CompileOut *)
Definition all1 := link m1 m2.

Lemma all1_ok : moduleOk all1.
  link m1_ok m2_ok.
Qed.

Require Import Bedrock.Platform.Facade.examples.QsImpl.

(* link all1 with the ADT implementation *)
Definition all := link all1 QsImpl.m.

Theorem all_ok : moduleOk all.
  link all1_ok QsImpl.ok.
Qed.
