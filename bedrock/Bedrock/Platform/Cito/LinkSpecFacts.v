Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.LinkSpec.

Section TopSection.

  Variable ADTValue : Type.

  Notation FName := SyntaxFunc.Name.
  Notation MName := GoodModule.Name.

  Require Import Bedrock.Platform.Cito.GeneralTactics.

  Lemma label_mapsto_in : forall modules imports lbl spec, @label_mapsto ADTValue modules imports lbl spec -> label_in modules imports lbl.
    unfold label_mapsto, label_in.
    intros.
    openhyp.
    left; descend; eauto.
    right; eapply MapsTo_In; eapply find_mapsto_iff; eauto.
  Qed.

  Lemma label_in_mapsto : forall modules imports lbl, @label_in ADTValue modules imports lbl -> exists spec, label_mapsto modules imports lbl spec.
    unfold label_mapsto, label_in.
    intros.
    openhyp.
    subst; simpl in *.
    descend; left; descend; eauto.
    eapply In_MapsTo in H; openhyp.
    eapply find_mapsto_iff in H.
    descend; right; descend; eauto.
  Qed.

  Definition specs_equal specs modules imports := forall lbl spec, find lbl specs = Some spec <-> @label_mapsto ADTValue modules imports lbl spec.

  Lemma specs_equal_in : forall specs modules imports, specs_equal specs modules imports -> forall lbl, In lbl specs <-> label_in modules imports lbl.
    split; intros.
    eapply In_MapsTo in H0.
    openhyp.
    eapply label_mapsto_in.
    eapply H.
    eapply find_mapsto_iff; eauto.
    eapply label_in_mapsto in H0; openhyp.
    eapply MapsTo_In.
    eapply find_mapsto_iff.
    eapply H; eauto.
  Qed.

  Require Import Bedrock.Platform.Cito.ProgramLogic2.

  Lemma specs_equal_agree : forall specs modules imports, specs_equal specs modules imports -> forall stn fs, env_good_to_use modules imports stn fs -> specs_env_agree specs (from_bedrock_label_map (Labels stn), fs stn).
    intros.
    split.

    unfold labels_in_scope.
    intros.
    unfold from_bedrock_label_map in *; simpl in *.
    eapply H0; eapply specs_equal_in; eauto.

    split.
    Focus 2.
    unfold specs_fs_agree.
    unfold from_bedrock_label_map in *; simpl in *.
    split; intros.

    eapply H0 in H1.
    destruct H1.
    destruct H1.
    descend.
    eauto.
    eapply H; eauto.

    openhyp.
    eapply H0.
    eexists.
    split.
    eauto.
    eapply H; eauto.

    unfold specs_stn_injective.
    intros.
    unfold from_bedrock_label_map in *; simpl in *.
    eapply H0; eauto.
    eapply specs_equal_in; eauto.
    eapply specs_equal_in; eauto.
  Qed.

End TopSection.
