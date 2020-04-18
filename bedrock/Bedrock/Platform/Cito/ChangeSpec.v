Set Implicit Arguments.

Section ADTValue.

  Variable ADTValue : Type.

  Require Import Bedrock.Platform.Cito.SemanticsFacts4.
  Require Import Bedrock.Platform.Cito.ProgramLogic2.
  Require Import Bedrock.Platform.Cito.Transit.
  Require Import Bedrock.Platform.Cito.Semantics.

  Require Import Bedrock.Platform.Cito.GLabel.
  Require Import Bedrock.Platform.Cito.GLabelMap.
  Import GLabelMap.
  Require Import Bedrock.Platform.Cito.GLabelMapFacts.

  Notation Internal := (@Internal ADTValue).

  Definition strengthen_specs specs_op specs_ax env_ax :=
    forall (lbl : glabel),
      find lbl specs_op = find lbl specs_ax \/
      exists spec_op spec_ax,
        find lbl specs_op = Some (Internal spec_op) /\
        find lbl specs_ax = Some (Foreign spec_ax) /\
        strengthen_op_ax spec_op spec_ax env_ax.

  Require Import Bedrock.Platform.Cito.GeneralTactics Bedrock.Platform.Cito.GeneralTactics2.
  Require Import Bedrock.Platform.Cito.Option.

  Lemma strengthen_specs_strengthen : forall specs_op specs_ax env_op env_ax, strengthen_specs specs_op specs_ax env_ax -> specs_env_agree specs_op env_op -> specs_env_agree specs_ax env_ax -> (forall lbl, fst env_op lbl = fst env_ax lbl) -> strengthen env_op env_ax.
  Proof.
    split; intros.
    eauto.
    destruct (option_dec (fs_op w)).
    destruct s.
    generalize e; intro.
    eapply H0 in e.
    openhyp.
    edestruct (H x0).
    left.
    rewrite e0.
    symmetry.
    eapply H1.
    rewrite H5 in H4; clear H5.
    descend; eauto.
    rewrite <- H2.
    eauto.

    openhyp.
    rewrite H5 in H4; injection H4; intros; subst.
    assert (fs_ax w = Some (Foreign x2)).
    eapply H1.
    descend; eauto.
    rewrite <- H2; eauto.
    right; descend; eauto.

    destruct (option_dec (fs_ax w)).
    destruct s.
    generalize e0; intro.
    eapply H1 in e0.
    openhyp.
    edestruct (H x0).
    assert (fs_op w = Some x).
    eapply H0.
    descend; eauto.
    rewrite H2; eauto.
    rewrite H5.
    eauto.
    rewrite H6 in e; intuition.
    openhyp.
    assert (fs_op w = Some (Internal x1)).
    eapply H0.
    descend; eauto.
    rewrite H2; eauto.
    rewrite H8 in e; intuition.
    left; congruence.
  Qed.

  Notation Foreign := (@Foreign ADTValue).

  Definition apply_specs_diff specs specs_diff := update specs (map Foreign specs_diff).

  Definition strengthen_diff_f specs env_ax k v a :=
    a /\
    (find k specs = Some (Foreign v) \/
     exists op,
       find k specs = Some (Internal op) /\
       strengthen_op_ax op v env_ax).

  Definition strengthen_diff specs specs_diff env_ax :=
    fold (strengthen_diff_f specs env_ax) specs_diff True.

  Lemma strengthen_diff_intro : forall specs_diff env_ax specs, (forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax) -> strengthen_diff specs specs_diff env_ax.
  Proof.
    do 3 intro.
    (* intros Hforall. *)
    (* unfold strengthen_diff. *)
    eapply fold_rec_bis with (P := fun specs_diff (H : Prop) => (forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax) -> H); simpl.
    intros m m' a Heqm Ha Hforall.
    { 
      eapply Ha.
      intros lbl ax Hfind.
      rewrite Heqm in Hfind.
      eauto.
    }
    { eauto. }
    intros k e a m' Hmapsto Hnin Ha Hforall.
    unfold strengthen_diff_f.
    split.
    {
      eapply Ha.
      intros lbl ax Hfind.
      eapply Hforall.
      eapply find_mapsto_iff.
      eapply add_mapsto_iff.
      right.
      split.
      {
        intro Heq; subst.
        contradict Hnin.
        eapply MapsTo_In.
        eapply find_mapsto_iff.
        eauto.
      }
      eapply find_mapsto_iff.
      eauto.
    }
    eapply Hforall.
    eapply find_mapsto_iff.
    eapply add_mapsto_iff.
    left.
    eauto.
  Qed.

  Lemma strengthen_diff_elim : forall specs_diff env_ax specs, strengthen_diff specs specs_diff env_ax -> forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax.
    do 3 intro.
    eapply fold_rec_bis with (P := fun specs_diff (H : Prop) => H -> forall lbl ax, find lbl specs_diff = Some ax -> find lbl specs = Some (Foreign ax) \/ exists op, find lbl specs = Some (Internal op) /\ strengthen_op_ax op ax env_ax); simpl; intros.
    eapply H0; eauto.
    rewrite H; eauto.
    rewrite empty_o in H0; intuition.
    eapply find_mapsto_iff in H3.
    eapply add_mapsto_iff in H3.
    openhyp.
    subst.
    destruct H2.
    openhyp.
    eauto.
    right; descend; eauto.
    eapply H1.
    destruct H2; eauto.
    eapply find_mapsto_iff; eauto.
  Qed.

  Lemma strengthen_diff_strengthen_specs : forall specs specs_diff env_ax, strengthen_diff specs specs_diff env_ax -> strengthen_specs specs (apply_specs_diff specs specs_diff) env_ax.
    intros.
    unfold strengthen_specs.
    intros.
    destruct (option_dec (find lbl specs_diff)).
    destruct s.
    eapply strengthen_diff_elim in H; eauto.
    openhyp.
    left.
    rewrite H.
    symmetry.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    left.
    eapply find_mapsto_iff.
    rewrite map_o.
    rewrite e.
    eauto.
    right; descend; eauto.
    eapply find_mapsto_iff.
    eapply update_mapsto_iff.
    left.
    eapply find_mapsto_iff.
    rewrite map_o.
    rewrite e.
    eauto.
    left.
    unfold apply_specs_diff.
    rewrite update_o_1; eauto.
    nintro.
    eapply map_4 in H0.
    eapply In_find_not_None in H0.
    erewrite e in H0.
    intuition.
  Qed.

  Lemma strengthen_diff_strenghthen : forall specs specs_diff env_op env_ax, strengthen_diff specs specs_diff env_ax -> specs_env_agree specs env_op -> specs_env_agree (apply_specs_diff specs specs_diff) env_ax -> (forall lbl, fst env_op lbl = fst env_ax lbl) -> strengthen env_op env_ax.
    intros.
    eapply strengthen_specs_strengthen; eauto.
    eapply strengthen_diff_strengthen_specs; eauto.
  Qed.

  Notation Callee := (@Callee ADTValue).

  Definition is_pointer_of_label specs (stn : glabel -> option W) w : option Callee :=
    fold (fun k v res =>
            match res with
              | Some _ => res
              | None =>
                match stn k with
                  | Some w' => if weq w w' then Some v else None
                  | None => None
                end
            end
         ) specs None.

  Notation Env := (@Env ADTValue).

  Definition change_env new_specs (env : Env) : Env :=
    let stn := fst env in
    let fs := snd env in
    (stn,
     fun w =>
       match is_pointer_of_label new_specs stn w with
         | Some new_spec => Some new_spec
         | None => fs w
       end).

  Notation specs_stn_injective := (@specs_stn_injective ADTValue).

  Lemma sub_domain_specs_stn_injective : forall specs1 specs2 stn, specs_stn_injective specs1 stn -> sub_domain specs2 specs1 -> specs_stn_injective specs2 stn.
    unfold ProgramLogic2.specs_stn_injective, sub_domain; intros.
    eapply H; eauto.
  Qed.

  Lemma add_specs_stn_injective : forall specs k v stn, specs_stn_injective (add k v specs) stn -> specs_stn_injective specs stn.
    intros.
    eapply sub_domain_specs_stn_injective; eauto.
    unfold sub_domain; intros.
    eapply add_in_iff; eauto.
  Qed.

  Lemma is_pointer_of_label_intro_elim : forall specs stn w, (forall v, is_pointer_of_label specs stn w = Some v -> exists lbl, find lbl specs = Some v /\ stn lbl = Some w) /\ (forall v lbl, specs_stn_injective specs stn -> find lbl specs = Some v -> stn lbl = Some w -> is_pointer_of_label specs stn w = Some v).
    do 3 intro.
    eapply fold_rec_bis with (P := fun specs a => (forall v, a = Some v -> exists lbl, find lbl specs = Some v /\ stn lbl = Some w) /\ (forall v lbl, specs_stn_injective specs stn -> find lbl specs = Some v -> stn lbl = Some w -> a = Some v)); simpl; intros.
    unfold ProgramLogic2.specs_stn_injective in *.
    setoid_rewrite H in H0.
    eapply H0; eauto.
    split; intros.
    intuition.
    rewrite empty_o in H0; intuition.
    openhyp.
    split; intros.
    destruct a.
    injection H3; intros; subst.
    edestruct H1; eauto.
    openhyp.
    descend; eauto.
    eapply find_mapsto_iff; eapply add_mapsto_iff.
    right.
    split.
    nintro; subst.
    eapply find_mapsto_iff in H4; eapply MapsTo_In in H4.
    contradiction.
    eapply find_mapsto_iff; eauto.
    destruct (option_dec (stn k)).
    destruct s.
    rewrite e0 in *.
    destruct (weq w x).
    subst.
    injection H3; intros; subst.
    descend; eauto.
    eapply find_mapsto_iff; eapply add_mapsto_iff.
    eauto.
    intuition.
    rewrite e0 in *; intuition.
    destruct a.
    edestruct H1; eauto.
    openhyp.
    eapply find_mapsto_iff in H4; eapply find_mapsto_iff in H6.
    assert (lbl = x).
    eapply H3; eauto.
    eapply MapsTo_In; eauto.
    eapply add_in_iff; right; eapply MapsTo_In; eauto.
    subst.
    eapply add_mapsto_iff in H4; openhyp.
    subst.
    eapply MapsTo_In in H6; contradiction.
    eapply H2; eauto.
    eapply add_specs_stn_injective; eauto.
    eapply find_mapsto_iff; eauto.

    eapply find_mapsto_iff in H4.
    destruct (option_dec (stn k)).
    destruct s.
    rewrite e0 in *.
    eapply add_mapsto_iff in H4; openhyp.
    subst.
    rewrite H5 in e0; injection e0; intros; subst.
    destruct (weq x x); intuition.
    destruct (weq w x).
    subst.
    contradict H4.
    eapply H3; eauto.
    eapply add_in_iff; eauto.
    eapply add_in_iff; right; eapply MapsTo_In; eauto.
    eapply H2; eauto.
    eapply add_specs_stn_injective; eauto.
    eapply find_mapsto_iff; eauto.
    rewrite e0 in *.
    eapply add_mapsto_iff in H4; openhyp.
    subst.
    rewrite H5 in e0; intuition.
    eapply H2; eauto.
    eapply add_specs_stn_injective; eauto.
    eapply find_mapsto_iff; eauto.
  Qed.

  Lemma is_pointer_of_label_intro : forall specs stn w v lbl, specs_stn_injective specs stn -> find lbl specs = Some v -> stn lbl = Some w -> is_pointer_of_label specs stn w = Some v.
    eapply is_pointer_of_label_intro_elim; eauto.
  Qed.

  Lemma is_pointer_of_label_elim : forall specs stn w v, is_pointer_of_label specs stn w = Some v -> exists lbl, find lbl specs = Some v /\ stn lbl = Some w.
    eapply is_pointer_of_label_intro_elim; eauto.
  Qed.

  Lemma equal_domain_specs_stn_injective : forall specs1 specs2 stn, equal_domain specs1 specs2 -> (specs_stn_injective specs1 stn <-> specs_stn_injective specs2 stn).
    split; intros.
    eapply sub_domain_specs_stn_injective; eauto; eapply H.
    eapply sub_domain_specs_stn_injective; eauto; eapply H.
  Qed.
  Lemma equal_domain_sym : forall elt1 elt2 (m1 : t elt1) (m2 : t elt2), equal_domain m1 m2 -> equal_domain m2 m1.
    unfold equal_domain; intuition.
  Qed.

  Lemma change_env_agree : forall specs new_specs, equal_domain new_specs specs -> forall env, specs_env_agree specs env -> specs_env_agree new_specs (change_env new_specs env).
  Proof.
    unfold specs_env_agree.
    intros.
    openhyp.
    simpl.
    split.
    unfold labels_in_scope in *.
    intros.
    eapply H0.
    eapply H; eauto.

    split.
    eapply equal_domain_specs_stn_injective; eauto.

    unfold specs_fs_agree in *.
    split; intros.
    simpl in *.
    destruct env in *; simpl in *.
    destruct (option_dec (is_pointer_of_label new_specs o p)).
    destruct s.
    rewrite e in *.
    injection H3; intros; subst.
    eapply is_pointer_of_label_elim in e; openhyp.
    descend; eauto.
    rewrite e in *.
    eapply H2 in H3; openhyp.
    eapply find_mapsto_iff in H4; eapply MapsTo_In in H4.
    eapply H in H4.
    eapply In_MapsTo in H4; openhyp.
    assert (is_pointer_of_label new_specs o p = Some x0).
    eapply is_pointer_of_label_intro; eauto.
    eapply equal_domain_specs_stn_injective; eauto.

    eapply find_mapsto_iff; eauto.
    rewrite e in H5; intuition.
    openhyp.
    simpl in *.
    destruct env; simpl in *.
    assert (is_pointer_of_label new_specs o p = Some spec).
    eapply is_pointer_of_label_intro; eauto.
    eapply equal_domain_specs_stn_injective; eauto.
    rewrite H5; eauto.
  Qed.

  Lemma sub_domain_apply_specs_diff_equal_domain a b : sub_domain b a -> equal_domain (apply_specs_diff a b) a.
  Proof.
    unfold apply_specs_diff.
    unfold equal_domain.
    intros H.
    split.
    {
      eapply sub_domain_update_sub_domain; eauto.
      eapply sub_domain_map_1; eauto.
    }
    {
      eapply sub_domain_update_1.
      eapply sub_domain_refl.
    }
  Qed.

End ADTValue.
