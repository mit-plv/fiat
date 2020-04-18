Set Implicit Arguments.

Require Import Bedrock.Platform.Facade.CompileRunsTo.

Require Import Bedrock.Platform.Facade.Facade.
Require Import Bedrock.Memory Bedrock.IL.
Require Import Bedrock.Platform.Cito.GLabel.

Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Bedrock.Platform.Cito.StringMap.
Import StringMap.
Require Import Bedrock.Platform.Cito.StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.
Require Import Coq.Lists.List.
Require Import Bedrock.ListFacts Bedrock.Platform.Cito.ListFacts2 Bedrock.Platform.Cito.ListFacts3 Bedrock.Platform.Cito.ListFacts5 Bedrock.Platform.Cito.ListFacts4.
Local Open Scope list_scope.
Require Import Bedrock.Platform.Cito.GeneralTactics Bedrock.Platform.Cito.GeneralTactics2 Bedrock.Platform.Cito.GeneralTactics3 Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Platform.Cito.Option.

Section ADTValue.

  Variable ADTValue : Type.

  Notation RunsTo := (@RunsTo ADTValue).
  Notation State := (@State ADTValue).
  Notation Env := (@Env ADTValue).
  Notation AxiomaticSpec := (@AxiomaticSpec ADTValue).
  Notation Value := (@Value ADTValue).
  Notation Sca := (@SCA ADTValue).
  Notation Adt := (@ADT ADTValue).

  Require Import Bedrock.Platform.Cito.WordMap.
  Import WordMap.
  Require Import Bedrock.Platform.Cito.WordMapFacts.
  Import FMapNotations.
  Local Open Scope fmap_scope.

  Require Import Bedrock.Platform.Facade.FacadeFacts.

  Notation CitoSafe := (@Semantics.Safe ADTValue).

  Ltac pick_related := try match goal with | |- related _ _ => eauto end.

  Hint Constructors NoDup.

  Lemma mapM_good_inputs args :
    forall words cinput input h h2 (st : State) vs,
      mapM (sel st) args = Some input ->
      cinput = input ->
      words = List.map vs args ->
      h2 <= h ->
      related st (vs, h2) ->
      NoDup args ->
      Semantics.good_inputs h (combine words cinput).
  Proof.
    simpl; induction args; destruct words; destruct cinput; destruct input; try solve [simpl in *; intros; eauto; try discriminate]; unfold Semantics.good_inputs, Semantics.disjoint_ptrs in *.
    - simpl in *.
      intros.
      intuition.
    - simpl in *.
      intros.
      intuition.
    - simpl in *.
      rename a into x.
      rename v into cv.
      rename v0 into v.
      intros h h2 st vs Hmm Hcin Hw Hsm Hr Hnd.
      destruct (option_dec (sel st x)) as [[y Hy] | Hn].
      + rewrite Hy in *.
        destruct (option_dec (mapM (sel st) args)) as [[ys Hys] | Hn].
        * rewrite Hys in *.
          inject Hmm.
          inject Hcin.
          inject Hw.
          inversion Hnd; subst.
          rename H1 into Hni.
          rename H2 into Hnd2.
          destruct v as [w | a]; simpl in *.
          {
            split.
            - econstructor.
              + unfold Semantics.word_adt_match.
                simpl.
                eapply Hr in Hy; simpl in *.
                eauto.
              + eapply IHargs; eauto.
            - eapply IHargs; eauto.
          }
          {
            split.
            - econstructor.
              + unfold Semantics.word_adt_match.
                simpl.
                eapply Hr in Hy; simpl in *.
                eauto.
              + eapply IHargs; eauto.
            - econstructor.
              + nintro.
                contradict Hni.
                eapply in_map_iff in H.
                destruct H as [[w cv] [Hw Hin]]; simpl in *.
                subst.
                eapply filter_In in Hin.
                destruct Hin as [Hin Hadt]; simpl in *.
                eapply is_adt_iff in Hadt.
                destruct Hadt as [a' Hcv].
                subst.
                eapply in_nth_error in Hin.
                destruct Hin as [i Hnc].
                eapply nth_error_combine_elim in Hnc.
                destruct Hnc as [Hia Hii].
                eapply nth_error_map_elim in Hia.
                destruct Hia as [x' [Hia Hvs]].
                eapply mapM_nth_error_1 in Hys; eauto.
                destruct Hys as [v [Hii' Hx']].
                unif v.
                assert (x = x').
                {
                  eapply related_no_alias; eauto.
                }
                subst.
                eapply Locals.nth_error_In; eauto.
              + eapply IHargs; eauto.
          }
        * rewrite Hn in *; discriminate.
      + rewrite Hn in *; discriminate.
  Qed.

  Require Import Bedrock.Platform.Facade.Compile.

  Require Import Bedrock.Platform.Cito.GeneralTactics5. Require Import Bedrock.Platform.Cito.SemanticsFacts8.

  Theorem compile_safe :
    forall s_env s s_st,
      Safe s_env s s_st ->
      (* h1 : the heap portion that this program is allowed to change *)
      forall vs h h1,
        h1 <= h ->
        related s_st (vs, h1) ->
        forall t_env,
          cenv_impls_env t_env s_env ->
          let t := compile s in
          let t_st := (vs, h) in
          CitoSafe t_env t t_st.
  Proof.
    simpl; intros.
    rename H2 into Henv.
    eapply
      (Semantics.Safe_coind
         (fun t v =>
            exists s s_st h1,
              let vs := fst v in
              let h := snd v in
              Safe s_env s s_st /\
              h1 <= h /\
              related s_st (vs, h1) /\
              t = compile s)
      ); [ .. | repeat try_eexists; simpl in *; intuition eauto ]; generalize Henv; clear; intros Henv; simpl; intros until v; destruct v as [vs h]; intros [s [s_st [h1 [Hsf [Hsm [Hr Hcomp]]]]]]; destruct s; simpl in *; try discriminate; inject Hcomp.

    (* seq *)
    {
      rename s1 into a.
      rename s2 into b.
      inversion Hsf; subst.
      destruct H2 as [Hsfa Hsfb].
      split.
      - exists a, s_st, h1; eauto.
      - intros [vs' h'] Hcrt; simpl in *.
        eapply compile_runsto in Hcrt; eauto.
        simpl in *.
        openhyp.
        repeat eexists_split; pick_related; eauto.
        eapply diff_submap.
    }

    (* if *)
    {
      rename e into cond.
      rename s1 into t.
      rename s2 into f.
      inversion Hsf; subst.
      - left.
        rename H3 into Hcond.
        rename H4 into Hsfbr.
        split.
        + eapply eval_bool_wneb; eauto.
        + repeat eexists_split; pick_related; eauto.
      - right.
        rename H3 into Hcond.
        rename H4 into Hsfbr.
        split.
        + eapply eval_bool_wneb; eauto.
        + repeat eexists_split; pick_related; eauto.
    }

    (* while *)
    {
      rename e into cond.
      rename s into body.
      inversion Hsf; unfold_all; subst.
      - left.
        rename H1 into Hcond.
        rename H2 into Hsfbody.
        rename H4 into Hsfk.
        repeat try_split.
        + eapply eval_bool_wneb; eauto.
        + repeat eexists_split; pick_related; eauto.
        + intros [vs' h'] Hcrt; simpl in *.
          eapply compile_runsto in Hcrt; eauto.
          simpl in *.
          openhyp.
          repeat eexists_split; pick_related; eauto.
          eapply diff_submap.
      - right.
        eapply eval_bool_wneb; eauto.
    }

    (* call *)
    {
      rename s into x.
      rename e into f_e.
      rename l into args.
      inversion Hsf; unfold_all; subst.
      (* axiomatic *)
      {
        right.
        rename H2 into Hnd.
        rename H3 into Hfe.
        rename H4 into Hfw.
        rename H5 into Hmm.
        rename H7 into Hna.
        rename H8 into Hpre.
        destruct spec; simpl in *.
        rewrite map_map.
        simpl.
        set (words := List.map (fun x0 : string => vs x0) args) in *.
        eapply Henv in Hfw.
        eexists.
        exists (combine words input).
        repeat eexists_split.
        {
          eapply eval_ceval in Hfe; eauto.
          rewrite Hfe.
          rewrite Hfw.
          simpl.
          eauto.
        }
        {
          rewrite map_fst_combine.
          eauto.
          unfold_all.
          repeat rewrite map_length.
          eapply mapM_length; eauto.
        }
        {
          eapply mapM_good_inputs; unfold_all; eauto.
        }
        {
          simpl in *.
          rewrite map_snd_combine.
          eauto.
          unfold_all.
          repeat rewrite map_length.
          eapply mapM_length; eauto.
        }
      }
      (* opereational *)
      {
        left.
        rename H2 into Hnd.
        rename H3 into Hfe.
        rename H4 into Hfw.
        rename H5 into Hl.
        rename H6 into Hmm.
        rename H7 into Hna.
        rename H9 into Hsfb.
        rename H10 into Hnl.
        destruct spec; simpl in *.
        eapply Henv in Hfw.
        repeat eexists_split.
        {
          eapply eval_ceval in Hfe; eauto.
          rewrite Hfe.
          rewrite Hfw.
          simpl.
          eauto.
        }
        {
          simpl in *.
          rewrite map_length.
          symmetry; eauto.
        }
        {
          simpl in *.
          intros vs_arg Hm.
          rewrite map_map in Hm.
          eapply reachable_submap_related in Hr; eauto.
          destruct Hr as [Hsm2 Hr].
          repeat eexists_split.
          - eauto.
          -
            instantiate (1 := reachable_heap vs args input).
            eapply submap_trans; eauto.
          - eapply change_var_names; eauto.
            eapply is_no_dup_sound; eauto.
            eapply mapM_length; eauto.
          - eauto.
        }
      }
    }

    (* label *)
    {
      rename s into x.
      rename g into lbl.
      inversion Hsf; unfold_all; subst.
      rename H1 into Hlbl2.
      eapply Henv in Hlbl2.
      intuition.
      rewrite H in Hlbl2.
      discriminate.
    }

  Qed.

End ADTValue.
