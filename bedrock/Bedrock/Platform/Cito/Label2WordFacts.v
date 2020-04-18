Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Label2Word.

Require Import Bedrock.Memory Bedrock.Word.
Require Import Bedrock.Platform.Cito.GLabel Bedrock.Platform.Cito.ConvertLabel.

Require Import Bedrock.Platform.Cito.GLabelMap.
Import GLabelMap.
Require Import Bedrock.Platform.Cito.GLabelMapFacts.

Require Import Bedrock.Platform.Cito.Option.
Require Import Bedrock.Platform.Cito.ListFacts1.

Require Import Bedrock.Platform.Cito.GeneralTactics.

Lemma find_by_word_elements_elim A l2w d p (v : A) : find_by_word l2w (elements d) p = Some v -> exists lbl : glabel, find lbl d = Some v /\ l2w lbl = Some p.
Proof.
  intros e.
  unfold find_by_word in *.
  destruct (option_dec (List.find (is_label_map_to_word' l2w p) (elements d))).
  {
    destruct s.
    destruct x.
    rewrite e0 in e.
    injection e; intros.
    subst.
    eapply find_spec in e0.
    openhyp.
    unfold is_label_map_to_word', is_label_map_to_word in *.
    simpl in *.
    destruct (option_dec (l2w g)).
    {
      destruct s.
      rewrite e0 in H.
      destruct (weq p x).
      {
        subst.
        exists g.
        split.
        {
          eapply In_find_Some; eauto.
          eapply InA_eqke_In; intuition.
        }
        intuition.
      }
      discriminate.
    }
    rewrite e0 in H; discriminate.
  }
  rewrite e0 in e; discriminate.
Qed.

Lemma find_by_word_elements_intro A l2w (lbl : glabel) p d (v : A) : l2w lbl = Some p -> stn_injective (fun k => In k d) l2w -> find lbl d = Some v -> find_by_word l2w (elements d) p = Some v.
Proof.
  intros H0 HH H.
  rename lbl into x.
  unfold find_by_word in *.
  destruct (option_dec (List.find (is_label_map_to_word' l2w p)
                                  (elements d))) in *.
  {
    destruct s.
    rewrite e.
    destruct x0; simpl in *.
    eapply find_spec in e.
    openhyp.
    unfold is_label_map_to_word' in *.
    unfold is_label_map_to_word in *; simpl in *.
    destruct (option_dec (l2w g)).
    {
      destruct s.
      rewrite e in H1.
      destruct (weq p x0).
      {
        subst.
        eapply InA_eqke_In in H2.
        eapply elements_mapsto_iff in H2.
        assert (g = x).
        {
          eapply HH; eauto.
          eapply MapsTo_In; eauto.
          eapply MapsTo_In; eauto.
          eapply find_mapsto_iff; eauto.
        }
        subst.
        eapply find_mapsto_iff in H2.
        congruence.
      }
      discriminate.
    }
    rewrite e in H1; discriminate.
  }
  eapply find_spec_None in e.
  contradict e.
  eexists; split.
  {
    eapply InA_eqke_In.
    eapply elements_1.
    eapply find_mapsto_iff; eauto.
  }
  unfold is_label_map_to_word' in *.
  unfold is_label_map_to_word in *; simpl in *.
  rewrite H0.
  destruct (weq p p); intuition.
Qed.
