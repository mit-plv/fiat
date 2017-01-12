Require Export Coq.FSets.FMapInterface.
Require Import Fiat.Common.Wf.
Require Export Fiat.Common.FMapExtensions.
Require Export Fiat.Common.FMapExtensions.LiftRelationInstances.
Require Import Fiat.Common.

Module FMapExtensionsWf_fun (E: DecidableType) (Import M: WSfun E).
  Module LiftRelationInstancesExtensions := FMapExtensionsLiftRelationInstances_fun E M.
  Include LiftRelationInstancesExtensions.

  Section rel.
    Context {A} (eqb leb : A -> A -> bool).

    Let ltb x y := (leb x y && negb (eqb x y)).
    Let gtb := flip ltb.

    Context (well_founded_gt : well_founded gtb).
    Context (top : A) (top_top : forall x, leb x top)
            (top_eqb : forall x, leb top x -> eqb top x)
            (eqb_Equivalence : Equivalence eqb).
            (*eqb_bl : forall x y, eqb x y -> x = y)
            (eqb_lb : forall x y, x = y -> eqb x y*)

    Definition lift_leb := lift_brelation leb top.
    Definition lift_eqb := lift_brelation eqb top.
    Definition lift_ltb x y
      := lift_leb x y && negb (lift_eqb x y).

    Global Instance lift_ltb_Proper_Equal
      : Proper (@Equal _ ==> @Equal _ ==> eq) lift_ltb | 5.
    Proof.
      unfold lift_ltb.
      intros ?? H ?? H'.
      rewrite H, H'.
      reflexivity.
    Qed.

    Global Instance lift_ltb_Proper_lift_eqb
           {HR : Reflexive eqb}
           {Hsub : subrelation eqb leb}
           {leb_Proper : Proper (eqb ==> eqb ==> eq) leb}
           {eqb_Proper : Proper (eqb ==> eqb ==> eq) eqb}
      : Proper (lift_eqb ==> lift_eqb ==> eq) lift_ltb.
    Proof.
      unfold lift_ltb.
      intros ?? H ?? H'.
      rewrite H, H'.
      reflexivity.
    Qed.

    Global Instance lift_ltb_Irreflexive : Irreflexive lift_ltb | 5.
    Proof.
      unfold lift_ltb; intro x; hnf.
      rewrite (reflexivity (R:=lift_eqb) x).
      edestruct lift_leb; simpl; congruence.
    Qed.
    Lemma lift_ltb_Irreflexiveb : forall x y, lift_eqb x y -> lift_ltb x y = false.
    Proof.
      unfold is_true, lift_ltb; intros x y H; rewrite H.
      edestruct lift_leb; simpl; congruence.
    Qed.

    Lemma empty_ltb_nothing v : lift_ltb (empty _) v = false.
    Proof.
      unfold lift_ltb.
      apply not_true_iff_false, BoolFacts.not_andb_negb_iff.
      unfold lift_leb, lift_eqb.
      setoid_rewrite lift_brelation_iff.
      intros H k; specialize (H k).
      rewrite empty_o in *.
      edestruct find; [ | reflexivity ].
      apply top_eqb; assumption.
    Qed.

    Section wf.
      Let to_function (m : t A) : key -> A :=
        fun k => find_default top k m.
      Let keys_of (m : t A) : list key := List.map (@fst _ _) (elements m).

      Lemma is_finite_for_keys (m : t A) : is_finite_forA eqb top E.eq to_function (keys_of m) m.
      Proof.
        unfold is_finite_forA, is_finite_forA', keys_of, to_function, find_default.
        intro k.
        rewrite InA_alt.
        setoid_rewrite in_map_iff.
        intro H.
        destruct (find k m) eqn:Hfind; simpl; [ | reflexivity ].
        apply elements_iff_find in Hfind.
        rewrite InA_alt in Hfind.
        destruct Hfind as [kv [[? ?] ?]]; simpl in *; subst.
        exfalso; apply H.
        intuition eauto.
      Qed.

      Lemma well_founded_lift_gtb
            {leb_Reflexive : Reflexive leb}
            {leb_Proper : Proper (eqb ==> eqb ==> eq) leb}
            {eqb_Proper : Proper (eqb ==> eqb ==> eq) eqb}
        : well_founded (Basics.flip lift_ltb).
      Proof.
        intro a.
        eapply Acc_subrelation.
        { eapply function_relationA_of_Acc;
          [ .. | eexact well_founded_gt | | eapply is_finite_for_keys ];
          [ try exact _.. ];
          [ repeat match goal with
                               | [ |- is_true (?R ?x ?x) ] => reflexivity
                   | _ => progress unfold gtb, ltb, flip, impl in *
                   | _ => intro
                   | _ => progress subst
                   | _ => assumption
                   | [ H : is_true (eqb ?x ?y) |- _ ]
                     => rewrite H in *; clear x H
                   end..
          | | ].
          { simpl; unfold gtb, flip, ltb in *.
            intro x; rewrite top_top; simpl.
            destruct (eqb x top) eqn:Heqb; [ left | right; reflexivity ].
            fold_is_true.
            rewrite Heqb; reflexivity. }
          { unfold to_function, find_default.
            intros ???? H.
            rewrite !(find_o _ H).
            trivial. } }
        { unfold gtb, flip; intros x y _ H.
          unfold lift_ltb in H.
          apply andb_true_iff in H.
          destruct H as [H0 H1].
          unfold function_relation.
          split; [ clear H1 | clear H0 ].
          { unfold to_function, lift_leb, find_default, ltb in *.
            setoid_rewrite lift_brelation_iff in H0.
            intro k; specialize (H0 k).
            do 2 edestruct find;
              repeat match goal with
                     | _ => progress simpl in *
                     | _ => left; congruence
                     | _ => right; reflexivity
                     | [ |- context[eqb ?x ?y] ] => destruct (eqb x y) eqn:?
                     | [ H : context[?x = true] |- _ ] => change (is_true x) in H
                     | [ H : is_true ?x, H' : context[?x] |- _ ] => rewrite H in H'
                     | [ H : is_true ?x |- context[?x] ] => rewrite H
                     | [ H : is_true (eqb ?x ?y) |- _ ]
                       => rewrite H in *; clear x H
                     | [ H : is_true (eqb ?x ?y) |- _ ]
                       => rewrite <- H in *; clear y H
                     | [ H : context[eqb ?x ?x] |- _ ]
                     => replace (eqb x x) with true
                       in H
                       by (symmetry; change (is_true (eqb x x)); reflexivity)                     end. }
          { unfold lift_eqb, to_function, find_default in *.
            apply negb_true_iff in H1.
            rewrite lift_brelation_iff_false in H1.
            destruct H1 as [k H1]; exists k.
            do 2 edestruct find;
              repeat match goal with
                     | _ => progress simpl in *
                     | _ => progress subst
                     | _ => congruence
                     | _ => intro
                     | [ H : is_true (eqb ?x ?y) |- _ ]
                       => rewrite H in *; clear x H
                     | [ H : is_true (eqb ?x ?y) |- _ ]
                       => rewrite <- H in *; clear y H
                     | [ H : context[eqb ?x ?x] |- _ ]
                       => replace (eqb x x) with true
                         in H
                         by (symmetry; change (is_true (eqb x x)); reflexivity)
                   end. } }
      Qed.
    End wf.
  End rel.
End FMapExtensionsWf_fun.

Module FMapExtensionsWf (M: WS) := FMapExtensionsWf_fun M.E M.
