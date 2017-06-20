Require Export Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetFacts.
Require Import Coq.MSets.MSetProperties.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.Instances.
Require Import Fiat.Common.NatFacts.
Require Import Fiat.Common.MSetExtensions.
Require Import Fiat.Common.

Module MSetBoundedLatticeOn (E: OrderedType) (Import M: SetsOn E).
  Module Import BasicFacts := WFactsOn E M.
  Module Import BasicProperties := WPropertiesOn E M.
  Module Import BasicExtensions := MSetExtensionsOn E M.

  Definition lift_ltb (x y : t) : bool
    := ((subset x y) && negb (equal x y)).

  Global Instance eq_flip_impl_flip_impl_impl_Prper
    : Proper (Logic.eq ==> flip impl ==> flip impl) impl.
  Proof. compute; intros; subst; tauto. Qed.

  Global Instance lift_ltb_Transitive : Transitive lift_ltb.
  Proof.
    unfold lift_ltb.
    intros x y z.
    setoid_rewrite andb_true_iff.
    destruct (equal x z) eqn:H;
      revert H;
      setoid_rewrite negb_true_iff;
      setoid_rewrite <- not_true_iff_false;
      to_caps;
      setoid_subst_rel Equal;
      intros; destruct_head and;
        simplify_sets;
        unfold not in *;
        specialize_by reflexivity;
        try tauto.
    split; try congruence.
    etransitivity; eassumption.
  Qed.

  Lemma not_equal_ex
        x y (H : ~Equal x y)
    : exists a, (In a x \/ In a y) /\ (In a x -> In a y -> False).
  Proof.
    revert dependent y.
    induction x as [|xs xs' IHxs v] using set_induction.
    { intro y.
      unfold Empty, Equal in *.
      setoid_rewrite (False_iff (H _)).
      destruct (choose y) as [v|] eqn:Hch.
      { setoid_rewrite_logic.
        apply choose_spec1 in Hch.
        eauto. }
      { apply choose_spec2 in Hch.
        unfold Equal, Empty in *.
        setoid_rewrite (False_iff (Hch _)).
        setoid_rewrite_logic.
        tauto. } }
    { intro y.
      let H := match goal with H : Add _ _ _ |- _ => H end in
      apply Add_Equal in H.
      setoid_subst xs'.
      setoid_rewrite add_spec.
      destruct (In_dec v y) as [pf|pf]; [ | exists v ].
      { intro Hneq.
        specialize (IHxs (remove v y)).
        setoid_rewrite remove_spec in IHxs.
        destruct IHxs as [a IHxs]; [ | exists a ].
        { intro Heq'; apply Hneq; clear Hneq.
          setoid_subst xs.
          rewrite add_remove by assumption.
          reflexivity. }
        { lazymatch type of IHxs with
          | context[E.eq ?x ?y]
            => assert (~E.eq x y) by (intro; rename x into x'; setoid_subst x'; firstorder)
          end.
          destruct_head and.
          destruct_head or; [ solve [ split; eauto ] | ].
          destruct_head and.
          let H := match goal with H : _ -> _ /\ _ -> _ |- _ => H end in
          specialize (fun a b c => H c (conj a b)).
          specialize_by assumption.
          split; eauto; [].
          firstorder. } }
      { assert (E.eq v v) by reflexivity.
        eauto. } }
  Qed.

  Definition well_founded_lift_ltb : well_founded lift_ltb.
  Proof.
    eapply well_founded_subrelation;
      [ | eexact (Wf_nat.well_founded_ltof _ cardinal) ].
    unfold Wf_nat.ltof, lift_ltb.
    intros x y H.
    apply andb_true_iff in H.
    destruct H as [H0 H1].
    apply subset_spec in H0.
    apply negb_true_iff, not_true_iff_false in H1.
    setoid_rewrite equal_spec in H1.
    destruct (not_equal_ex H1) as [a [[H2|H2] H3]];
      eapply subset_cardinal_lt; [ assumption | solve [ eauto ].. ].
  Qed.

  Section rel.
    Context (max : t).

    Definition lift_ltb_with_max (x y : t) : bool
      := ((subset x y)
            && (subset y max)
            && negb (equal x y)).

    Global Instance subrelation_lift_gtb
      : subrelation (fun x y : t => lift_ltb_with_max y x)
                    (fun a b : t => cardinal max - cardinal a < cardinal max - cardinal b).
    Proof.
      intros x y H.
      repeat setoid_rewrite andb_true_iff in H.
      destruct H as [[H0 H1] H2].
      apply subset_spec in H0.
      apply subset_spec in H1.
      apply negb_true_iff, not_true_iff_false in H2.
      setoid_rewrite equal_spec in H2.
      pose proof (subset_cardinal H0) as H0'.
      pose proof (subset_cardinal H1) as H1'.
      destruct (not_equal_ex H2) as [a [H3 H4]].
      pose proof (subset_cardinal_lt (x := a) H0).
      destruct H3 as [H3|H3].
      { intuition. }
      { intuition omega. }
    Qed.

    Definition well_founded_lift_gtb_with_max : well_founded (Basics.flip lift_ltb_with_max).
    Proof.
      eapply well_founded_subrelation;
        [ | eexact (Wf_nat.well_founded_ltof _ (fun x => cardinal max - cardinal x)) ].
      apply subrelation_lift_gtb.
    Defined.
  End rel.
End MSetBoundedLatticeOn.

Module MSetBoundedLattice (M: S) := MSetBoundedLatticeOn M.E M.
