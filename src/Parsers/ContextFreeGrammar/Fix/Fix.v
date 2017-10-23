Require Import Coq.Init.Wf Coq.Numbers.BinNums.
Require Import Coq.Arith.Arith.
Require Import Coq.FSets.FMapPositive.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Export Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Properties.
Require Import Fiat.Common.FMapExtensions.Wf.
Require Import Fiat.Common.
Require Import Fiat.Common.OptionFacts.
Module PositiveMapExtensions := FMapExtensionsWf PositiveMap.
Require Import Fiat.Common.SetoidInstances. (* must come after the above for instance priority *)

Set Implicit Arguments.
Local Open Scope grammar_fixedpoint_scope.

Section grammar_fixedpoint.
  Context {Char : Type}.

  Context (gdata : grammar_fixedpoint_data).

  Definition aggregate_state := PositiveMap.t (state gdata).

  Local Notation default_value := ⊤ (only parsing).

  Definition lookup_state (st : aggregate_state) (nt : default_nonterminal_carrierT)
    : state gdata
    := PositiveMapExtensions.find_default default_value (nonterminal_to_positive nt) st.

  Notation from_aggregate_state := lookup_state (only parsing).

  Definition aggregate_state_le : aggregate_state -> aggregate_state -> bool
    := PositiveMapExtensions.lift_leb state_le default_value.
  Definition aggregate_state_eq : aggregate_state -> aggregate_state -> bool
    := PositiveMapExtensions.lift_eqb state_beq default_value.
  Definition aggregate_state_lt (v1 v2 : aggregate_state) : bool
    := PositiveMapExtensions.lift_ltb state_beq state_le default_value v1 v2.

  Lemma PositiveMap_elements_iff {A m k v}
    : @PositiveMap.find A k m = Some v <-> In (k, v) (PositiveMap.elements m).
  Proof.
    rewrite PositiveMapExtensions.elements_iff_find.
    rewrite InA_alt; unfold PositiveMap.eq_key_elt, PositiveMap.E.eq; simpl.
    split; [ intros [[? ?] [[? ?] ?]] | intro H; exists (k, v) ];
      subst; repeat split; assumption.
  Qed.

  Lemma PositiveMap_elements_iff' {A m kv}
    : @PositiveMap.find A (fst kv) m = Some (snd kv) <-> In kv (PositiveMap.elements m).
  Proof.
    destruct kv; apply PositiveMap_elements_iff.
  Qed.

  Create HintDb aggregate_step_db discriminated.
  Hint Rewrite PositiveMap.fold_1 PositiveMap.gmapi nonterminal_to_positive_to_nonterminal positive_to_nonterminal_to_positive PositiveMap.gempty PositiveMapAdditionalFacts.gsspec (@state_beq_refl _ gdata) orb_true_iff orb_true_r orb_false_iff (@state_le_bottom_eq_bottom _ gdata) (@no_state_lt_bottom _ gdata) (@state_le_bottom_eq_bottom _ gdata) (@state_ge_top_eq_top _ gdata) (@bottom_lub_r _ gdata) (@bottom_lub_l _ gdata) (@top_lub_r _ gdata) (@top_lub_l _ gdata) (fun a b => @least_upper_bound_correct_l _ gdata a b : _ = true) (fun a b => @least_upper_bound_correct_r _ gdata a b : _ = true) (fun s => @bottom_bottom _ gdata s : _ = true) (fun s => @top_top _ gdata s : _ = true) beq_nat_true_iff @PositiveMapExtensions.lift_brelation_iff : aggregate_step_db.
  Hint Rewrite <- beq_nat_refl : aggregate_step_db.
  Hint Rewrite PositiveMapExtensions.map2_1bis_for_rewrite using reflexivity : aggregate_step_db.
  Hint Rewrite PositiveMapExtensions.fold_andb_true : aggregate_step_db.

  Local Ltac fold_andb_t_step :=
    idtac;
    match goal with
    | _ => progress intros
    | _ => progress subst
    | _ => congruence
    | _ => progress unfold PositiveMap.key in *
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ H : Some ?b <> Some false |- _ ] => destruct b eqn:?; [ clear H | congruence ]
    | [ H : (⊥ =b ?s) = false, H' : (⊥ < ?s) = false |- _ ]
      => let H'' := fresh in
         pose proof (bottom_bottom s) as H''; setoid_rewrite orb_true_iff in H''; destruct H''; congruence
    | [ H : context[PositiveMap.fold _ _ _ = true] |- _ ]
      => setoid_rewrite PositiveMapExtensions.fold_andb_true in H
    | [ |- context[PositiveMap.fold _ _ _ = true] ]
      => setoid_rewrite PositiveMapExtensions.fold_andb_true
    | [ |- true = false ] => symmetry
    | [ H : PositiveMap.fold _ _ _ = false |- false = true ]
      => rewrite <- H; clear H
    | [ H : context[PositiveMap.find _ (PositiveMap.map2 ?f _ _)] |- _ ]
      => setoid_rewrite (@PositiveMapExtensions.map2_1bis_for_rewrite _ _ _ f eq_refl) in H
    | [ |- context[PositiveMap.find _ (PositiveMap.map2 ?f _ _)] ]
      => setoid_rewrite (@PositiveMapExtensions.map2_1bis_for_rewrite _ _ _ f eq_refl)
    | [ H : context[PositiveMapExtensions.lift_brelation] |- _ ]
      => setoid_rewrite PositiveMapExtensions.lift_brelation_iff in H
    | [ |- context[PositiveMapExtensions.lift_brelation] ]
      => setoid_rewrite PositiveMapExtensions.lift_brelation_iff
    | [ H : ?x = _, H' : context[?x] |- _ ] => setoid_rewrite H in H'
    | [ H : ?x = _ |- context[?x] ] => setoid_rewrite H
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : pointwise_relation _ eq ?x ?y, H' : context[step_constraints _ ?x] |- _ ]
      => rewrite H in H'
    | _ => progress autorewrite with aggregate_step_db in *
    | [ H : forall k : positive, _ |- _ ]
      => repeat match goal with
                | [ k' : positive |- _ ]
                  => unique pose proof (H k')
                | [ |- context[PositiveMap.find ?k' _] ]
                  => unique pose proof (H k')
                | [ _ : context[PositiveMap.find ?k' _] |- _ ]
                  => unique pose proof (H k')
                end;
         clear H
    | _ => progress simpl in *
    | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
    | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
    | [ |- _ <> _ ] => intro
    | [ H : or _ _ |- _ ] => destruct H
    | [ |- and _ _ ] => split
    | [ H : (?x < ?y) = true, H' : (?y < ?z) = true |- _ ]
      => unique pose proof (state_lt_Transitive H H' : (x < z) = true)
    | [ H : is_true (?x =b ?y) |- _ ]
      => rewrite H in *; clear x H
    | [ H : is_true (?x =b ?y) |- _ ]
      => rewrite <- H in *; clear x H
    | [ H : ?R ?x ?y |- _ ]
      => is_var x; rewrite H in *; clear x H
    | [ H : ?R ?x ?y |- _ ]
      => is_var y; rewrite <- H in *; clear y H
    end.
  Local Ltac fold_andb_t := repeat fold_andb_t_step.

  Global Instance aggregate_state_eq_Reflexive : Reflexive aggregate_state_eq | 1 := _.
  Global Instance aggregate_state_eq_Symmetric : Symmetric aggregate_state_eq | 1 := _.
  Global Instance aggregate_state_eq_Transitive : Transitive aggregate_state_eq | 1 := _.
  Global Instance aggregate_state_le_Reflexive : Reflexive aggregate_state_le | 1 := _.
  Global Instance aggregate_state_le_Transitive : Transitive aggregate_state_le | 1 := _.
  Global Instance aggregate_state_eq_Proper_Equal
    : Proper (@PositiveMap.Equal _ ==> @PositiveMap.Equal _ ==> eq) aggregate_state_eq | 100
    := _.
  Global Instance aggregate_state_le_Proper_Equal
    : Proper (@PositiveMap.Equal _ ==> @PositiveMap.Equal _ ==> eq) aggregate_state_le | 100
    := _.
  Global Instance aggregate_state_lt_Proper_Equal
    : Proper (@PositiveMap.Equal _ ==> @PositiveMap.Equal _ ==> eq) aggregate_state_lt | 100
    := _.
  Global Instance aggregate_state_le_Proper
    : Proper (aggregate_state_eq ==> aggregate_state_eq ==> eq) aggregate_state_le | 1
    := _.
  Global Instance aggregate_state_lt_Proper
    : Proper (aggregate_state_eq ==> aggregate_state_eq ==> eq) aggregate_state_lt | 1
    := _.

  Definition aggregate_state_lub_f : option (state gdata) -> option (state gdata) -> option (state gdata)
      := PositiveMapExtensions.defaulted_f default_value default_value least_upper_bound.

  Definition aggregate_state_lub (v1 v2 : aggregate_state) : aggregate_state
    := PositiveMap.map2 aggregate_state_lub_f v1 v2.

  Definition aggregate_prestep (v : aggregate_state) : aggregate_state
    := let helper := step_constraints gdata (from_aggregate_state v) in
       PositiveMap.mapi (fun nt => helper (positive_to_nonterminal nt)) v.

  Definition aggregate_step (v : aggregate_state) : aggregate_state
    := aggregate_state_lub v (aggregate_prestep v).

  Definition aggregate_state_lub_correct (v1 v2 : aggregate_state)
    : aggregate_state_le v1 (aggregate_state_lub v1 v2)
      /\ aggregate_state_le v2 (aggregate_state_lub v1 v2).
  Proof.
    unfold aggregate_state_le, aggregate_state_lub, aggregate_state_lub_f.
    setoid_rewrite PositiveMapExtensions.lift_brelation_iff.
    unfold PositiveMapExtensions.defaulted_f.
    repeat match goal with
           | [ |- and _ _ ] => split
           | _ => intro
           | _ => progress subst
           | [ H : ?x = _ |- context[?x] ] => setoid_rewrite H
           | [ H : ?x = _, H' : context[?x] |- _ ] => setoid_rewrite H in H'
           | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
           | [ H : context[match ?e with _ => _ end] |- _ ] => destruct e eqn:?
           | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
           | [ |- is_true (?R ?x ?x) ] => reflexivity
           | _ => apply top_top
           | _ => apply least_upper_bound_correct_l
           | _ => apply least_upper_bound_correct_r
           | _ => congruence
           | [ H : _ |- _ ] => setoid_rewrite PositiveMapExtensions.map2_1bis_for_rewrite in H; [ | reflexivity.. ]
           end.
  Qed.

  Lemma find_aggregate_state_lub a b k
    : PositiveMap.find k (aggregate_state_lub a b)
      = aggregate_state_lub_f (PositiveMap.find k a) (PositiveMap.find k b).
  Proof.
    unfold aggregate_state_lub.
    fold_andb_t.
  Qed.

  Lemma nothing_empty_lt v : ~aggregate_state_lt (PositiveMap.empty _) v.
  Proof.
    setoid_rewrite PositiveMapExtensions.empty_ltb_nothing; [ congruence | ].
    setoid_rewrite state_ge_top_eq_top.
    intros; symmetry; assumption.
  Qed.

  Lemma aggregate_state_lt_wf : well_founded (Basics.flip aggregate_state_lt).
  Proof.
    apply PositiveMapExtensions.well_founded_lift_gtb.
    { eapply Wf.well_founded_subrelation; [ | eexact (@state_gt_wf _ gdata) ].
      unfold flip, state_le; intros x y H.
      destruct (y < x); [ reflexivity | simpl in * ].
      destruct (y =b x) eqn:Heqb; simpl in *; assumption. }
    { apply top_top. }
    { exact _. }
    { exact _. }
    { exact _. }
    { exact _. }
  Defined.

  Section wrap_wf.
    Context {A R} (Rwf : @well_founded A R).

    Definition lt_wf_idx_step
               (lt_wf_idx : nat -> well_founded R)
               (n : nat)
      : well_founded R.
    Proof.
      destruct n.
      { clear -Rwf; abstract apply Rwf. }
      { constructor; intros; apply lt_wf_idx; assumption. }
    Defined.

    Fixpoint lt_wf_idx (n : nat) : well_founded R
      := lt_wf_idx_step (@lt_wf_idx) n.
  End wrap_wf.

  Definition aggregate_state_lt_wf_idx (n : nat) : well_founded (Basics.flip aggregate_state_lt)
    := lt_wf_idx aggregate_state_lt_wf n.

  Definition step_lt {st}
    : aggregate_state_eq st (aggregate_step st) = false -> Basics.flip aggregate_state_lt (aggregate_step st) st.
  Proof.
    unfold Basics.flip.
    intros pf.
    destruct (aggregate_state_lt st (aggregate_step st)) eqn:H; [ reflexivity | exfalso ].
    unfold aggregate_step in *.
    pose proof (proj1 (aggregate_state_lub_correct st (aggregate_prestep st))) as H'.
    unfold aggregate_state_lt, PositiveMapExtensions.lift_ltb in *.
    fold aggregate_state_le in *.
    fold aggregate_state_eq in *.
    generalize dependent (aggregate_state_le st (aggregate_state_lub st (aggregate_prestep st))).
    generalize dependent (aggregate_state_eq st (aggregate_state_lub st (aggregate_prestep st))).
    clear.
    abstract (
        intros [] ? []; simpl; intros; congruence
      ).
  Defined.

  Global Instance aggregate_state_lub_Proper
    : Proper (aggregate_state_eq ==> aggregate_state_eq ==> aggregate_state_eq) aggregate_state_lub | 1.
  Proof.
    unfold aggregate_state_eq, aggregate_state_lub, aggregate_state_lub_f.
    refine PositiveMapExtensions.map2_defaulted_Proper_lift_brelation.
  Qed.

  Global Instance from_aggregate_state_Proper
    : Proper (aggregate_state_eq ==> eq ==> state_beq) from_aggregate_state | 1.
  Proof.
    unfold aggregate_state_eq, PositiveMapExtensions.lift_eqb, from_aggregate_state, PositiveMapExtensions.find_default, option_rect; repeat intro; fold_andb_t.
  Qed.

  Global Instance aggregate_step_Proper
    : Proper (aggregate_state_eq ==> aggregate_state_eq) aggregate_step | 1.
  Proof.
    intros x y H.
    assert (H' : pointwise_relation _ state_beq (from_aggregate_state x) (from_aggregate_state y)) by (intro; setoid_rewrite H; reflexivity).
    unfold aggregate_state_eq, PositiveMapExtensions.lift_eqb, aggregate_step, aggregate_state_lub, aggregate_prestep in *.
    setoid_rewrite PositiveMapExtensions.lift_brelation_iff in H.
    setoid_rewrite PositiveMapExtensions.lift_brelation_iff.
    repeat setoid_rewrite fold_option_rect_nodep.
    first [ setoid_rewrite (PositiveMapExtensions.map2_1bis_for_rewrite _ _ _ _ eq_refl)
          | setoid_rewrite (PositiveMapExtensions.map2_1bis_for_rewrite _ _ _ _ _); [ | reflexivity.. ] ].
    setoid_rewrite PositiveMap.gmapi.
    unfold option_rect_nodep, option_map.
    intro k; specialize (H k).
    generalize dependent (lookup_state x); generalize dependent (lookup_state y); intros;
      do 2 edestruct PositiveMap.find;
      fold_andb_t.
  Qed.

  Lemma lookup_state_aggregate_state_lub a b nt
    : lookup_state (aggregate_state_lub a b) nt = (lookup_state a nt ⊔ lookup_state b nt).
  Proof.
    unfold lookup_state, PositiveMapExtensions.find_default.
    rewrite find_aggregate_state_lub.
    unfold option_rect, aggregate_state_lub_f.
    fold_andb_t.
  Qed.

  Global Instance lookup_state_Proper
    : Proper (aggregate_state_eq ==> eq ==> state_beq) lookup_state | 1.
  Proof.
    unfold aggregate_state_eq, PositiveMapExtensions.lift_eqb, lookup_state, PositiveMapExtensions.find_default, option_rect; repeat intro; fold_andb_t.
  Qed.

  Lemma find_aggregate_prestep st nt
    : PositiveMap.find nt (aggregate_prestep st)
      = option_map (step_constraints gdata (lookup_state st) (positive_to_nonterminal nt))
                   (PositiveMap.find nt st).
  Proof.
    unfold aggregate_prestep.
    autorewrite with aggregate_step_db.
    unfold from_aggregate_state, option_rect, option_map.
    edestruct PositiveMap.find; reflexivity.
  Qed.

  Lemma find_aggregate_step st nt
    : PositiveMap.find nt (aggregate_step st)
      = option_map (fun v => v ⊔ step_constraints gdata (lookup_state st) (positive_to_nonterminal nt) v)
                   (PositiveMap.find nt st).
  Proof.
    unfold aggregate_step.
    rewrite find_aggregate_state_lub, find_aggregate_prestep.
    edestruct PositiveMap.find; reflexivity.
  Qed.

  Lemma lookup_state_aggregate_prestep st nt
    : lookup_state (aggregate_prestep st) nt
      = option_rect (fun _ => _)
                    (fun _ => step_constraints gdata (lookup_state st) nt (lookup_state st nt))
                    default_value
                    (PositiveMap.find (nonterminal_to_positive nt) st).
  Proof.
    unfold lookup_state.
    unfold PositiveMapExtensions.find_default.
    rewrite find_aggregate_prestep.
    unfold lookup_state.
    rewrite nonterminal_to_positive_to_nonterminal.
    unfold PositiveMapExtensions.find_default.
    unfold state in *; simpl in *.
    edestruct PositiveMap.find; reflexivity.
  Qed.

  Lemma lookup_state_aggregate_step st nt
    : lookup_state (aggregate_step st) nt
      = option_rect (fun _ => _)
                    (fun s => s ⊔ step_constraints gdata (lookup_state st) nt (lookup_state st nt))
                    default_value
                    (PositiveMap.find (nonterminal_to_positive nt) st).
  Proof.
    unfold lookup_state, PositiveMapExtensions.find_default.
    rewrite find_aggregate_step.
    unfold lookup_state, PositiveMapExtensions.find_default.
    rewrite nonterminal_to_positive_to_nonterminal.
    unfold state in *; simpl in *.
    edestruct PositiveMap.find; reflexivity.
  Qed.

  Section with_initial.
    Context (initial_nonterminals_data : list default_nonterminal_carrierT).

    Definition aggregate_state_max : aggregate_state
      := List.fold_right
           (fun nt st => PositiveMap.add (nonterminal_to_positive nt) ⊥ st)
           (PositiveMap.empty _)
           initial_nonterminals_data.

    Definition pre_Fix_grammar_helper : aggregate_state -> aggregate_state
      := Fix
           (aggregate_state_lt_wf_idx (10 * List.length initial_nonterminals_data))
           (fun _ => aggregate_state)
           (fun st Fix_grammar_internal
            => let st' := aggregate_step st in
               match Sumbool.sumbool_of_bool (aggregate_state_eq st st') with
               | left pf => st
               | right pf => Fix_grammar_internal st' (step_lt pf)
               end).

    Definition pre_Fix_grammar : aggregate_state
      := pre_Fix_grammar_helper aggregate_state_max.

    Lemma pre_Fix_grammar_helper_fixed st (H : aggregate_state_eq st (aggregate_step st))
      : aggregate_state_eq st (pre_Fix_grammar_helper st).
    Proof.
      unfold pre_Fix_grammar_helper.
      rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
      edestruct dec; [ | congruence ].
      reflexivity.
    Qed.

    Lemma pre_Fix_grammar_helper_commute v
      : aggregate_state_eq (pre_Fix_grammar_helper (aggregate_step v))
                           (aggregate_step (pre_Fix_grammar_helper v)).
    Proof.
      unfold pre_Fix_grammar_helper.
      induction (aggregate_state_lt_wf v) as [v H IHv].
      rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial);
        symmetry;
        rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial);
        symmetry.
      do 2 edestruct dec; try reflexivity;
        repeat match goal with
               | [ H : ?x = true |- _ ] => change (is_true x) in H
               end.
      { fold @pre_Fix_grammar_helper in *.
        rewrite <- pre_Fix_grammar_helper_fixed by assumption.
        assumption. }
      { match goal with
        | [ H : is_true (aggregate_state_eq ?x ?y), H' : context[?x] |- _ ]
          => rewrite <- H in H'
        end.
        congruence. }
      { apply IHv.
        apply step_lt; assumption. }
    Qed.

    Global Instance aggregate_state_eq_Proper_eq
      : Proper (eq ==> eq ==> eq) aggregate_state_eq
      := _.
    Global Instance aggregate_step_Proper_eq
      : Proper (eq ==> eq) aggregate_step
      := _.

    Lemma pre_Fix_grammar_fixedpoint
      : aggregate_state_eq pre_Fix_grammar (aggregate_step pre_Fix_grammar).
    Proof.
      unfold pre_Fix_grammar, pre_Fix_grammar_helper.
      generalize aggregate_state_max; intro a.
      rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
      edestruct dec as [pf|pf].
      { rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
        edestruct dec; [ | congruence ].
        assumption. }
      { induction (aggregate_state_lt_wf a) as [?? IH].
        rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
        symmetry;
          rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial);
          symmetry.
        rewrite pf; simpl.
        edestruct dec as [pf'|pf'].
        { rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
          rewrite pf'; simpl.
          assumption. }
        { apply IH; try assumption; []; clear IH.
          unfold Basics.flip, aggregate_state_lt, PositiveMapExtensions.lift_ltb.
          setoid_rewrite pf; simpl; rewrite andb_true_r.
          pose proof (fun x => aggregate_state_lub_correct x (aggregate_prestep x)) as H'.
          unfold aggregate_step in *.
          edestruct H'; eassumption. } }
    Qed.

    Lemma find_aggregate_state_max_rdp_spec k v
      : PositiveMap.find k aggregate_state_max = Some v
        <-> (v = ⊥ /\ rdp_list_is_valid_nonterminal initial_nonterminals_data (positive_to_nonterminal k)).
    Proof.
      unfold aggregate_state_max in *.
      generalize dependent initial_nonterminals_data; intros ls.
      induction ls as [|x xs IHxs].
      { simpl in *.
        autorewrite with aggregate_step_db in *.
        intuition (tauto || congruence || eauto). }
      { simpl in *.
        autorewrite with aggregate_step_db in *.
        edestruct PositiveMap.E.eq_dec; subst;
          autorewrite with aggregate_step_db in *;
          auto using eq_refl with nocore.
        { repeat intuition (congruence || subst || eauto). }
        { intuition (congruence || subst || eauto).
          { apply orb_true_iff; intuition. }
          { do 2 match goal with
                 | [ H : is_true (orb _ _) |- _ ] => apply orb_true_iff in H
                 | [ H : _ |- _ ] => setoid_rewrite beq_nat_true_iff in H
                 end.
            repeat intuition (congruence || subst || (autorewrite with aggregate_step_db in * ) || eauto). } } }
    Qed.

    Lemma find_aggregate_state_max k v
      : PositiveMap.find k aggregate_state_max = Some v
        -> PositiveMap.find k aggregate_state_max = Some ⊥.
    Proof.
      setoid_rewrite find_aggregate_state_max_rdp_spec.
      tauto.
    Qed.

    Lemma find_aggregate_state_max_exact k
      : PositiveMap.find k aggregate_state_max
        = if rdp_list_is_valid_nonterminal initial_nonterminals_data (positive_to_nonterminal k)
          then Some ⊥
          else None.
    Proof.
      pose proof (find_aggregate_state_max_rdp_spec k) as H;
        unfold is_true in *; split_iff; break_match.
      { intuition eauto. }
      { edestruct PositiveMap.find; [ | reflexivity ].
        specialize_all_ways; specialize_by (exact eq_refl).
        intuition congruence. }
    Qed.
  End with_initial.

  Section with_grammar.
    Context (G : pregrammar' Char).

    Let predata := @rdp_list_predata _ G.
    Local Existing Instance predata.

    Definition find_aggregate_state_max_spec k v
      : PositiveMap.find k (aggregate_state_max initial_nonterminals_data) = Some v
        <-> (v = ⊥ /\ is_valid_nonterminal initial_nonterminals_data (positive_to_nonterminal k))
      := find_aggregate_state_max_rdp_spec initial_nonterminals_data k v.

    Hint Rewrite find_aggregate_state_max_spec : aggregate_step_db.

    Lemma lookup_state_aggregate_state_max nt
      : lookup_state (aggregate_state_max initial_nonterminals_data) nt
        = if is_valid_nonterminal initial_nonterminals_data nt
          then ⊥
          else default_value.
    Proof.
      unfold lookup_state, PositiveMapExtensions.find_default, option_rect.
      destruct (PositiveMap.find (nonterminal_to_positive nt) (aggregate_state_max (@initial_nonterminals_data _ predata))) eqn:H; [ | ];
        setoid_rewrite H.
      { simpl in *.
        apply find_aggregate_state_max_spec in H.
        rewrite nonterminal_to_positive_to_nonterminal in H.
        destruct H as [? H']; subst; simpl in *; rewrite H'; intuition. }
      { match goal with |- context[if ?e then _ else _] => destruct e eqn:H' end;
        [ | reflexivity ].
        pose proof (find_aggregate_state_max_spec (nonterminal_to_positive nt) ⊥) as H''.
        rewrite nonterminal_to_positive_to_nonterminal, H' in H''.
        destruct H'' as [_ H''].
        rewrite H'' in H by intuition.
        congruence. }
    Qed.

    Lemma find_pre_Fix_grammar (nt : default_nonterminal_carrierT)
      : is_valid_nonterminal initial_nonterminals_data nt
        <-> PositiveMap.find (nonterminal_to_positive nt) (pre_Fix_grammar initial_nonterminals_data) <> None.
    Proof.
      unfold pre_Fix_grammar, pre_Fix_grammar_helper.
      assert (H : PositiveMap.find (nonterminal_to_positive nt) (aggregate_state_max initial_nonterminals_data) <> None
                  <-> is_valid_nonterminal initial_nonterminals_data nt).
      { pose proof (find_aggregate_state_max_spec (nonterminal_to_positive nt)) as H.
        rewrite nonterminal_to_positive_to_nonterminal in H.
        edestruct PositiveMap.find.
        { edestruct H as [H0 H1]; clear H.
          intuition congruence. }
        { specialize (H ⊥).
          intuition congruence. } }
      rewrite <- H; clear H.
      generalize dependent (aggregate_state_max initial_nonterminals_data); intro a; intros.
      induction (aggregate_state_lt_wf a) as [?? IH].
      rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
      edestruct dec as [pf|pf]; [ reflexivity | ].
      rewrite <- IH by (apply step_lt; assumption).
      rewrite find_aggregate_step.
      unfold option_map; split; fold_andb_t.
    Qed.

    Lemma find_pre_Fix_grammar_to_lookup_state (nt : default_nonterminal_carrierT)
      : PositiveMap.find (nonterminal_to_positive nt) (pre_Fix_grammar initial_nonterminals_data)
        = if is_valid_nonterminal initial_nonterminals_data nt
          then Some (lookup_state (pre_Fix_grammar initial_nonterminals_data) nt)
          else None.
    Proof.
      let v := match goal with |- context[if ?v then _ else _] => v end in
      destruct v eqn:Hvalid.
      { apply find_pre_Fix_grammar in Hvalid.
        unfold lookup_state, PositiveMapExtensions.find_default, state in *; simpl in *.
        edestruct PositiveMap.find;
          [ reflexivity | congruence ]. }
      { destruct (PositiveMap.find (nonterminal_to_positive nt) (pre_Fix_grammar (@initial_nonterminals_data _ predata))) eqn:H; [ | reflexivity ].
        rewrite (proj2 (find_pre_Fix_grammar _)) in Hvalid; congruence. }
    Qed.

    Lemma find_pre_Fix_grammar_to_lookup_state' nt
      : PositiveMap.find nt (pre_Fix_grammar initial_nonterminals_data)
        = if is_valid_nonterminal initial_nonterminals_data (positive_to_nonterminal nt)
          then Some (lookup_state (pre_Fix_grammar initial_nonterminals_data) (positive_to_nonterminal nt))
          else None.
    Proof.
      rewrite <- find_pre_Fix_grammar_to_lookup_state, positive_to_nonterminal_to_positive.
      reflexivity.
    Qed.

    Lemma lookup_state_invalid_pre_Fix_grammar (nt : default_nonterminal_carrierT)
          (Hinvalid : is_valid_nonterminal initial_nonterminals_data nt = false)
      : lookup_state (pre_Fix_grammar initial_nonterminals_data) nt = default_value.
    Proof.
      unfold lookup_state, PositiveMapExtensions.find_default.
      pose proof (find_pre_Fix_grammar nt).
      rewrite Hinvalid in H; destruct H.
      unfold state in *; simpl in *.
      edestruct PositiveMap.find.
      { intuition congruence. }
      { reflexivity. }
    Qed.
  End with_grammar.
End grammar_fixedpoint.
