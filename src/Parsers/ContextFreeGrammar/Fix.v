Require Import Coq.Init.Wf Coq.Numbers.BinNums Coq.PArith.BinPos Coq.PArith.Pnat.
Require Import Coq.Arith.Arith.
Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMaps.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetPositive.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.BaseTypes.
Require Export Fiat.Parsers.ContextFreeGrammar.FixDefinitions.
Require Import Fiat.Common.FMapExtensions.
Require Import Fiat.Common.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.List.ListMorphisms.
Require Import Fiat.Common.BoolFacts.
Require Import Fiat.Common.Notations.

Set Implicit Arguments.
Local Open Scope grammar_fixedpoint_scope.

Module PositiveMapExtensions := FMapExtensions PositiveMap.

Definition PositiveSet_of_list (ls : list positive) : PositiveSet.t
  := List.fold_right
       PositiveSet.add
       PositiveSet.empty
       ls.

Lemma state_le_refl {state} {fp : grammar_fixedpoint_lattice_data state} (s : state) : s <= s.
Proof.
  unfold state_le.
  rewrite state_beq_refl.
  reflexivity.
Qed.

Global Instance state_beq_Equivalence {T d} : Equivalence (@state_beq T d).
Proof.
  split; repeat intro;
    repeat match goal with H : _ |- _ => apply state_beq_bl in H end;
    subst; apply state_beq_refl.
Qed.

Global Instance state_lt_Irreflexive {T d} : Irreflexive (@state_lt T d).
Proof.
  intros x H.
  induction (state_lt_wf x) as [x H' IH].
  eauto.
Qed.

Global Instance state_le_Reflexive {T d} : Reflexive (@state_le T d).
Proof.
  unfold state_le; repeat intro; rewrite state_beq_refl; reflexivity.
Qed.

Global Instance state_le_Transitive {T d} : Transitive (@state_le T d).
Proof.
  unfold state_le, is_true; repeat intro;
    rewrite orb_true_iff in *;
    destruct_head or;
    repeat match goal with H : _ |- _ => apply state_beq_bl in H end;
    subst;
    rewrite ?state_beq_refl; try solve [ eauto ].
  right.
  eapply state_lt_Transitive; eassumption.
Qed.

Lemma state_le_bottom_eq_bottom {state} {d : grammar_fixedpoint_lattice_data state} (s : state)
  : (s <= ⊥) = (s =b ⊥).
Proof.
  pose proof (bottom_bottom s) as H.
  unfold state_le in *.
  destruct (s =b ⊥) eqn:H'.
  { apply state_beq_bl in H'; subst.
    reflexivity. }
  { simpl.
    apply orb_true_iff in H; destruct H as [H|H].
    { apply state_beq_bl in H; subst.
      rewrite state_beq_refl in H'; congruence. }
    { destruct (s < ⊥) eqn:H''; trivial.
      exfalso; eapply state_lt_Irreflexive.
      etransitivity; eassumption. } }
Qed.

Section grammar_fixedpoint.
  Context {Char : Type}.

  Context (gdata : grammar_fixedpoint_data)
          (G : pregrammar Char).

  Definition aggregate_state := PositiveMap.t (state gdata).

  Definition from_aggregate_state (f : aggregate_state) : default_nonterminal_carrierT -> state gdata
    := fun nt => option_rect (fun _ => state gdata) (fun v => v) (initial_state nt)
                             (PositiveMap.find (nonterminal_to_positive nt) f).

  Definition aggregate_state_le (v1 v2 : aggregate_state) : bool
    := PositiveMap.fold
         (fun _ => andb)
         (PositiveMap.map2
            (fun x1 x2
             => match x1, x2 with
                | Some x1, Some x2 => Some (x1 <= x2)
                | Some x1, None => Some (x1 <= ⊥)
                | None, None => None
                | None, Some x2 => Some (⊥ <= x2)
                end)
            v1 v2)
         true.
  Definition aggregate_state_eq (v1 v2 : aggregate_state) : bool
    := PositiveMap.fold
         (fun _ => andb)
         (PositiveMap.map2
            (fun x1 x2
             => match x1, x2 with
                | Some x1, Some x2 => Some (x1 =b x2)
                | Some x, None
                | None, Some x
                  => Some (x =b ⊥)
                | None, None => None
                end)
            v1 v2)
         true.

  Definition aggregate_state_lt (v1 v2 : aggregate_state) : bool
    := aggregate_state_le v1 v2 && negb (aggregate_state_eq v1 v2).

  Local Ltac handle_PositiveMap_fold :=
    repeat match goal with
           | _ => rewrite !PositiveMap.fold_1
           | [ H : _ |- _ ] => rewrite !PositiveMap.fold_1 in H
           | [ |- appcontext[fold_left (fun a b => @?f b && a)%bool] ]
             => rewrite (@ListFacts.fold_map _ _ _ _ (fun a b => andb b a) f), <- fold_left_rev_right, <- map_rev
           | [ H : appcontext[fold_left (fun a b => ?g (@?f b) a)] |- _ ]
             => rewrite (@ListFacts.fold_map _ _ _ _ (fun a b => g b a) f), <- fold_left_rev_right, <- map_rev in H
           | [ H : context[fold_right andb true _] |- _ ] => setoid_rewrite fold_right_andb_map_in_iff in H
           | [ |- context[fold_right andb true _] ] => setoid_rewrite fold_right_andb_map_in_iff
           | [ H : context[In _ (rev _)] |- _ ] => setoid_rewrite <- in_rev in H
           | [ |- context[In _ (rev _)] ] => setoid_rewrite <- in_rev
           end.

  Lemma PositiveMap_elements_iff {A m k v}
    : @PositiveMap.find A k m = Some v <-> In (k, v) (PositiveMap.elements m).
  Proof.
    split; [ apply PositiveMap.elements_correct | apply PositiveMap.elements_complete ].
  Qed.

  Lemma PositiveMap_elements_iff' {A m kv}
    : @PositiveMap.find A (fst kv) m = Some (snd kv) <-> In kv (PositiveMap.elements m).
  Proof.
    destruct kv; apply PositiveMap_elements_iff.
  Qed.

  Create HintDb aggregate_step_db discriminated.
  Hint Rewrite PositiveMap.fold_1 PositiveMap.gmapi nonterminal_to_positive_to_nonterminal positive_to_nonterminal_to_positive PositiveMap.gempty PositiveMapAdditionalFacts.gsspec @state_beq_refl orb_true_iff orb_true_r orb_false_iff @greatest_lower_bound_correct_l @greatest_lower_bound_correct_r @bottom_bottom @state_le_bottom_eq_bottom : aggregate_step_db.
  Definition map2_1bis_for_rewrite (* no metavariables deep inside the beta-iota normal form *)
             elt elt' elt'' f H m m' x
    := @PositiveMapExtensions.BasicFacts.map2_1bis elt elt' elt'' m m' x f H.
  Hint Rewrite map2_1bis_for_rewrite using reflexivity : aggregate_step_db.

  Lemma PositiveMap_fold_andb_true v
    : PositiveMap.fold (fun _ => andb) v true <-> forall k, PositiveMap.find k v <> Some false.
  Proof.
    handle_PositiveMap_fold.
    setoid_rewrite PositiveMap_elements_iff.
    split; intros H x; [ specialize (H (x, false)) | specialize (H (fst x)) ].
    { simpl in *; intuition congruence. }
    { destruct x as [? []]; simpl in *; intuition. }
  Qed.

  Hint Rewrite PositiveMap_fold_andb_true : aggregate_step_db.

  Local Ltac fold_andb_t_step :=
    idtac;
    match goal with
    | _ => progress intros
    | _ => progress subst
    | _ => congruence
    | _ => progress unfold is_true in *
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | [ H : (_ =b _) = true |- _ ] => apply state_beq_bl in H
    | [ H : Some ?b <> Some false |- _ ] => destruct b eqn:?; [ clear H | congruence ]
    | [ H : (⊥ =b ?s) = false, H' : (⊥ < ?s) = false |- _ ]
      => let H'' := fresh in
         pose proof (bottom_bottom s) as H''; setoid_rewrite orb_true_iff in H''; destruct H''; congruence
    | [ H : context[PositiveMap.fold _ _ _ = true] |- _ ]
      => setoid_rewrite PositiveMap_fold_andb_true in H
    | [ |- context[PositiveMap.fold _ _ _ = true] ]
      => setoid_rewrite PositiveMap_fold_andb_true
    | [ |- true = false ] => symmetry
    | [ H : PositiveMap.fold _ _ _ = false |- false = true ]
      => rewrite <- H; clear H
    | [ H : context[PositiveMap.find _ (PositiveMap.map2 ?f _ _)] |- _ ]
      => setoid_rewrite (@map2_1bis_for_rewrite _ _ _ f eq_refl) in H
    | [ |- context[PositiveMap.find _ (PositiveMap.map2 ?f _ _)] ]
      => setoid_rewrite (@map2_1bis_for_rewrite _ _ _ f eq_refl)
    | [ H : ?x = _, H' : context[?x] |- _ ] => rewrite H in H'
    | [ H : and _ _ |- _ ] => destruct H
    | _ => progress autorewrite with aggregate_step_db in *
    | [ H : forall k : positive, _ |- _ ]
      => repeat match goal with
                | [ k' : positive |- _ ]
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
    end.
  Local Ltac fold_andb_t := repeat fold_andb_t_step.

  Global Instance aggregate_state_eq_Reflexive : Reflexive aggregate_state_eq.
  Proof. unfold aggregate_state_eq; repeat intro; fold_andb_t. Qed.

  Global Instance aggregate_state_eq_Symmetric : Symmetric aggregate_state_eq.
  Proof. unfold aggregate_state_eq; repeat intro; fold_andb_t. Qed.

  Global Instance aggregate_state_eq_Transitive : Transitive aggregate_state_eq.
  Proof. unfold aggregate_state_eq; repeat intro; fold_andb_t. Qed.

  Global Instance aggregate_state_le_Reflexive : Reflexive aggregate_state_le.
  Proof. unfold aggregate_state_le, state_le; repeat intro; fold_andb_t. Qed.

  Global Instance aggregate_state_le_Transitive : Transitive aggregate_state_le.
  Proof. unfold aggregate_state_le, state_le; repeat intro; fold_andb_t. Qed.

  Global Instance aggregate_state_eq_Proper
    : Proper (@PositiveMap.Equal _ ==> @PositiveMap.Equal _ ==> eq) aggregate_state_eq.
  Proof.
    intros a b H a' b' H'.
    destruct (aggregate_state_eq a a') eqn:Ha;
    destruct (aggregate_state_eq b b') eqn:Hb;
    unfold aggregate_state_eq in *;
    try reflexivity; fold_andb_t.
  Qed.

  Global Instance aggregate_state_le_Proper
    : Proper (@PositiveMap.Equal _ ==> @PositiveMap.Equal _ ==> eq) aggregate_state_le.
  Proof.
    intros a b H a' b' H'.
    destruct (aggregate_state_le a a') eqn:Ha;
    destruct (aggregate_state_le b b') eqn:Hb;
    unfold aggregate_state_le in *;
    try reflexivity; fold_andb_t.
  Qed.

  Global Instance aggregate_state_lt_Proper
    : Proper (@PositiveMap.Equal _ ==> @PositiveMap.Equal _ ==> eq) aggregate_state_lt.
  Proof.
    unfold aggregate_state_lt.
    intros ?? H ?? H'.
    rewrite H, H'.
    reflexivity.
  Qed.

  Definition aggregate_state_glb (v1 v2 : aggregate_state) : aggregate_state
    := PositiveMap.map2
         (fun x1 x2
          => match x1, x2 with
             | Some x1, Some x2 => Some (x1 ⊓ x2)
             | Some x, _
             | _, Some x
               => None
             | None, None => None
             (*| None, _ => None
             | _, None => None*)
             end)
         v1 v2.

  Definition aggregate_prestep (v : aggregate_state) : aggregate_state
    := let helper := step_constraints gdata (from_aggregate_state v) in
       PositiveMap.mapi (fun nt => helper (positive_to_nonterminal nt)) v.

  Definition aggregate_step (v : aggregate_state) : aggregate_state
    := aggregate_state_glb v (aggregate_prestep v).

  Definition aggregate_state_glb_correct (v1 v2 : aggregate_state)
    : aggregate_state_le (aggregate_state_glb v1 v2) v1
      /\ aggregate_state_le (aggregate_state_glb v1 v2) v2.
  Proof.
    unfold aggregate_state_le, aggregate_state_glb.
    fold_andb_t.
  Qed.

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition aggregate_state_max : aggregate_state
    := List.fold_right
         (fun nt st => PositiveMap.add (nonterminal_to_positive nt) (initial_state nt) st)
         (PositiveMap.empty _)
         initial_nonterminals_data.

  Lemma find_aggregate_state_max k v
    : PositiveMap.find k aggregate_state_max = Some v
      -> PositiveMap.find k aggregate_state_max = Some (initial_state (positive_to_nonterminal k)).
  Proof.
    unfold aggregate_state_max in *.
    generalize (@initial_nonterminals_data _ _); intros ls H.
    induction ls as [|x xs IHxs].
    { simpl in *.
      autorewrite with aggregate_step_db in *.
      congruence. }
    { simpl in *.
      autorewrite with aggregate_step_db in *.
      edestruct PositiveMap.E.eq_dec; subst;
      autorewrite with aggregate_step_db in *;
      auto using eq_refl with nocore. }
  Qed.

  Local Ltac aggregate_step_t :=
    repeat match goal with
           | [ |- True ] => constructor
           | _ => progress intros
           | _ => progress unfold from_aggregate_state, aggregate_state, aggregate_state_le, aggregate_step, option_map, option_rect in *
           | _ => congruence
           | _ => progress autorewrite with aggregate_step_db
           | [ H : _ |- _ ] => progress autorewrite with aggregate_step_db in H
           | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : sig _ |- _ ] => destruct H
           | _ => progress subst
           | _ => progress simpl in *
           | [ |- context[PositiveMap.find ?k ?st] ]
             => destruct (PositiveMap.find k st) eqn:?
           | [ H : context[match PositiveMap.find ?k ?st with _ => _ end] |- _ ]
             => destruct (PositiveMap.find k st) eqn:?
           | _ => progress handle_PositiveMap_fold
           | [ H : In _ (rev _) |- _ ] => apply in_rev in H
           | [ H : In ?x (PositiveMap.elements _) |- _ ] => is_var x; destruct x
           | [ H : In (_, _) (PositiveMap.elements _) |- _ ] => apply PositiveMap.elements_complete in H
           | [ H : PositiveMap.find ?k (PositiveMap.map2 ?f ?ls1 ?ls2) = Some ?v |- _ ]
             => erewrite PositiveMap.map2_1 in H by (eapply PositiveMap.map2_2; exists v; exact H)
           | [ H : andb _ _ = true |- _ ] => apply andb_true_iff in H
           | _ => progress unfold is_true in *
           | [ H : PositiveMap.find _ aggregate_state_max = Some _ |- _ ] => erewrite find_aggregate_state_max in H by eassumption
           end.

  Lemma nothing_lt_empty v : ~aggregate_state_lt v (PositiveMap.empty _).
  Proof.
    unfold aggregate_state_lt.
    apply not_andb_negb_iff.
    unfold aggregate_state_le, aggregate_state_eq.
    fold_andb_t.
  Qed.

  Lemma aggregate_state_of_list_lt_wf : well_founded (fun v1 v2 => aggregate_state_lt (PositiveMapExtensions.of_list v1) (PositiveMapExtensions.of_list v2)).
  Proof.
    intro a.
    induction a as [|x xs IHxs];
      constructor; simpl; intros y H.
    { exfalso; eapply nothing_lt_empty; eassumption. }
    { admit. }
  Admitted.

  Lemma aggregate_state_lt_wf : well_founded aggregate_state_lt.
  Proof.
    intro a.
    remember (PositiveMap.elements a) as a'.
    revert dependent a.
    pose proof (aggregate_state_of_list_lt_wf a') as H.
    induction H as [a' H H'].
    intros a Heq; subst.
    specialize (fun a0 pf => H' _ pf a0 eq_refl).
    constructor; intros b H''.
    apply H'; clear H' H.
    rewrite !PositiveMapExtensions.of_list_elements; assumption.
  Defined.

  Definition aggregate_state_lt_wf_idx_step
             (aggregate_state_lt_wf_idx : nat -> well_founded aggregate_state_lt)
             (n : nat)
    : well_founded aggregate_state_lt.
  Proof.
    destruct n.
    { clear; abstract apply aggregate_state_lt_wf. }
    { constructor; intros; apply aggregate_state_lt_wf_idx; assumption. }
  Defined.

  Fixpoint aggregate_state_lt_wf_idx (n : nat) : well_founded aggregate_state_lt
    := aggregate_state_lt_wf_idx_step (@aggregate_state_lt_wf_idx) n.

  Definition step_lt {st}
    : aggregate_state_eq (aggregate_step st) st = false -> aggregate_state_lt (aggregate_step st) st.
  Proof.
    intros pf.
    destruct (aggregate_state_lt (aggregate_step st) st) eqn:H; [ reflexivity | exfalso ].
    abstract (
        unfold aggregate_step in *;
        pose proof (aggregate_state_glb_correct st (aggregate_prestep st)) as H';
        destruct H' as [H' _];
        unfold aggregate_state_lt in *;
        rewrite H', pf in H;
        simpl in *;
        congruence
      ).
  Defined.

  Definition pre_Fix_grammar : aggregate_state
    := Fix
         (aggregate_state_lt_wf_idx (10 * List.length initial_nonterminals_data))
         (fun _ => aggregate_state)
         (fun st Fix_grammar_internal
          => match Sumbool.sumbool_of_bool (aggregate_state_eq (aggregate_step st) st) with
             | left pf => st
             | right pf => Fix_grammar_internal (aggregate_step st) (step_lt pf)
             end)
         aggregate_state_max.

  Definition lookup_state (st : aggregate_state) (nt : default_nonterminal_carrierT)
    : state gdata
    := option_rect (fun _ => state gdata)
                   (fun v => v)
                   (initial_state nt)
                   (PositiveMap.find (nonterminal_to_positive nt) st).

  Lemma pre_Fix_grammar_fixedpoint
    : aggregate_state_eq pre_Fix_grammar (aggregate_step pre_Fix_grammar).
  Proof.
    unfold pre_Fix_grammar.
    generalize aggregate_state_max; intro a.
    rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
    edestruct dec as [pf|pf].
    { rewrite Init.Wf.Fix_eq at 1 by (intros; edestruct dec; trivial).
      edestruct dec; [ | congruence ].
      symmetry.
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
        symmetry; assumption. }
      { apply IH; try assumption; []; clear IH.
        unfold aggregate_state_lt.
        rewrite pf; simpl; rewrite andb_true_r.
        pose proof (fun x => aggregate_state_glb_correct x (aggregate_prestep x)) as H'.
        unfold aggregate_step in *.
        edestruct H'; eassumption. } }
  Qed.
End grammar_fixedpoint.
