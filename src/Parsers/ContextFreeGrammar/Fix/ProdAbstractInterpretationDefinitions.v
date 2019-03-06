Require Import Coq.Sets.Ensembles.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Prod.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Common.
Require Import Fiat.Common.Instances.
Require Import Fiat.Common.BoolFacts.

Set Implicit Arguments.

Lemma simplify_bool_expr a b (Himpl : is_true a -> is_true b)
  : (a || (b && negb a))%bool = b.
Proof.
  destruct a, b; try reflexivity; simpl; symmetry; apply Himpl; reflexivity.
Qed.

Lemma simplify_bool_expr' a b (Himpl : is_true a -> is_true b)
  : (a || (b && negb a))%bool -> b.
Proof. rewrite simplify_bool_expr by assumption; trivial. Qed.

Section aidata.
  Context {Char : Type} {T T0 T1}
          {fpldata : grammar_fixedpoint_lattice_data T}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}.

  Definition prod_on_terminal
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
    : (Char -> bool) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun P => constant (on_terminal0 P, on_terminal1 P).

  Definition prod_on_nil_production
             (on_nil_production0 : lattice_for T0)
             (on_nil_production1 : lattice_for T1)
    : lattice_for (lattice_for T0 * lattice_for T1)
    := constant (on_nil_production0, on_nil_production1).

  Definition prod_precombine_production_dep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production (precombine_production1 (fst x) (fst y)) (snd x) (snd y)).

  Definition prod_precombine_production_nondep
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (precombine_production1 : T1 -> T1 -> lattice_for T1)
    : (lattice_for T0 * lattice_for T1) -> (lattice_for T0 * lattice_for T1) -> lattice_for (lattice_for T0 * lattice_for T1)
    := fun x y => constant (lattice_for_combine_production precombine_production0 (fst x) (fst y),
                            lattice_for_combine_production precombine_production1 (snd x) (snd y)).

  Local Ltac t_Proper_step :=
    idtac;
    match goal with
    | _ => intro
    | _ => congruence
    | [ |- is_true (_ <= ⊤)%fixedpoint ] => apply top_top
    | [ |- is_true (⊥ <= _)%fixedpoint ] => apply bottom_bottom
    | _ => progress unfold Equality.prod_beq in *
    | _ => progress fold_is_true
    | _ => progress simpl in *
    | [ H : is_true (andb _ _) |- _ ] => apply Bool.andb_true_iff in H
    | [ |- is_true (andb _ _) ] => apply Bool.andb_true_iff
    | _ => progress destruct_head and
    | _ => progress destruct_head prod
    | [ |- and _ _ ] => split
    | [ H : is_true (?R ?x ?y) |- context[lattice_for_combine_production _ ?x] ]
      => is_var x; is_var y; destruct x, y; simpl in H; try congruence
    | [ |- context[match ?x with _ => _ end] ]
      => is_var x; destruct x
    | [ H : Proper _ ?f |- context[?f] ] => apply H; assumption
    | _ => rewrite simplify_bool_expr
          in *
          by (clear; unfold state_le, state_beq, state_lt; bool_congr_setoid; tauto)
    end.

  Local Ltac t_Proper := repeat t_Proper_step.

  Global Instance prod_precombine_production_dep_Proper
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0}
         {HP1 : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1}
    : Proper (prestate_beq ==> prestate_beq ==> state_beq) (prod_precombine_production_dep precombine_production0 precombine_production1).
  Proof. unfold state_le, prestate_le; simpl; t_Proper. Qed.

  Global Instance prod_precombine_production_nondep_Proper
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0}
         {HP1 : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production1}
    : Proper (prestate_beq ==> prestate_beq ==> state_beq) (prod_precombine_production_nondep precombine_production0 precombine_production1).
  Proof. unfold state_le, prestate_le; simpl; t_Proper. Qed.

  Definition prod_aidata_dep
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_nil_production0 : lattice_for T0)
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
             (on_nil_production1 : lattice_for T1)
             (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
             (precombine_production0_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0)
             (precombine_production1_Proper
              : Proper (state_beq ==> state_beq ==> prestate_beq ==> prestate_beq ==> state_beq) precombine_production1)
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'.
  Proof.
    refine {| on_terminal := prod_on_terminal on_terminal0 on_terminal1;
              on_nil_production := prod_on_nil_production on_nil_production0 on_nil_production1;
              precombine_production := prod_precombine_production_dep precombine_production0 precombine_production1 |}.
  Defined.

  Definition prod_aidata_nondep
             (on_terminal0 : (Char -> bool) -> lattice_for T0)
             (on_nil_production0 : lattice_for T0)
             (precombine_production0 : T0 -> T0 -> lattice_for T0)
             (on_terminal1 : (Char -> bool) -> lattice_for T1)
             (on_nil_production1 : lattice_for T1)
             (precombine_production1 : T1 -> T1 -> lattice_for T1)
             (precombine_production0_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production0)
             (precombine_production1_Proper
              : Proper (prestate_beq ==> prestate_beq ==> state_beq) precombine_production1)
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'.
  Proof.
    refine {| on_terminal := prod_on_terminal on_terminal0 on_terminal1;
              on_nil_production := prod_on_nil_production on_nil_production0 on_nil_production1;
              precombine_production := prod_precombine_production_nondep precombine_production0 precombine_production1 |}.
  Defined.

  Global Instance prod_AbstractInterpretation
             {aidata0 : @AbstractInterpretation Char T0 fpldata0}
             {aidata1 : @AbstractInterpretation Char T1 fpldata1}
    : @AbstractInterpretation Char (lattice_for T0 * lattice_for T1) prod_fixedpoint_lattice'
    := { on_terminal := prod_on_terminal on_terminal on_terminal;
         on_nil_production := prod_on_nil_production on_nil_production on_nil_production;
         precombine_production := prod_precombine_production_nondep precombine_production precombine_production }.

  Global Instance prod_precombine_production_dep_Proper_le
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (prestate_le ==> prestate_le ==> state_le) (prod_precombine_production_dep precombine_production0 precombine_production1).
  Proof. unfold state_le, prestate_le; simpl; t_Proper. Qed.

  Global Instance prod_precombine_production_nondep_Proper_le
         {precombine_production0 : T0 -> T0 -> lattice_for T0}
         {precombine_production1 : T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (prestate_le ==> prestate_le ==> state_le) (prod_precombine_production_nondep precombine_production0 precombine_production1).
  Proof.
    intros x y H x' y' H'.
    change (prod_precombine_production_nondep precombine_production0 precombine_production1) with
    (prod_precombine_production_dep precombine_production0 (fun _ _ => precombine_production1)).
    eapply prod_precombine_production_dep_Proper_le; assumption.
  Qed.

  Global Instance prod_precombine_production_nondep_dep_Proper_le
         {precombine_production0 : lattice_for T -> lattice_for T -> T0 -> T0 -> lattice_for T0}
         {precombine_production1 : lattice_for T -> lattice_for T -> T1 -> T1 -> lattice_for T1}
         {HP0 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production0}
         {HP1 : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) precombine_production1}
    : Proper (state_le ==> state_le ==> prestate_le ==> prestate_le ==> state_le) (fun x y => prod_precombine_production_nondep (precombine_production0 x y) (precombine_production1 x y)).
  Proof. unfold state_le, prestate_le; simpl; t_Proper. Qed.
End aidata.

Global Arguments prod_AbstractInterpretation {_ T0 T1 _ _ _ _}, {_ T0 T1 _ _} _ _.

Section aicdata.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
          {T0 T1}
          {fpldata0 : grammar_fixedpoint_lattice_data T0}
          {fpldata1 : grammar_fixedpoint_lattice_data T1}
          (prerelated0 : Ensemble String -> T0 -> Prop)
          (prerelated1 : Ensemble String -> T1 -> Prop).

  Definition prod_prerelated : Ensemble String -> (lattice_for T0 * lattice_for T1) -> Prop
    := fun P st
       => lattice_for_related prerelated0 P (fst st)
          /\ lattice_for_related prerelated1 P (snd st).

  Local Ltac t_step :=
    idtac;
    match goal with
    | _ => intro
    | _ => progress unfold prod_prerelated, ensemble_least_upper_bound, ensemble_combine_production in *
    | _ => progress simpl in *
    | [ |- and _ True ] => split; [ | tauto ]
    | [ |- and True _ ] => split; [ tauto | ]
    | [ H : ?R _ _, H' : is_true _ |- _ ] => specialize (H _ _ H')
    | [ H : ?R _ _, H' : ?R' _ _ |- _ ] => specialize (H _ _ H')
    | _ => progress destruct_head and
    | [ H : is_true (Equality.prod_beq _ _ _ _) |- _ ]
      => unfold Equality.prod_beq in H;
         apply Bool.andb_true_iff in H
    | _ => progress fold_is_true
    | _ => progress destruct_head prod
    | _ => progress destruct_head ex
    | [ |- (lattice_for_related _ _ _ /\ lattice_for_related _ _ _)
           <-> (lattice_for_related _ _ _ /\ lattice_for_related _ _ _) ]
      => apply and_iff_iff_iff_Proper
    | [ H : is_true (state_beq ?x ?y) |- _ ]
      => lazymatch goal with
         | [ |- context[x] ]
           => fail
         | [ |- context[y] ]
           => fail
         | _ => clear dependent x
         end
    | _ => solve [ unfold not in *; eauto; destruct_head or; eauto ]
    | [ H : context[(_ ⊔ ⊥)%fixedpoint] |- _ ]
      => setoid_rewrite bottom_lub_r in H
    | [ H : context[(⊥ ⊔ _)%fixedpoint] |- _ ]
      => setoid_rewrite bottom_lub_l in H
    | _ => progress rewrite ?bottom_lub_r, ?bottom_lub_l
    | [ H : is_true (state_le ?x ?y) |- _ ] => is_var x; destruct x
    | [ H : is_true (state_le ?x ?y) |- _ ] => is_var y; destruct y
    | [ H : is_true (_ || (_ && negb _)) |- _ ]
      => apply simplify_bool_expr' in H; [ | unfold state_le; bool_congr_setoid; tauto ];
         try apply Bool.andb_true_iff in H
    | [ x : lattice_for (_ * _) |- _ ] => destruct x
    | [ x : lattice_for _ |- _ ] => destruct x
    | _ => congruence
    | _ => tauto
    | [ H : (_ ==> _)%signature (?f _) (?g _) |- _ ]
      => lazymatch goal with
         | [ |- context[f] ]
           => fail
         | [ |- context[g] ]
           => fail
         | _ => clear dependent f
         end
    | _ => progress setoid_subst_rel (beq ==> iff)%signature
    | [ |- and _ _ ] => split
    end.

  Local Ltac t := repeat t_step.

  Global Instance prod_prerelated_ext
         {prerelated0_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated0}
         {prerelated1_ext : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prerelated1}
    : Proper ((beq ==> iff) ==> prestate_beq ==> iff) prod_prerelated.
  Proof. t. Qed.

  Lemma prod_related_monotonic
         {related0_monotonic : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prerelated0 v s0 -> lattice_for_related prerelated0 v s1}
         {related1_monotonic : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prerelated1 v s0 -> lattice_for_related prerelated1 v s1}
    : forall s0 s1, (s0 <= s1)%fixedpoint -> forall v, lattice_for_related prod_prerelated v s0 -> lattice_for_related prod_prerelated v s1.
  Proof.
    pose proof (fun v => related0_monotonic ⊥%fixedpoint v (bottom_bottom v)).
    pose proof (fun v => related1_monotonic ⊥%fixedpoint v (bottom_bottom v)).
    unfold state; simpl in *.
    t.
  Qed.

  Lemma prod_lub_correct
        (lub0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint)
        (lub1_correct : forall P1 st1,
            lattice_for_related prerelated1 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint)
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_least_upper_bound P1 P2) (st1 ⊔ st2)%fixedpoint.
  Proof.
    pose proof (fun P1 H1 P2 st2 => lub0_correct P1 ⊥%fixedpoint H1 P2 (constant st2)).
    pose proof (fun P1 H1 P2 st2 => lub1_correct P1 ⊥%fixedpoint H1 P2 (constant st2)).
    pose proof (fun P1 st1 H1 P2 => lub0_correct P1 (constant st1) H1 P2 ⊥%fixedpoint).
    pose proof (fun P1 st1 H1 P2 => lub1_correct P1 (constant st1) H1 P2 ⊥%fixedpoint).
    t.
  Qed.

  Lemma prod_on_terminal_correct
        (on_terminal0 : (Char -> bool) -> lattice_for T0)
        (on_terminal1 : (Char -> bool) -> lattice_for T1)
        (on_terminal0_correct : forall P, lattice_for_related prerelated0 (ensemble_on_terminal P) (on_terminal0 P))
        (on_terminal1_correct : forall P, lattice_for_related prerelated1 (ensemble_on_terminal P) (on_terminal1 P))
    : forall P, lattice_for_related prod_prerelated (ensemble_on_terminal P) (prod_on_terminal on_terminal0 on_terminal1 P).
  Proof. t. Qed.

  Lemma prod_on_nil_production_correct
        (on_nil_production0 : lattice_for T0)
        (on_nil_production1 : lattice_for T1)
        (on_nil_production0_correct : lattice_for_related prerelated0 ensemble_on_nil_production on_nil_production0)
        (on_nil_production1_correct : lattice_for_related prerelated1 ensemble_on_nil_production on_nil_production1)
    : lattice_for_related prod_prerelated ensemble_on_nil_production (prod_on_nil_production on_nil_production0 on_nil_production1).
  Proof. t. Qed.

  Lemma prod_combine_production_dep_correct
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : lattice_for T0 -> lattice_for T0 -> T1 -> T1 -> lattice_for T1)
        (combine_production0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 st1 st2))
        (combine_production1_correct : forall P1 st1 st10,
            lattice_for_related prerelated0 P1 st10
            -> lattice_for_related prerelated1 P1 st1
            -> forall P2 st2 st20,
              lattice_for_related prerelated0 P2 st20
              -> lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production (precombine_production1 st10 st20) st1 st2))
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_dep precombine_production0 precombine_production1) st1 st2).
  Proof. t. Qed.

  Lemma prod_combine_production_nondep_correct
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : T1 -> T1 -> lattice_for T1)
        (combine_production0_correct : forall P1 st1,
            lattice_for_related prerelated0 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated0 P2 st2
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 st1 st2))
        (combine_production1_correct : forall P1 st1,
            lattice_for_related prerelated1 P1 st1
            -> forall P2 st2,
              lattice_for_related prerelated1 P2 st2
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production1 st1 st2))
    : forall P1 st1,
      lattice_for_related prod_prerelated P1 st1
      -> forall P2 st2,
        lattice_for_related prod_prerelated P2 st2
        -> lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_nondep precombine_production0 precombine_production1) st1 st2).
  Proof. t. Qed.

  Lemma prod_combine_production_nondep_correct_specific
        (precombine_production0 : T0 -> T0 -> lattice_for T0)
        (precombine_production1 : T1 -> T1 -> lattice_for T1)
        P1 st1
        (Hrel1 : lattice_for_related prod_prerelated P1 st1)
        P2 st2
        (Hrel2 : lattice_for_related prod_prerelated P2 st2)
        (combine_production0_correct
         : forall st1v,
            st1 = constant st1v
            -> forall st2v,
              st2 = constant st2v
              -> lattice_for_related prerelated0 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production0 (fst st1v) (fst st2v)))
        (combine_production1_correct
         : forall st1v,
            st1 = constant st1v
            -> forall st2v,
              st2 = constant st2v
              -> lattice_for_related prerelated1 (ensemble_combine_production P1 P2) (lattice_for_combine_production precombine_production1 (snd st1v) (snd st2v)))
    : lattice_for_related prod_prerelated (ensemble_combine_production P1 P2) (lattice_for_combine_production (prod_precombine_production_nondep precombine_production0 precombine_production1) st1 st2).
  Proof.
    destruct st1 as [|st1|], st2 as [|st2|];
      try specialize (combine_production0_correct _ eq_refl _ eq_refl);
      try specialize (combine_production1_correct _ eq_refl _ eq_refl);
      t.
  Qed.
End aicdata.

Global Arguments prod_prerelated_ext {_ _ _ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _ _.
Global Arguments prod_related_monotonic {_ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _.
Global Arguments prod_lub_correct {_ _ T0 T1 _ _ prerelated0 prerelated1} _ _ _ _ _ _ _ _.
Global Arguments prod_on_terminal_correct {_ _ _ T0 T1 prerelated0 prerelated1 on_terminal0 on_terminal1} _ _ _.
Global Arguments prod_on_nil_production_correct {_ _ T0 T1 prerelated0 prerelated1 on_nil_production0 on_nil_production1} _ _.
Global Arguments prod_precombine_production_dep_Proper_le {T0 T1 _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_precombine_production_nondep_Proper_le {T0 T1 _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_combine_production_dep_correct {_ _ _ T0 T1 prerelated0 prerelated1 precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_combine_production_nondep_correct {_ _ _ T0 T1 prerelated0 prerelated1 precombine_production0 precombine_production1} _ _ _ _ _ _ _ _.
Global Arguments prod_precombine_production_nondep_dep_Proper_le {T T0 T1 _ _ _ precombine_production0 precombine_production1} _ _ _ _ _ _ _ _ _ _ _ _ _ _.
