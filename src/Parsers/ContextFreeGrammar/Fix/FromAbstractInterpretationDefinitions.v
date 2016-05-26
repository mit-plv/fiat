Require Import Coq.Sets.Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Definitions.

Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section general_fold.
  Context {Char : Type}
          {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}.

  Class AbstractInterpretation :=
    { on_terminal : (Char -> bool) -> T;
      on_nil_production : T;
      combine_production : T -> T -> T }.

  Context {aidata : AbstractInterpretation}.

  Context (G : pregrammar' Char).

  Definition fold_item'
             (fold_nt : default_nonterminal_carrierT -> T)
             (it : item Char)
    := match it with
       | Terminal ch => on_terminal ch
       | NonTerminal nt => fold_nt (@of_nonterminal _ (@rdp_list_predata _ G) nt)
       end.

  Lemma fold_item'_ext {f g} (ext : forall b, f b = g b) b
  : fold_item' f b = fold_item' g b.
  Proof.
    unfold fold_item'.
    destruct b; rewrite ?ext; reflexivity.
  Qed.

  Definition fold_production'
             (fold_nt : default_nonterminal_carrierT -> T)
             (its : production Char)
    := List.fold_right
         combine_production
         on_nil_production
         (List.map
            (fold_item' fold_nt)
            its).

  Lemma fold_production'_ext {f g} (ext : forall b, f b = g b) b
  : fold_production' f b = fold_production' g b.
  Proof.
    unfold fold_production'.
    induction b as [ | x ]; try reflexivity; simpl.
    rewrite IHb, (fold_item'_ext ext); reflexivity.
  Qed.

  Definition fold_productions'
             (fold_nt : default_nonterminal_carrierT -> T)
             (its : productions Char)
    := List.fold_right
         greatest_lower_bound
         initial_state
         (List.map
            (fold_production' fold_nt)
            its).

  Lemma fold_productions'_ext {f g} (ext : forall b, f b = g b) b
  : fold_productions' f b = fold_productions' g b.
  Proof.
    unfold fold_productions'.
    induction b as [ | x ]; try reflexivity; simpl.
    rewrite IHb, (fold_production'_ext ext); reflexivity.
  Qed.

  Definition fold_constraints
             (fold_nt : default_nonterminal_carrierT -> T)
             (nt : default_nonterminal_carrierT)
    : T
    := fold_productions'
         fold_nt
         (Lookup_idx G nt).

  Lemma fold_constraints_ext f g (H : forall x, f x = g x) nt
    : fold_constraints f nt = fold_constraints g nt.
  Proof.
    unfold fold_constraints.
    apply fold_productions'_ext.
    intro; apply H.
  Qed.

  Global Instance fold_constraints_Proper
    : Proper (pointwise_relation default_nonterminal_carrierT eq ==> eq ==> eq)
             fold_constraints.
  Proof.
    intros f g H; repeat intro; subst.
    apply fold_constraints_ext; assumption.
  Qed.

  Definition fixedpoint_by_abstract_interpretation : grammar_fixedpoint_data.
  Proof.
    refine {| state := T;
              step_constraints folder nt st := fold_constraints folder nt;
              lattice_data := fpdata |}.
    { repeat intro; apply fold_constraints_Proper; assumption. }
  Defined.

End general_fold.

Section on_ensembles.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.
  Context (G : pregrammar Char).

  Definition ensemble_on_terminal (P : Char -> bool) : Ensemble String
    := (fun str => exists ch, is_true (P ch) /\ str ~= [ ch ])%string_like.

  Definition ensemble_on_nil_production : Ensemble String
    := (fun str => length str = 0).

  Definition ensemble_combine_production : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => exists n, P1 (take n str) /\ P2 (drop n str).

  Definition ensemble_initial : Ensemble String
    := Empty_set _.

  Definition ensemble_greatest_lower_bound : Ensemble String -> Ensemble String -> Ensemble String
    := fun P1 P2 => fun str => P1 str \/ P2 str.

  Definition ensemble_bottom : Ensemble String
    := Full_set _.

  Definition ensemble_le : Ensemble String -> Ensemble String -> Prop
    := fun s0 s1 => forall v, s1 v -> s0 v.

  Definition ensemble_fold_production'
             (fold_nt : default_nonterminal_carrierT -> Ensemble String)
             (its : production Char)
    := List.fold_right
         ensemble_combine_production
         ensemble_on_nil_production
         (List.map
            (fun it =>
               match it with
               | Terminal ch => ensemble_on_terminal ch
               | NonTerminal nt => fold_nt (@of_nonterminal _ (@rdp_list_predata _ G) nt)
               end)
            its).

  Lemma ensemble_fold_production'_ext {f g} (ext : forall b, f b = g b) b
  : ensemble_fold_production' f b = ensemble_fold_production' g b.
  Proof.
    unfold ensemble_fold_production'.
    induction b as [ | x ]; try reflexivity; simpl in *; [].
    rewrite IHb; destruct x; rewrite ?ext; reflexivity.
  Qed.

  Definition ensemble_fold_productions'
             (fold_nt : default_nonterminal_carrierT -> Ensemble String)
             (its : productions Char)
    := List.fold_right
         ensemble_greatest_lower_bound
         ensemble_initial
         (List.map
            (ensemble_fold_production' fold_nt)
            its).

  Lemma ensemble_fold_productions'_ext {f g} (ext : forall b, f b = g b) b
  : ensemble_fold_productions' f b = ensemble_fold_productions' g b.
  Proof.
    unfold ensemble_fold_productions'.
    induction b as [ | x ]; try reflexivity; simpl.
    rewrite IHb, (ensemble_fold_production'_ext ext); reflexivity.
  Qed.

  Definition ensemble_fold_constraints
             (fold_nt : default_nonterminal_carrierT -> Ensemble String)
             (nt : default_nonterminal_carrierT)
    : Ensemble String
    := ensemble_fold_productions'
         fold_nt
         (Lookup_idx G nt).

  Lemma ensemble_fold_constraints_ext f g (H : forall x, f x = g x) nt
    : ensemble_fold_constraints f nt = ensemble_fold_constraints g nt.
  Proof.
    unfold ensemble_fold_constraints.
    apply ensemble_fold_productions'_ext.
    intro; apply H.
  Qed.
End on_ensembles.

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T}.
  Context (G : pregrammar Char)
          (related : Ensemble String -> T -> Prop).

  Class AbstractInterpretationCorrectness :=
    { related_ext : Proper ((beq ==> iff) ==> eq ==> iff) related;
      related_monotonic : forall s0 s1, s0 <= s1 <-> (forall v, related v s1 -> related v s0);
      initial_top : forall s, s <= initial_state;
      initial_related : (related ensemble_initial initial_state);
      bottom_related : (related ensemble_bottom ⊥);
      glb_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_greatest_lower_bound P1 P2) (greatest_lower_bound st1 st2);
      on_terminal_correct
      : forall P,
          related (ensemble_on_terminal P) (on_terminal P);
      on_nil_production_correct
      : related ensemble_on_nil_production on_nil_production;
      combine_production_Proper_eq
      : Proper (state_beq ==> state_beq ==> state_beq) combine_production;
      combine_production_Proper_le
      : Proper (state_le ==> state_le ==> state_le) combine_production;
      combine_production_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (ensemble_combine_production P1 P2) (combine_production st1 st2)
    }.

  Context {aicdata : AbstractInterpretationCorrectness}.

  Lemma fold_production_related
        (mapping : default_nonterminal_carrierT -> Ensemble String)
        st
        (Hmapping : forall nt, related (mapping nt) (st nt))
    : forall pat, related (ensemble_fold_production' G mapping pat) (fold_production' G st pat).
  Proof.
    unfold ensemble_fold_production', fold_production' in *.
    induction pat as [|[|] xs IHxs];
      simpl;
      eauto using on_nil_production_correct, combine_production_correct, on_terminal_correct.
  Qed.

  Lemma fold_productions_related
        (mapping : default_nonterminal_carrierT -> Ensemble String)
        st
        (Hmapping : forall nt, related (mapping nt) (st nt))
    : forall pats, related (ensemble_fold_productions' G mapping pats) (fold_productions' G st pats).
  Proof.
    unfold ensemble_fold_productions', fold_productions' in *.
    induction pats as [|[|] xs IHxs];
      simpl;
      eauto using initial_related, glb_correct, fold_production_related.
  Qed.

  Lemma fold_constraints_related
        (mapping : default_nonterminal_carrierT -> Ensemble String)
        st
        (Hmapping : forall nt, related (mapping nt) (st nt))
    : forall nt, related (ensemble_fold_constraints G mapping nt) (fold_constraints G st nt).
  Proof.
    intro nt.
    unfold ensemble_fold_constraints, fold_constraints.
    apply fold_productions_related; assumption.
  Qed.
End fold_correctness.
