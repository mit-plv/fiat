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
    { on_terminal : Reflective.RCharExpr Char -> T;
      on_nil_production : T;
      combine_production : T -> T -> T }.

  Context {aidata : AbstractInterpretation}.

  Context (G : pregrammar Char).

  Definition fold_production'
             (fold_nt : default_nonterminal_carrierT -> T)
             (its : Reflective.rproduction Char)
    := List.fold_right
         combine_production
         on_nil_production
         (List.map
            (fun it =>
               match it with
               | Reflective.RTerminal ch => on_terminal ch
               | Reflective.RNonTerminal nt => fold_nt (@of_nonterminal _ (@rdp_list_predata _ G) nt)
               end)
            its).

  Lemma fold_production'_ext {f g} (ext : forall b, f b = g b) b
  : fold_production' f b = fold_production' g b.
  Proof.
    unfold fold_production'.
    induction b as [ | x ]; try reflexivity; simpl in *; [].
    rewrite IHb; destruct x; rewrite ?ext; reflexivity.
  Qed.

  Definition fold_productions'
             (fold_nt : default_nonterminal_carrierT -> T)
             (its : Reflective.rproductions Char)
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
         (RLookup_idx G nt).

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

Section fold_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char}
          {irdata : Reflective.interp_RCharExpr_data Char}.
  Context {T : Type}.
  Context {fpdata : @grammar_fixedpoint_lattice_data T}
          {aidata : @AbstractInterpretation Char T}.
  Context (G : pregrammar Char).

  Class AbstractInterpretationCorrectness (related : Ensemble String -> T -> Prop) :=
    { related_ext : Proper ((beq ==> iff) ==> eq ==> iff) related;
      related_monotonic : forall s0 s1, s0 <= s1 <-> (forall v, related v s1 -> related v s0);
      bottom_related : (related (Full_set _) ⊥);
      on_terminal_correct
      : forall P,
          related (fun str => exists ch, Reflective.interp_RCharExpr P ch /\ str ~= [ ch ])%string_like
                  (on_terminal P);
      on_nil_production_correct
      : related (fun str => length str = 0) on_nil_production;
      combine_production_Proper_eq
      : Proper (state_beq ==> state_beq ==> state_beq) combine_production;
      combine_production_Proper_le
      : Proper (state_le ==> state_le ==> state_le) combine_production;
      combine_production_correct
      : forall P1 st1,
          related P1 st1
          -> forall P2 st2,
            related P2 st2
            -> related (fun str => exists n, P1 (take n str) /\ P2 (drop n str))
                       (combine_production st1 st2)
    }.
End fold_correctness.
