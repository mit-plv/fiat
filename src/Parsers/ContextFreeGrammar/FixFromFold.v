Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Carriers.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fold.
Require Import Fiat.Parsers.ContextFreeGrammar.FixDefinitions.

Set Implicit Arguments.
Local Coercion is_true : bool >-> Sortclass.
Local Open Scope list_scope.
Local Open Scope grammar_fixedpoint_scope.

Section general_fold.
  Context {Char : Type} {T : Type}.
  Context {fgdata : @fold_grammar_data Char T}
          {fpdata : @grammar_fixedpoint_lattice_data T}
          (G : pregrammar' Char).

  Definition fold_constraints
             (fold_nt : default_nonterminal_carrierT -> T)
             (nt : default_nonterminal_carrierT)
    : T
    := fold_productions'
         (fun nt => fold_nt (@of_nonterminal _ (@rdp_list_predata _ G) nt))
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

  Definition fixedpoint_from_fold : grammar_fixedpoint_data.
  Proof.
    refine {| state := T;
              step_constraints folder nt st := fold_constraints folder nt;
              lattice_data := fpdata |}.
    { repeat intro; apply fold_constraints_Proper; assumption. }
  Defined.
End general_fold.

Section fold_correctness.
  Context {Char : Type} {T : Type}.
  Context {FGD : fold_grammar_data Char T}
          {fpdata : @grammar_fixedpoint_lattice_data T}
          (G : pregrammar' Char).

  Class fold_fix_grammar_correctness_computational_data :=
    { Pnt : String.string -> T -> Type;
      Ppat : production Char -> T -> Type;
      Ppats : productions Char -> T -> Type }.

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Global Instance fold_fix_of_fold_ccdata_compat {_ : @fold_grammar_correctness_computational_data Char T G}
    : fold_fix_grammar_correctness_computational_data
    := { Pnt := Fold.Pnt initial_nonterminals_data;
         Ppat := Fold.Ppat initial_nonterminals_data;
         Ppats := Fold.Ppats initial_nonterminals_data }.

  Class fold_fix_grammar_correctness_data :=
    { ffgccd :> fold_fix_grammar_correctness_computational_data;
      Pnt_lift : forall nt value,
          is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)
          -> Ppats (G nt) value
          -> Pnt nt value;
      Pnt_bottom : forall nt,
          is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt) = false
          -> Pnt nt ⊥;
      Pnt_init : forall nt,
          is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt) = true
          -> Pnt nt (initial_state (of_nonterminal nt));
      Pnt_glb : forall nt a b,
          is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt) = true
          -> Pnt nt a
          -> Pnt nt b
          -> Pnt nt (a ⊓ b);
      Ppat_nil : Ppat nil on_nil_production;
      Ppat_cons_nt : forall nt xs p ps,
                       Pnt nt p
                       -> Ppat xs ps
                       -> Ppat (NonTerminal nt::xs)
                               (combine_production (on_nonterminal nt p) ps);
      Ppat_cons_t : forall ch xs ps,
          Ppat xs ps
          -> Ppat (Terminal ch::xs)
                  (combine_production (on_terminal ch) ps);
      Ppats_nil : Ppats nil on_nil_productions;
      Ppats_cons : forall x xs p ps,
          Ppat x p
          -> Ppats xs ps
          -> Ppats (x::xs) (combine_productions p ps) }.

  Context {FGCD : fold_fix_grammar_correctness_data}.

  Lemma fold_production'_correct
        f
        (IHf : forall nt, Pnt nt (f nt))
        pat
  : Ppat pat (fold_production' f pat).
  Proof.
    unfold fold_production'.
    induction pat; simpl.
    { apply Ppat_nil. }
    { edestruct (_ : item _).
      { apply Ppat_cons_t; trivial. }
      { apply Ppat_cons_nt; trivial. } }
  Qed.

  Lemma fold_productions'_correct
        f
        (IHf : forall nt, Pnt nt (f nt))
        pats
  : Ppats pats (fold_productions' f pats).
  Proof.
    unfold fold_productions'.
    induction pats as [ | x xs IHxs ]; intros.
    { simpl; apply Ppats_nil. }
    { simpl; apply Ppats_cons; trivial; [].
      { apply fold_production'_correct; trivial. } }
  Qed.
End fold_correctness.
