Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretationDefinitions.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.Fix.
Require Import Fiat.Parsers.ContextFreeGrammar.Fix.FromAbstractInterpretation.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope grammar_fixedpoint_scope.

(** no_parses < nonempty < could be empty < anything *)

Inductive nonemptyT := nonempty | could_be_empty.
Scheme Equality for nonemptyT.
Ltac nonemptyT_beq_to_eq :=
  repeat match goal with
         | [ |- is_true (nonemptyT_beq _ _) ] => apply internal_nonemptyT_dec_lb
         | [ H : is_true (nonemptyT_beq _ _) |- _ ]
           => apply internal_nonemptyT_dec_bl in H
         | [ |- nonemptyT_beq _ _ = true ] => apply internal_nonemptyT_dec_lb
         | [ H : nonemptyT_beq _ _ = true |- _ ]
           => apply internal_nonemptyT_dec_bl in H
         end.
Definition nonemptyT_lt (x y : nonemptyT) : bool
  := match x, y with
     | nonempty, nonempty => false
     | nonempty, _ => true
     | _, nonempty => false
     | could_be_empty, could_be_empty => false
     end.

Global Instance nonemptyT_beq_Reflexive : Reflexive nonemptyT_beq.
Proof. repeat intro; nonemptyT_beq_to_eq; reflexivity. Qed.
Global Instance nonemptyT_beq_Symmetric : Symmetric nonemptyT_beq.
Proof. repeat intro; nonemptyT_beq_to_eq; symmetry; assumption. Qed.
Global Instance nonemptyT_beq_Transitive : Transitive nonemptyT_beq.
Proof. repeat intro; nonemptyT_beq_to_eq; etransitivity; eassumption. Qed.
Global Instance nonemptyT_beq_Antisymmetric : Antisymmetric _ eq nonemptyT_beq.
Proof. repeat intro; nonemptyT_beq_to_eq; assumption. Qed.

Global Instance might_be_empty_lattice : grammar_fixedpoint_lattice_data nonemptyT.
Proof.
  refine {| prestate_lt := nonemptyT_lt;
            prestate_beq := nonemptyT_beq;
            preleast_upper_bound x y := if nonemptyT_beq x y
                                        then constant x
                                        else constant could_be_empty |};
    repeat match goal with
         | [ |- is_true true ] => reflexivity
         | [ |- ?x = ?x ] => reflexivity
         | _ => assumption
         | [ H : is_true false |- _ ] => exfalso; clear -H; abstract congruence
         | _ => progress nonemptyT_beq_to_eq
         | _ => progress subst
         | _ => progress simpl in *
         | [ |- RelationClasses.Equivalence _ ] => split
         | _ => intro
         | [ x : bool |- _ ] => destruct x
         | [ x : nonemptyT |- _ ] => destruct x
         | _ => progress unfold Basics.flip
         | [ |- Acc _ _ ] => do 2 constructor; intros; exfalso
         end.
Defined.

Global Instance might_be_empty_aidata {Char} : @AbstractInterpretation Char nonemptyT _.
Proof.
  refine {| on_terminal t := constant nonempty;
            on_nil_production := constant could_be_empty;
            precombine_production x y
            := match x, y with
               | nonempty, _
               | _, nonempty
                 => constant nonempty
               | could_be_empty, could_be_empty => constant could_be_empty
               end |}.
  clear; abstract (intros [] [] ? [] [] ?; simpl in *; (reflexivity || assumption)).
Defined.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition might_be_empty_accurate
             (P : String -> Prop) (nonemptyv : nonemptyT)
    : Prop
    := nonemptyv = nonempty -> forall str, P str -> length str <> 0.

  Local Ltac t_Proper_step :=
    idtac;
    match goal with
    | _ => tauto
    | _ => congruence
    | [ |- is_true _ ] => reflexivity
    | _ => intro
    | _ => progress simpl in *
    | _ => progress unfold might_be_empty_accurate, respectful, state, ensemble_least_upper_bound, ensemble_combine_production, ensemble_on_terminal in *
    | [ H : forall x y, ?R x y -> (_ <-> _) |- _ ]
      => setoid_rewrite (H _ _ (reflexivity _))
    | [ x : lattice_for _ |- _ ] => destruct x
    | [ x : ex _ |- _ ] => destruct x
    | [ x : and _ _ |- _ ] => destruct x
    | _ => progress nonemptyT_beq_to_eq
    | _ => progress subst
    | _ => solve [ eauto
                 | exfalso; unfold not in *; eauto ]
    | [ H : ?A -> ?B |- _ ]
      => let H' := fresh in
         assert (H' : A) by eauto;
         specialize (H H'); clear H'
    | [ H : _ |- _ ]
      => setoid_rewrite is_char_parts in H
    | [ x : or _ _ |- _ ] => destruct x
    | [ x : nonemptyT |- _ ] => destruct x
    | [ x : bool |- _ ] => destruct x
    | [ |- and _ _ ] => split
    | _ => progress rewrite ?take_length, ?drop_length, ?Min.min_0_r, ?Min.min_0_l
    | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length, ?Min.min_0_r, ?Min.min_0_l in H
    | _ => omega
    | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
    | [ H : ?P ?v, H' : forall str, ?P str -> length str <> 0 |- _ ]
      => apply H' in H
    | [ H : ?P ?v, H' : forall str, ?P str -> length str = 0 |- _ ]
      => apply H' in H
    | [ H : ?x = 0, H' : context[?x] |- _ ] => rewrite H in H'
    | [ H : min _ _ = 0 |- _ ] => revert H; apply Min.min_case_strong
    end.

  Local Ltac t_Proper := repeat t_Proper_step.

  Global Instance might_be_empty_aicdata
    : AbstractInterpretationCorrectness might_be_empty_accurate.
  Proof.
    split; try exact _;
      try solve [ t_Proper ].
  Qed.
End correctness.

Definition might_be_emptyT := lattice_for nonemptyT.
Coercion collapse_might_be_empty (x : might_be_emptyT) : bool
  := match x with
     | ⊤ => true
     | constant could_be_empty => true
     | constant nonempty => false
     | ⊥ => false
     end.


Global Instance collapse_might_be_empty_ProperR {R : nonemptyT -> _ -> bool}
       {R_S : Symmetric R}
       {R_AS : Antisymmetric _ eq R}
  : Proper (lattice_for_beq R ==> eq) collapse_might_be_empty.
Proof.
  intros [|[]|] [|[]|]; simpl; trivial; try congruence;
    intro H; specialize (R_S _ _ H); specialize (R_AS _ _ H R_S); congruence.
Qed.
Global Instance collapse_might_be_empty_Proper
  : Proper (state_beq ==> eq) collapse_might_be_empty
  := _.

Definition might_be_empty_data {Char} (G : pregrammar' Char) := fold_grammar_data G.
Existing Class might_be_empty_data.

Section defs.
  Context {Char} (G : pregrammar' Char) {mbedata : might_be_empty_data G}.

  Definition might_be_empty_nt
    : String.string -> might_be_emptyT
    := fun nt => lookup_state mbedata (@of_nonterminal _ (@rdp_list_predata _ G) nt).
End defs.
Global Arguments might_be_empty_nt {_} G {_} _.

Section might_be_empty.
  Context {Char}
          {HSLM : StringLikeMin Char}
          {HSL : StringLike Char}
          {HSLP : StringLikeProperties Char}
          (G : pregrammar' Char)
          {mbedata : might_be_empty_data G}.

  Lemma might_be_empty_parse_of_item_nt
        (nt : String.string)
        (str : String)
        (Hlen : length str = 0)
        (p : parse_of_item G str (NonTerminal nt))
    : collapse_might_be_empty (might_be_empty_nt G nt) = true.
  Proof.
    unfold might_be_empty_nt.
    apply (fold_grammar_correct_item eq_refl) in p.
    destruct p as [P [Hp0 p]].
    rewrite fgd_fold_grammar_correct.
    lazymatch goal with
    | [ p : related _ (lookup_state ?st ?nt) |- collapse_might_be_empty (lookup_state ?st ?nt') = true ]
      => change nt' with nt;
           destruct (lookup_state st nt) as [|[]|] eqn:H
    end; [ reflexivity | | | ];
    simpl in p; unfold might_be_empty_accurate in p;
      try specialize (p eq_refl);
      try specialize (p _ Hp0); (congruence || tauto).
  Qed.

  Lemma might_be_empty_parse_of
        (nt : String.string)
        (str : String)
        (Hlen : length str = 0)
        (p : parse_of G str (Lookup G nt))
    : collapse_might_be_empty (might_be_empty_nt G nt) = true.
  Proof.
    unfold might_be_empty_nt.
    rewrite fgd_fold_grammar_correct.
    apply (fold_grammar_correct eq_refl) in p.
    destruct p as [P [Hp0 p]].
    lazymatch goal with
    | [ p : related _ (lookup_state ?st ?nt) |- collapse_might_be_empty (lookup_state ?st ?nt') = true ]
      => change nt' with nt;
           destruct (lookup_state st nt) as [|[]|] eqn:H
    end; [ reflexivity | | | ];
    simpl in p; unfold might_be_empty_accurate in p;
      try specialize (p eq_refl);
      try specialize (p _ Hp0); (congruence || tauto).
  Qed.
End might_be_empty.
