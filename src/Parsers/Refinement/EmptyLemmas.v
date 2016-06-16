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

(** no_parses < nonempty < anything *)

Local Notation pnonempty := tt.

Global Instance might_be_empty_lattice : grammar_fixedpoint_lattice_data unit.
Proof.
  refine {| prestate_lt x y := false;
            prestate_beq x y := true;
            preleast_upper_bound x y := constant tt |};
    repeat match goal with
         | [ |- is_true true ] => reflexivity
         | [ |- ?x = ?x ] => reflexivity
         | _ => assumption
         | [ H : is_true false |- _ ] => exfalso; clear -H; abstract congruence
         | _ => progress simpl in *
         | [ |- RelationClasses.Equivalence _ ] => split
         | _ => intro
         | [ x : bool |- _ ] => destruct x
         | _ => progress unfold Basics.flip
         | [ |- Acc _ _ ] => do 2 constructor; intros; exfalso
         end.
Defined.

Global Instance might_be_empty_aidata {Char} : @AbstractInterpretation Char unit _.
Proof.
  refine {| on_terminal t := constant pnonempty;
            on_nil_production := ⊤;
            precombine_production x y := constant pnonempty |}.
Defined.

Section correctness.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.

  Definition might_be_empty_accurate
             (P : String -> Prop) (nonempty : unit)
    : Prop
    := forall str, P str -> length str <> 0.

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
    | _ => solve [ eauto
                 | exfalso; unfold not in *; eauto ]
    | [ H : ?A -> ?B |- _ ]
      => let H' := fresh in
         assert (H' : A) by eauto;
         specialize (H H'); clear H'
    | [ H : _ |- _ ]
      => setoid_rewrite is_char_parts in H
    | [ x : or _ _ |- _ ] => destruct x
    | [ x : bool |- _ ] => destruct x
    | [ |- and _ _ ] => split
    | _ => progress rewrite ?take_length, ?drop_length
    | [ H : _ |- _ ] => progress rewrite ?take_length, ?drop_length in H
    | _ => omega
    | [ H : ?P ?v, H' : forall str, ?P str -> length str <> 0 |- _ ]
      => apply H' in H
    end.

  Local Ltac t_Proper := repeat t_Proper_step.

  Global Instance might_be_empty_aicdata
    : AbstractInterpretationCorrectness might_be_empty_accurate.
  Proof.
    split; try exact _;
      try solve [ t_Proper ].
  Qed.
End correctness.

Definition might_be_emptyT := lattice_for unit.
Coercion collapse_might_be_empty (x : might_be_emptyT) : bool
  := match x with
     | ⊤ => true
     | constant _ => false
     | ⊥ => false
     end.


Global Instance collapse_might_be_empty_ProperR {R}
  : Proper (lattice_for_beq R ==> eq) collapse_might_be_empty.
Proof.
  intros [|?|] [|?|]; simpl; trivial; congruence.
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
    : might_be_empty_nt G nt = ⊤.
  Proof.
    unfold might_be_empty_nt.
    apply fold_grammar_correct_item in p.
    destruct p as [P [Hp0 p]].
    rewrite fgd_fold_grammar_correct.
    destruct (lookup_state (fold_grammar G) (@of_nonterminal _ (@rdp_list_predata _ G) nt)) eqn:H; [ reflexivity | | ];
    simpl in p; unfold might_be_empty_accurate in p;
      specialize (p _ Hp0); (congruence || tauto).
  Qed.

  Lemma might_be_empty_parse_of
        (nt : String.string)
        (str : String)
        (Hlen : length str = 0)
        (p : parse_of G str (Lookup G nt))
    : might_be_empty_nt G nt = ⊤.
  Proof.
    unfold might_be_empty_nt.
    rewrite fgd_fold_grammar_correct.
    apply fold_grammar_correct in p.
    destruct p as [P [Hp0 p]].
    destruct (lookup_state (fold_grammar G) (@of_nonterminal _ (@rdp_list_predata _ G) nt)) eqn:H; [ reflexivity | | ];
    simpl in p; unfold might_be_empty_accurate in p;
      specialize (p _ Hp0); (congruence || tauto).
  Qed.
End might_be_empty.
