(** * Proof that SimpleRecognizer outputs correct parse trees *)
Require Import Coq.Classes.Morphisms.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectness.
Require Import Fiat.Parsers.ContextFreeGrammar.SimpleCorrectnessMorphisms.
Require Import Fiat.Parsers.BaseTypes Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.GenericBaseTypes Fiat.Parsers.GenericCorrectnessBaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.GenericRecognizerMin.
Require Import Fiat.Parsers.SimpleRecognizer.
Require Import Fiat.Common.

Section convenience.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {cdata : @boolean_parser_completeness_dataT' Char _ _ G _}
          {rdata : @parser_removal_dataT' _ G _}
          (gvalid : grammar_valid G).

  Local Instance gencdata_default_proper {A}
    : Proper (beq ==> eq ==> eq ==> eq ==> Basics.impl) (fun _ (_ : A) (x y : bool) => y = x).
  Proof.
    repeat intro; repeat subst; reflexivity.
  Qed.

  Local Ltac t' :=
    idtac;
    match goal with
    | _ => intro
    | _ => assumption
    | [ H : False |- _ ] => solve [ destruct H ]
    | [ H : true = false |- _ ] => solve [ inversion H ]
    | [ H : false = true |- _ ] => solve [ inversion H ]
    | [ H : Some _ = None |- _ ] => solve [ inversion H ]
    | [ H : None = Some _ |- _ ] => solve [ inversion H ]
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H
    | _ => progress subst
    | [ H : iff _ _ |- _ ] => destruct H
    | [ H : and _ _ |- _ ] => destruct H
    | [ H : ex _ |- _ ] => destruct H
    | [ |- and _ _ ] => split
    | [ |- iff _ _ ] => split
    | [ H : beq ?x ?y |- context[?y] ]
      => is_var y; rewrite <- H; clear H y
    | [ H : forall x, Some _ = Some x -> _ |- _ ]
      => specialize (H _ eq_refl)
    | _ => progress unfold not in *
    | _ => progress specialize_by assumption
    | _ => progress specialize_by (exact eq_refl)
    | _ => progress specialize_by congruence
    | _ => tauto
    | _ => congruence
    | _ => progress simpl in *
    | _ => progress simpl_simple_parse_of_correct
    | [ |- exists p, Some ?x = Some p /\ _ ] => exists x
    | [ H : ?x = 0 \/ _, H' : andb (EqNat.beq_nat ?x (S _)) _ = true |- _ ]
      => destruct H
    | [ H : andb _ (char_at_matches _ _ _) = true |- _ ]
      => apply char_at_matches_is_char_no_ex in H; [ | assumption ]
    | [ H : context[match get ?n ?str with _ => _ end] |- _ ]
      => destruct (get n str) eqn:?
    | [ |- context[unsafe_get _ _] ]
      => erewrite unsafe_get_correct by eassumption
    | [ H : is_true ?x |- context[?x] ] => rewrite H
    | [ H : option_orb ?x ?y = None -> False |- _ ] => is_var x; is_var y; destruct x, y
    | [ H : option_orb ?x _ = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_orb _ ?x = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_orb ?x ?y = Some _ |- _ ] => is_var x; is_var y; destruct x, y
    | [ H : option_orb ?x _ = Some _ |- _ ] => is_var x; destruct x
    | [ H : option_orb _ ?x = Some _ |- _ ] => is_var x; destruct x
    | [ H : option_simple_parse_of_orb ?x ?y = None -> False |- _ ] => is_var x; is_var y; destruct x, y
    | [ H : option_simple_parse_of_orb ?x _ = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_simple_parse_of_orb _ ?x = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_simple_parse_of_orb ?x ?y = Some _ |- _ ] => is_var x; is_var y; destruct x, y
    | [ H : option_simple_parse_of_orb ?x _ = Some _ |- _ ] => is_var x; destruct x
    | [ H : option_simple_parse_of_orb _ ?x = Some _ |- _ ] => is_var x; destruct x
    | [ H : option_SimpleParseProductionCons ?x ?y = None -> False |- _ ] => is_var x; is_var y; destruct x, y
    | [ H : option_SimpleParseProductionCons ?x _ = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_SimpleParseProductionCons _ ?x = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_SimpleParseProductionCons ?x ?y = Some _ |- _ ] => is_var x; is_var y; destruct x, y
    | [ H : option_SimpleParseProductionCons ?x _ = Some _ |- _ ] => is_var x; destruct x
    | [ H : option_SimpleParseProductionCons _ ?x = Some _ |- _ ] => is_var x; destruct x
    | [ H : ?x = None -> False |- _ ] => is_var x; destruct x
    | [ H : ?x = true -> _ -> False |- _ ] => is_var x; destruct x
    | [ H : option_map _ ?x = None -> False |- _ ] => is_var x; destruct x
    | [ H : option_map _ ?x = Some _ |- _ ] => is_var x; destruct x
    | [ H : orb ?x _ = true |- _ ] => is_var x; destruct x
    | [ H : option_orb ?x _ = None |- _ ] => is_var x; destruct x
    | [ H : option_simple_parse_of_orb ?x _ = None |- _ ] => is_var x; destruct x
    | [ H : List.In (to_nonterminal _) _ |- _ ]
      => apply initial_nonterminals_correct' in H
    | [ H : is_true (is_valid_nonterminal _ (of_nonterminal _)) |- _ ]
      => apply initial_nonterminals_correct in H
    | [ H : context[to_nonterminal (of_nonterminal _)] |- _ ]
      => rewrite to_of_nonterminal in H by assumption
    | [ H : ?x = _ |- context[match ?x with _ => _ end] ] => rewrite H
    | [ |- context[drop _ (substring _ _ _)] ]
      => setoid_rewrite drop_take
    | [ |- context[drop _ (drop _ _)] ]
      => setoid_rewrite drop_drop
    | [ |- context[take _ (take _ _)] ]
      => setoid_rewrite take_take
    | [ H : context[substring (?offset + ?loc) _ _] |- context[substring (_ + ?offset) _ _] ]
      => rewrite (Plus.plus_comm offset loc) in H
    | [ H : context[to_production (production_tl _)] |- _ ]
      => rewrite production_tl_correct in H
    | [ H : ?x = _, H' : context[List.tl ?x] |- _ ]
      => rewrite H in H'
    | _ => solve [ eauto using ex_intro, conj with nocore ]
    | [ |- List.In (to_nonterminal _) _ ]
      => apply initial_nonterminals_correct'
    | [ |- is_true (is_valid_nonterminal _ (of_nonterminal _)) ]
      => apply initial_nonterminals_correct
    | [ |- context[Lookup _ (to_nonterminal _)] ]
      => rewrite <- nonterminal_to_production_correct' by assumption
    | [ |- context[length (substring _ 0 _)] ]
      => rewrite substring_correct0_length
    end.

  Local Ltac t := repeat t'.

  Local Obligation Tactic := try solve [ t ].

  Local Existing Instance simple_gendata.
  Global Program Instance simple_gencdata1 : generic_parser_correctness_dataT
    := { parse_nt_is_correct str nt exp act
         := exp = true <-> act <> None;
         parse_item_is_correct str it exp act
         := exp = true <-> act <> None;
         parse_production_is_correct str p exp act
         := exp = true <-> act <> None;
         parse_productions_is_correct str p exp act
         := exp = true <-> act <> None }.

  Global Program Instance simple_gencdata2 : generic_parser_correctness_dataT
    := { parse_nt_is_correct str nt exp act
         := (exp = true <-> act <> None)
            /\ forall p, act = Some p -> simple_parse_of_item_correct G str (NonTerminal (to_nonterminal nt)) (SimpleParseNonTerminal (to_nonterminal nt) p);
         parse_item_is_correct str it exp act
         := (exp = true <-> act <> None)
            /\ forall p, act = Some p -> simple_parse_of_item_correct G str it p;
         parse_production_is_correct str p exp act
         := (exp = true <-> act <> None)
            /\ forall t, act = Some t -> simple_parse_of_production_correct G str (to_production p) t;
         parse_productions_is_correct str p exp act
         := (exp = true <-> act <> None)
            /\ forall t, act = Some t -> simple_parse_of_correct G str (List.map to_production p) t }.

  Local Ltac t_parse_correct :=
    repeat match goal with
           | _ => intro
           | _ => assumption
           | _ => progress simpl in *
           | _ => progress destruct_head iff
           | _ => progress destruct_head and
           | _ => progress specialize_by congruence
           | [ H : forall p, _ = Some p -> _, H' : _ = Some _ |- _ ]
             => specialize (H _ H')
           end.

  Definition parse_item_correct
             str it p
    : parse_item str it = Some p -> simple_parse_of_item_correct G str it p.
  Proof.
    pose proof (parse_item_correct (gcdata := simple_gencdata1) str it).
    pose proof (parse_item_correct (gcdata := simple_gencdata2) str it).
    t_parse_correct.
  Qed.

  Definition parse_nonterminal_correct
             str nt p
    : parse_nonterminal str nt = Some p
      -> simple_parse_of_item_correct G str (NonTerminal nt) (SimpleParseNonTerminal nt p).
  Proof.
    pose proof (parse_nonterminal_correct (gcdata := simple_gencdata1) str nt).
    pose proof (parse_nonterminal_correct (gcdata := simple_gencdata2) str nt).
    t_parse_correct.
    match goal with H : _ |- _ => rewrite to_of_nonterminal in H end.
    { assumption. }
    { unfold parse_nonterminal in H1.
      pose proof (parse_nonterminal_correct (gcdata := simple_gencdata1) str nt) as H'.
      destruct (is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt)) eqn:H''.
      { apply initial_nonterminals_correct in H''; assumption. }
      { rewrite parse_nonterminal_invalid_none' in H'; simpl in H'.
        { destruct_head iff.
          specialize_by congruence; congruence. }
        { intro H'''.
          apply initial_nonterminals_correct in H'''.
          congruence. } } }
  Qed.
End convenience.
