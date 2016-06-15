Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.GenericBoolCorrectnessBaseTypes.
Require Import Fiat.Parsers.GenericRecognizerBoolEquality.
Require Fiat.Parsers.BooleanRecognizer.
Require Fiat.Parsers.SimpleRecognizer.

Coercion bool_of_option {A} (x : option A) : bool :=
  match x with
    | Some _ => true
    | None => false
  end.

Section eq.
  Context {Char} {HSLM : StringLikeMin Char} {G : grammar Char}.
  Context {data : @boolean_parser_dataT Char _}
          {rdata : @parser_removal_dataT' _ G _}.
  Context (str : String).

  Local Notation simple_parse_of := (@simple_parse_of Char) (only parsing).
  Local Notation simple_parse_of_production := (@simple_parse_of_production Char) (only parsing).

  Local Existing Instance BooleanRecognizer.boolean_gendata.
  Local Existing Instance SimpleRecognizer.simple_gendata.

  Global Instance boolean_genddata
    : @generic_parser_decidable_data Char BooleanRecognizer.boolean_gendata
    := { parse_nt_T_to_bool x := x;
         parse_item_T_to_bool x := x;
         parse_production_T_to_bool x := x;
         parse_productions_T_to_bool x := x }.

  Global Instance simple_genddata
    : @generic_parser_decidable_data Char SimpleRecognizer.simple_gendata
    := { parse_nt_T_to_bool x := x;
         parse_item_T_to_bool x := x;
         parse_production_T_to_bool x := x;
         parse_productions_T_to_bool x := x }.

  Local Ltac t' :=
    idtac;
    match goal with
    | _ => intro
    | _ => progress simpl in *
    | [ |- ?R ?x ?x ] => reflexivity
    | [ H : option _ |- _ ] => destruct H
    end.

  Local Ltac t := repeat t'.

  Local Obligation Tactic := t.

  Global Program Instance boolean_gendcdata
    : generic_parser_decidable_correctness_data (gendata := BooleanRecognizer.boolean_gendata).

  Global Program Instance simple_gendcdata
    : generic_parser_decidable_correctness_data (gendata := SimpleRecognizer.simple_gendata).

  Definition parse_item'_eq
    : forall (str_matches_nonterminal : nonterminal_carrierT -> bool)
             (str_matches_nonterminal' : nonterminal_carrierT -> option simple_parse_of)
             (str_matches_nonterminal_eq : forall nt,
                 str_matches_nonterminal nt = str_matches_nonterminal' nt)
             (offset : nat) (len : nat)
             (it : item Char),
      BooleanRecognizer.parse_item' str str_matches_nonterminal offset len it = SimpleRecognizer.parse_item' str str_matches_nonterminal' offset len it
    := parse_item'_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.

  Section production.
    Context {len0 : nat}
            (parse_nonterminal
             : forall (offset : nat) (len0_minus_len : nat),
                nonterminal_carrierT
                -> bool)
            (parse_nonterminal'
             : forall (offset : nat) (len0_minus_len : nat),
                nonterminal_carrierT
                -> option simple_parse_of)
            (parse_nonterminal_eq
             : forall offset len0_minus_len nt, parse_nonterminal offset len0_minus_len nt = parse_nonterminal' offset len0_minus_len nt).

    Definition parse_production'_for_eq
      : forall (splits : production_carrierT -> String -> nat -> nat -> list nat)
               (offset : nat)
               (len0_minus_len : nat)
               (prod_idx : production_carrierT),
        BooleanRecognizer.parse_production'_for str parse_nonterminal splits offset len0_minus_len prod_idx
        = SimpleRecognizer.parse_production'_for str parse_nonterminal' splits offset len0_minus_len prod_idx
      := parse_production'_for_eq (len0 := len0) (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str _ _ parse_nonterminal_eq.

    Definition parse_production'_eq
      : forall (offset : nat)
               (len0_minus_len : nat)
               (prod_idx : production_carrierT),
        BooleanRecognizer.parse_production' str parse_nonterminal offset len0_minus_len prod_idx
        = SimpleRecognizer.parse_production' str parse_nonterminal' offset len0_minus_len prod_idx
      := parse_production'_eq (len0 := len0) (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str _ _ parse_nonterminal_eq.
  End production.

  Section productions.
    Context {len0 : nat}
            (parse_nonterminal
             : forall (offset : nat)
                      (len0_minus_len : nat),
                nonterminal_carrierT -> bool)
            (parse_nonterminal'
             : forall (offset : nat)
                      (len0_minus_len : nat),
                nonterminal_carrierT -> option simple_parse_of)
            (parse_nonterminal_eq
             : forall offset len0_minus_len nt,
                parse_nonterminal offset len0_minus_len nt
                = parse_nonterminal' offset len0_minus_len nt).

    Definition parse_productions'_eq
      : forall (offset : nat)
               (len0_minus_len : nat)
               (prods : list production_carrierT),
        BooleanRecognizer.parse_productions' str parse_nonterminal offset len0_minus_len prods
        = SimpleRecognizer.parse_productions' str parse_nonterminal' offset len0_minus_len prods
      := parse_productions'_eq (len0 := len0) (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str _ _ parse_nonterminal_eq.
  End productions.

  Section nonterminals.
    Section step.
      Context {len0 valid_len}
              (parse_nonterminal
               : forall (p : nat * nat),
                  Wf.prod_relation lt lt p (len0, valid_len)
                  -> forall (valid : nonterminals_listT)
                            (offset : nat) (len : nat),
                    len <= fst p -> nonterminal_carrierT -> bool)
              (parse_nonterminal'
               : forall (p : nat * nat),
                  Wf.prod_relation lt lt p (len0, valid_len)
                  -> forall (valid : nonterminals_listT)
                            (offset : nat) (len : nat),
                    len <= fst p -> nonterminal_carrierT -> option simple_parse_of)
              (parse_nonterminal_eq
               : forall (p : nat * nat)
                        (pf : Wf.prod_relation lt lt p (len0, valid_len))
                        (valid : nonterminals_listT)
                        (offset : nat) (len : nat)
                        (pf' : len <= fst p)
                        (nt : nonterminal_carrierT),
                  parse_nonterminal p pf valid offset len pf' nt
                  = parse_nonterminal' p pf valid offset len pf' nt).

      Definition parse_nonterminal_step_eq
        : forall (valid : nonterminals_listT)
                 (offset : nat)
                 (len : nat)
                 (pf : len <= len0)
                 (nt : nonterminal_carrierT),
          BooleanRecognizer.parse_nonterminal_step str parse_nonterminal valid offset pf nt
          = SimpleRecognizer.parse_nonterminal_step str parse_nonterminal' valid offset pf nt
        := parse_nonterminal_step_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str _ _ parse_nonterminal_eq.
    End step.

    Section wf.
      Definition parse_nonterminal_or_abort_eq
      : forall (p : nat * nat)
               (valid : nonterminals_listT)
               (offset : nat) (len : nat)
               (pf : len <= fst p)
               (nt : nonterminal_carrierT),
        BooleanRecognizer.parse_nonterminal_or_abort str p valid offset pf nt
        = SimpleRecognizer.parse_nonterminal_or_abort str p valid offset pf nt
        := parse_nonterminal_or_abort_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.

      Definition parse_nonterminal'_eq
        : forall (nt : nonterminal_carrierT),
          BooleanRecognizer.parse_nonterminal' str nt
          = SimpleRecognizer.parse_nonterminal' str nt
        := parse_nonterminal'_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.

      Definition parse_nonterminal_eq
        : forall (nt : String.string),
          BooleanRecognizer.parse_nonterminal str nt
          = SimpleRecognizer.parse_nonterminal str nt
        := parse_nonterminal_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.
    End wf.
  End nonterminals.

  Definition parse_item_eq
    : forall (it : item Char),
      BooleanRecognizer.parse_item str it
      = SimpleRecognizer.parse_item str it
    := parse_item_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.

  Definition parse_production_eq
    : forall (pat : production_carrierT),
      BooleanRecognizer.parse_production str pat
      = SimpleRecognizer.parse_production str pat
    := parse_production_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.

  Definition parse_productions_eq
    : forall (pats : list production_carrierT),
      BooleanRecognizer.parse_productions str pats
      = SimpleRecognizer.parse_productions str pats
    := parse_productions_eq (gendata := BooleanRecognizer.boolean_gendata) (gendata' := SimpleRecognizer.simple_gendata) str.
End eq.
