Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Export Coq.Classes.RelationPairs.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.
Require Import Fiat.Common.SetoidInstances.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT}.

  Class paren_balanced_hiding_dataT :=
    { is_open : Char -> bool;
      is_close : Char -> bool;
      is_bin_op : Char -> bool }.

  Context {pdata : paren_balanced_hiding_dataT}.

  Context (G : grammar Char).

  (**
<<
pbh' ch n "" = true
pbh' ch n (ch :: s) = n > 0 && pbh' ch n s
pbh' ch n ('(' :: s) = pbh' ch (n + 1) s
pbh' ch n (')' :: s) = n > 0 && pbh' ch (n - 1) s
pbh' ch n (_ :: s) = pbh' ch n s

pbh = pbh' '+' 0
>>
*)

  Definition pbh_check_level (ch : Char) (guarded_above_start_level : bool * nat) : bool
    := let '(guarded_above, start_level) := (fst guarded_above_start_level, snd guarded_above_start_level) in
       if is_bin_op ch
       then (guarded_above || (Compare_dec.gt_dec start_level 0 : bool))%bool
       else if is_open ch
            then true
            else if is_close ch
                 then (Compare_dec.gt_dec start_level 0 : bool)
                 else true.

  Definition pbh_new_level (ch : Char) (guarded_above_start_level : bool * nat) : bool * nat
    := let '(guarded_above, start_level) := (fst guarded_above_start_level, snd guarded_above_start_level) in
       if is_bin_op ch
       then (guarded_above, start_level)
       else if is_open ch
            then (guarded_above, S start_level)
            else if is_close ch
                 then (guarded_above, pred start_level)
                 else (guarded_above, start_level).

  Definition pbh_lookup_level (guarded_above_start_level : bool * nat) : bool * nat
    := let '(guarded_above, start_level) := (fst guarded_above_start_level, snd guarded_above_start_level) in
       (guarded_above || Compare_dec.gt_dec start_level 0, 0)%bool.

  Section generic.
    Context (transform_valid : nonterminals_listT -> string -> nonterminals_listT).

    Inductive generic_pbh'_productions : nonterminals_listT -> bool * nat -> productions Char -> Type :=
    | PBHNil : forall valid guarded,
                 generic_pbh'_productions valid guarded nil
    | PBHCons : forall valid guarded pat pats,
                  generic_pbh'_production valid guarded pat
                  -> generic_pbh'_productions valid guarded pats
                  -> generic_pbh'_productions valid guarded (pat::pats)
    with generic_pbh'_production : nonterminals_listT -> bool * nat -> production Char -> Type :=
    | PBHProductionNil : forall valid start_level,
                           generic_pbh'_production valid start_level nil
    | PBHProductionConsNonTerminal : forall valid start_level nt its,
                                       is_valid_nonterminal valid nt
                                       -> generic_pbh'_productions (transform_valid valid nt) (pbh_lookup_level start_level) (Lookup G nt)
                                       -> generic_pbh'_production valid start_level its
                                       -> generic_pbh'_production valid start_level (NonTerminal nt :: its)
    | PBHProductionConsTerminal : forall valid start_level ch its,
                                    pbh_check_level ch start_level
                                    -> generic_pbh'_production valid (pbh_new_level ch start_level) its
                                    -> generic_pbh'_production valid start_level (Terminal ch :: its).
  End generic.

  Definition minimal_pbh'_productions := generic_pbh'_productions remove_nonterminal.
  Definition minimal_pbh'_production := generic_pbh'_production remove_nonterminal.

  Definition pbh'_productions := generic_pbh'_productions (fun valid _ => valid).
  Definition pbh'_production := generic_pbh'_production (fun valid _ => valid).
End cfg.

Global Arguments paren_balanced_hiding_dataT : clear implicits.
