Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.

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
pbh' ch n "" = (n == 0)
pbh' ch n (ch :: s) = n > 0 && pbh' ch n s
pbh' ch n ('(' :: s) = pbh' ch (n + 1) s
pbh' ch n (')' :: s) = n > 0 && pbh' ch (n - 1) s
pbh' ch n (_ :: s) = pbh' ch n s

pbh = pbh' '+' 0
>>
*)

  Definition pbh_check_level (ch : Char) (start_level : nat) : bool
    := if is_bin_op ch
       then (Compare_dec.gt_dec start_level 0 : bool)
       else if is_open ch
            then true
            else if is_close ch
                 then (Compare_dec.gt_dec start_level 0 : bool)
                 else true.

  Definition pbh_new_level (ch : Char) (start_level : nat) : nat
    := if is_bin_op ch
       then start_level
       else if is_open ch
            then (S start_level)
            else if is_close ch
                 then (pred start_level)
                 else start_level.

  Section generic.
    Context (transform_valid : nonterminals_listT -> string -> nonterminals_listT).

    Inductive generic_pbh'_productions : nonterminals_listT -> bool -> productions Char -> Type :=
    | PBHNil : forall valid guarded,
                 generic_pbh'_productions valid guarded nil
    | PBHCons : forall valid (guarded : bool) pat pats,
                  generic_pbh'_production valid (if guarded then 1 else 0) pat
                  -> generic_pbh'_productions valid guarded pats
                  -> generic_pbh'_productions valid guarded (pat::pats)
    with generic_pbh'_production : nonterminals_listT -> nat -> production Char -> Type :=
    | PBHProductionNil : forall valid start_level,
                           generic_pbh'_production valid start_level nil
    | PBHProductionConsNonTerminal : forall valid start_level nt its,
                                       is_valid_nonterminal valid nt
                                       -> generic_pbh'_productions (transform_valid valid nt) (match start_level with 0 => false | _ => true end) (Lookup G nt)
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

  Lemma pbh_check_level_le {ch} {n n'} (Hle : n <= n')
  : pbh_check_level ch n -> pbh_check_level ch n'.
  Proof.
    unfold pbh_check_level.
    do 2 edestruct Compare_dec.gt_dec; trivial; try omega; simpl.
    edestruct is_bin_op;
      edestruct is_close;
      edestruct is_open;
      unfold is_true;
      trivial.
  Qed.

  Global Instance pbh_new_level_Proper {ch}
  : Proper (le ==> le) (pbh_new_level ch).
  Proof.
    intros ???.
    unfold pbh_new_level.
    edestruct is_bin_op;
      edestruct is_close;
      edestruct is_open;
      unfold is_true;
      trivial;
      omega.
  Qed.

  Global Instance pbh_new_level_flip_Proper {ch}
  : Proper (Basics.flip le ==> Basics.flip le) (pbh_new_level ch).
  Proof.
    unfold Basics.flip, pbh_new_level.
    intros ???.
    edestruct is_bin_op;
      edestruct is_close;
      edestruct is_open;
      unfold is_true;
      trivial;
      omega.
  Qed.
End cfg.

Global Arguments paren_balanced_hiding_dataT : clear implicits.
