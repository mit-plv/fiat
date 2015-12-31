Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {predata : @parser_computational_predataT Char}.

  Class paren_balanced_hiding_dataT :=
    { is_open : Char -> bool;
      is_close : Char -> bool;
      is_bin_op : Char -> bool }.

  Context {pdata : paren_balanced_hiding_dataT}.

  Context (G : grammar Char).

  (**
<<
pb' ch n "" = (n == 0)
pb' ch n (ch :: s) = n > 0 && pb' ch n s
pb' ch n ('(' :: s) = pb' ch (n + 1) s
pb' ch n (')' :: s) = n > 0 && pb' ch (n - 1) s
pb' ch n (_ :: s) = pb' ch n s

pb = pb' '+' 0
>>
*)

  Definition pb_check_level (hiding : bool) (ch : Char) (start_level : nat) : bool
    := if is_bin_op ch
       then if hiding
            then Compare_dec.gt_dec start_level 0 : bool
            else true
       else if is_open ch
            then true
            else if is_close ch
                 then (Compare_dec.gt_dec start_level 0 : bool)
                 else true.

  Definition pb_new_level (ch : Char) (start_level : nat) : nat
    := if is_bin_op ch
       then start_level
       else if is_open ch
            then (S start_level)
            else if is_close ch
                 then (pred start_level)
                 else start_level.

  Section generic.
    Context (transform_valid : nonterminals_listT -> nonterminal_carrierT -> nonterminals_listT).

    Inductive generic_pb'_productions : nonterminals_listT -> productions Char -> Type :=
    | PBNil : forall valid,
                 generic_pb'_productions valid nil
    | PBCons : forall valid pat pats,
                  generic_pb'_production valid 0 pat
                  -> generic_pb'_productions valid pats
                  -> generic_pb'_productions valid (pat::pats)
    with generic_pb'_production : nonterminals_listT -> nat -> production Char -> Type :=
    | PBProductionNil : forall valid,
                           generic_pb'_production valid 0 nil
    | PBProductionConsNonTerminal : forall valid start_level nt its,
                                       is_valid_nonterminal valid (of_nonterminal nt)
                                       -> generic_pb'_productions (transform_valid valid (of_nonterminal nt)) (Lookup G nt)
                                       -> generic_pb'_production valid start_level its
                                       -> generic_pb'_production valid start_level (NonTerminal nt :: its)
    | PBProductionConsTerminal : forall valid start_level ch its,
                                    pb_check_level false ch start_level
                                    -> generic_pb'_production valid (pb_new_level ch start_level) its
                                    -> generic_pb'_production valid start_level (Terminal ch :: its).
  End generic.

  Definition minimal_pb'_productions := generic_pb'_productions remove_nonterminal.
  Definition minimal_pb'_production := generic_pb'_production remove_nonterminal.

  Definition pb'_productions := generic_pb'_productions (fun valid _ => valid).
  Definition pb'_production := generic_pb'_production (fun valid _ => valid).

  Lemma pb_check_level_le {ch b} {n n'} (Hle : n <= n')
  : pb_check_level b ch n -> pb_check_level b ch n'.
  Proof.
    unfold pb_check_level.
    do 2 edestruct Compare_dec.gt_dec; trivial; try omega; simpl.
    destruct b;
    edestruct is_bin_op; trivial;
    edestruct is_close;
    edestruct is_open;
    unfold is_true;
    trivial.
  Qed.

  Global Instance pb_new_level_Proper {ch}
  : Proper (le ==> le) (pb_new_level ch).
  Proof.
    intros ???.
    unfold pb_new_level.
    edestruct is_bin_op; trivial;
    edestruct is_close;
    edestruct is_open;
    unfold is_true;
    trivial;
    omega.
  Qed.

  Global Instance pb_new_level_flip_Proper {ch}
  : Proper (Basics.flip le ==> Basics.flip le) (pb_new_level ch).
  Proof.
    unfold Basics.flip, pb_new_level.
    intros ???.
    edestruct is_bin_op; trivial;
    edestruct is_close;
    edestruct is_open;
    unfold is_true;
    trivial;
    omega.
  Qed.
End cfg.

Global Arguments paren_balanced_hiding_dataT : clear implicits.
