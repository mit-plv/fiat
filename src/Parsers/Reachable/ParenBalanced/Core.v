Require Import Coq.Strings.String Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Common.
Require Import Fiat.Common.List.ListFacts.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.LogicFacts.
Require Import Fiat.Common.Equality.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSLM : StringLikeMin Char} {predata : @parser_computational_predataT Char} {HEC : Enumerable Char}.

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

  (** We can check the level for a function [Char -> bool] by enumerating through all the booleans *)
  Definition pb_check_level_fun (hiding : bool) (P : Char -> bool) (start_level : nat) : bool
    := List.fold_right
         andb
         true
         (List.map
            (fun ch => pb_check_level hiding ch start_level)
            (List.filter
               P
               (enumerate Char))).

  Lemma pb_check_level_fun_correct hiding P start_level
  : pb_check_level_fun hiding P start_level
    <-> (forall ch, P ch -> pb_check_level hiding ch start_level).
  Proof.
    unfold pb_check_level_fun.
    setoid_rewrite fold_right_andb_map_in_iff.
    setoid_rewrite filter_In.
    setoid_rewrite (fun x => @and_TrueP_L (In x (enumerate Char)) (P x = true) (enumerate_correct x)).
    reflexivity.
  Qed.

  Definition pb_new_level_fun (P : Char -> bool) (start_level : nat) : list nat
    := List.uniquize
         EqNat.beq_nat
         (List.map
            (fun ch => pb_new_level ch start_level)
            (List.filter
               P
               (enumerate Char))).

  Lemma pb_new_level_fun_correct P start_level new_level
  : pb_new_level_fun P start_level = [new_level]
    <-> ((exists ch, P ch) /\ forall ch, P ch -> new_level = pb_new_level ch start_level).
  Proof.
    unfold pb_new_level_fun.
    rewrite (uniquize_singleton (beq := EqNat.beq_nat) bl lb).
    setoid_rewrite in_map_iff.
    setoid_rewrite filter_In.
    setoid_rewrite (fun x => @and_TrueP_L (In x (enumerate Char)) (P x = true) (enumerate_correct _)).
    split; intro H;
    repeat match goal with
             | _ => split
             | _ => intro
             | _ => progress subst
             | _ => progress destruct_head ex
             | _ => progress split_and
             | _ => progress split_iff
             | [ H : forall x, _ = x -> _ |- _ ] => specialize (H _ eq_refl)
             | [ H : forall x, x = _ -> _ |- _ ] => specialize (H _ eq_refl)
             | [ H : forall x, _ -> _ = _ |- _ ] => unique pose proof (fun x H' => eq_sym (H x H'))
             | _ => solve [ eauto ]
           end.
  Qed.

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
    | PBProductionConsTerminal : forall valid start_level new_level P its,
                                   (forall ch, is_true (P ch) -> pb_check_level false ch start_level)
                                   -> (forall ch, is_true (P ch) -> pb_new_level ch start_level = new_level)
                                    -> generic_pb'_production valid new_level its
                                    -> generic_pb'_production valid start_level (Terminal P :: its).
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
