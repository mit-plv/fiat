Require Import Coq.Strings.String Coq.Lists.List Coq.Program.Program.
Require Export Coq.Classes.RelationPairs.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Reachable.ParenBalancedHiding.Core.
Require Import Fiat.Common.
Require Export Fiat.Common.SetoidInstances.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT}.
  Context {pdata : paren_balanced_hiding_dataT Char}.
  Context (G : grammar Char).

  Local Arguments pbh_new_level / .
  Local Arguments pbh_check_level / .
  Local Arguments pbh_lookup_level / .

  Local Ltac t
    := repeat first [ progress destruct_head prod
                    | progress destruct_head and
                    | progress hnf in *
                    | progress simpl in *
                    | progress subst
                    | omega
                    | congruence
                    | solve [ trivial ]
                    | progress destruct_head bool
                    | intro
                    | idtac;
                      match goal with
                        | [ |- context[match ?e with _ => _ end] ] => destruct e eqn:?
                        | [ |- context[Compare_dec.gt_dec ?a ?b] ] => destruct (Compare_dec.gt_dec a b)
                        | [ H : context[Compare_dec.gt_dec ?a ?b] |- _ ] => destruct (Compare_dec.gt_dec a b)
                        | [ |- _ /\ _ ] => split
                      end ].

  Section check_level.
    Global Instance pbh_check_level_ProperL {ch}
    : Proper (implb * eq ==> implb) (pbh_check_level ch).
    Proof. t. Qed.

    Global Instance pbh_check_level_ProperR {ch}
    : Proper (eq * le ==> implb) (pbh_check_level ch).
    Proof. t. Qed.

    Global Instance pbh_check_level_flip_ProperL {ch}
    : Proper (flip implb * eq ==> flip implb) (pbh_check_level ch).
    Proof. t. Qed.

    Global Instance pbh_check_level_flip_ProperR {ch}
    : Proper (eq * flip le ==> flip implb) (pbh_check_level ch).
    Proof. t. Qed.

    Global Instance pbh_check_level_ProperL'
    : Proper (eq ==> implb * eq ==> implb) pbh_check_level.
    Proof. intros ?? []; apply pbh_check_level_ProperL. Qed.

    Global Instance pbh_check_level_ProperR'
    : Proper (eq ==> eq * le ==> implb) pbh_check_level.
    Proof. intros ?? []; apply pbh_check_level_ProperR. Qed.

    Global Instance pbh_check_level_flip_ProperL'
    : Proper (eq ==> flip implb * eq ==> flip implb) pbh_check_level.
    Proof. intros ?? []; apply pbh_check_level_flip_ProperL. Qed.

    Global Instance pbh_check_level_flip_ProperR'
    : Proper (eq ==> eq * flip le ==> flip implb) pbh_check_level.
    Proof. intros ?? []; apply pbh_check_level_flip_ProperR. Qed.

    Global Instance pbh_check_level_Proper {ch}
    : Proper (implb * le ==> impl) (pbh_check_level ch).
    Proof.
      intros [??] [??] [H0 H1].
      unfold RelCompFun in *; simpl in H0, H1.
      rewrite H0, H1; reflexivity.
    Qed.
  End check_level.

  Section new_level.
    Global Instance pbh_new_level_ProperL {ch}
    : Proper (implb * eq ==> implb * eq) (pbh_new_level ch).
    Proof. t. Qed.

    Global Instance pbh_new_level_ProperR {ch}
    : Proper (eq * le ==> eq * le) (pbh_new_level ch).
    Proof. t. Qed.

    Global Instance pbh_new_level_flip_ProperL {ch}
    : Proper (flip implb * eq ==> flip implb * eq) (pbh_new_level ch).
    Proof. t. Qed.

    Global Instance pbh_new_level_flip_ProperR {ch}
    : Proper (eq * flip le ==> eq * flip le) (pbh_new_level ch).
    Proof. t. Qed.

    Global Instance pbh_new_level_ProperL'
    : Proper (eq ==> implb * eq ==> implb * eq) pbh_new_level.
    Proof. intros ?? []; apply pbh_new_level_ProperL. Qed.

    Global Instance pbh_new_level_ProperR'
    : Proper (eq ==> eq * le ==> eq * le) pbh_new_level.
    Proof. intros ?? []; apply pbh_new_level_ProperR. Qed.

    Global Instance pbh_new_level_flip_ProperL'
    : Proper (eq ==> flip implb * eq ==> flip implb * eq) pbh_new_level.
    Proof. intros ?? []; apply pbh_new_level_flip_ProperL. Qed.

    Global Instance pbh_new_level_flip_ProperR'
    : Proper (eq ==> eq * flip le ==> eq * flip le) pbh_new_level.
    Proof. intros ?? []; apply pbh_new_level_flip_ProperR. Qed.

    Global Instance pbh_new_level_Proper {ch}
    : Proper (implb * le ==> implb * le) (pbh_new_level ch).
    Proof.
      intros [??] [??] [H0 H1]; split;
      unfold RelCompFun in *; simpl in H0, H1;
      rewrite H0, H1; reflexivity.
    Qed.
  End new_level.

  Section lookup_level.
    Print pbh_lookup_level.
    Global Instance pbh_lookup_level_ProperL
    : Proper (implb * eq ==> implb * eq) pbh_lookup_level.
    Proof. t. Qed.

    Global Instance pbh_lookup_level_ProperR
    : Proper (eq * le ==> implb * eq) pbh_lookup_level.
    Proof. t. Qed.

    Global Instance pbh_lookup_level_flip_ProperL
    : Proper (flip implb * eq ==> flip implb * eq) pbh_lookup_level.
    Proof. t. Qed.

    Global Instance pbh_lookup_level_flip_ProperR
    : Proper (eq * flip le ==> flip implb * eq) pbh_lookup_level.
    Proof. t. Qed.

    Global Instance pbh_lookup_level_Proper
    : Proper (implb * le ==> implb * eq) pbh_lookup_level.
    Proof.
      intros [??] [??] [H0 H1]; split;
      unfold RelCompFun in *; simpl in H0, H1;
      rewrite H0, H1; reflexivity.
    Qed.

    Global Instance pbh_lookup_level_Proper_le
    : Proper (implb * le ==> implb * le) pbh_lookup_level.
    Proof.
      intros [??] [??] [H0 H1]; split;
      unfold RelCompFun in *; simpl in H0, H1;
      rewrite H0, H1; reflexivity.
    Qed.
  End lookup_level.
End cfg.

Typeclasses Opaque pbh_new_level pbh_check_level pbh_lookup_level.
