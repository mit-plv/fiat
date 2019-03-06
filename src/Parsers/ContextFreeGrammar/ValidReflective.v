(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Export Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} (G : pregrammar' Char).

  Let predata := @rdp_list_predata _ G.
  Local Existing Instance predata.

  Definition item_rvalid (it : item Char)
    := match it with
         | Terminal _ => true
         | NonTerminal nt' => is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt')
       end.

  Definition production_rvalid pat
    := fold_right andb true (map item_rvalid pat).

  Definition productions_rvalid pats
    := fold_right andb true (map production_rvalid pats).

  Definition grammar_rvalid
    := fold_right andb true (map productions_rvalid (map (Lookup G) (Valid_nonterminals G))).

  Lemma item_rvalid_correct {it} : is_true (item_rvalid it) <-> item_valid it.
  Proof.
    destruct it; simpl; unfold is_true; try tauto.
  Qed.

  Local Ltac t' :=
    idtac;
    match goal with
      | _ => assumption
      | [ H : False |- _ ] => destruct H
      | _ => progress simpl in *
      | _ => setoid_rewrite Bool.andb_true_iff
      | [ H : context[(_ || _)%bool = true] |- _ ] => setoid_rewrite Bool.orb_true_iff in H
      | [ |- _ <-> _ ] => split
      | [ |- _ /\ _ ] => split
      | _ => intro
      | [ |- List.Forall _ nil ] => constructor
      | [ |- List.Forall _ (_::_) ] => constructor
      | _ => reflexivity
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ <-> _ |- _ ] => destruct H
      | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
      | _ => progress unfold is_true, rdp_list_is_valid_nonterminal in *
      | [ H : List.Forall _ (_::_) |- _ ] => inversion H; clear H
      | _ => progress subst
      | _ => congruence
      | [ H : EqNat.beq_nat _ _ = true |- _ ] => apply EqNat.beq_nat_true in H
      | [ H : Equality.string_beq _ _ = true |- _ ] => apply Equality.string_bl in H
      | [ H : or _ _ |- _ ] => destruct H
      | [ H : forall x, @?A x \/ @?B x -> _ |- _ ]
        => pose proof (fun a b => H a (or_introl b));
          pose proof (fun a b => H a (or_intror b));
          clear H
      | [ H : _ |- _ ] => apply H; apply Equality.string_lb; reflexivity
      | [ H : _ |- _ ] => eapply H; eassumption
      | [ H : _ |- _ ] => eapply H; reflexivity
    end.

  Local Ltac t tac := repeat (t' || tac).

  Lemma production_rvalid_correct {pat} : is_true (production_rvalid pat) <-> production_valid pat.
  Proof.
    unfold production_rvalid, production_valid.
    induction pat;
    t ltac:(idtac;
            match goal with
              | [ |- item_valid _ ] => apply item_rvalid_correct
              | [ H : item_valid _ |- _ ] => apply item_rvalid_correct in H
            end).
  Qed.

  Lemma productions_rvalid_correct {pats} : is_true (productions_rvalid pats) <-> productions_valid pats.
  Proof.
    unfold productions_rvalid, productions_valid.
    induction pats;
    t ltac:(idtac;
            match goal with
              | [ |- production_valid _ ] => apply production_rvalid_correct
              | [ H : production_valid _ |- _ ] => apply production_rvalid_correct in H
            end).
  Qed.

  Lemma grammar_rvalid_correct : is_true grammar_rvalid <-> grammar_valid G.
  Proof.
    unfold grammar_rvalid, grammar_valid.
    induction (Valid_nonterminals G);
      t ltac:(idtac;
              match goal with
                | [ |- productions_valid _ ] => apply productions_rvalid_correct
                | [ H : context[productions_valid _] |- _ ] => setoid_rewrite <- productions_rvalid_correct in H
              end).
  Qed.
End cfg.
