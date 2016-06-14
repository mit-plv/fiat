(** * Definition of Context Free Grammars *)
Require Import Coq.Strings.String Coq.Lists.List.
Require Export Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Common Fiat.Common.UIP Fiat.Common.List.ListFacts.

Set Implicit Arguments.

Local Open Scope string_like_scope.
Local Open Scope type_scope.

Section cfg.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} (G : grammar Char)
          {predata : @parser_computational_predataT Char}
          (Hvalid : grammar_valid G).

  Local Notation P' nt := (is_true (is_valid_nonterminal initial_nonterminals_data nt)) (only parsing).
  Local Notation P nt := (P' (of_nonterminal nt)) (only parsing).

  Definition Forall_parse_of_item_valid'
             (Forall_parse_of_valid'
              : forall str pats,
                  productions_valid pats
                  -> forall p : parse_of G str pats,
                       Forall_parse_of (fun _ nt' => P nt') p)
             {str it}
             (Hit : item_valid it)
             (p : parse_of_item G str it)
  : Forall_parse_of_item (fun _ nt' => P nt') p.
  Proof.
    destruct p; simpl in *.
    { constructor. }
    { split; try assumption.
      eauto. }
  Defined.

  Fixpoint Forall_parse_of_valid
             {str pats}
             (Hv : productions_valid pats)
             (p : parse_of G str pats)
  : Forall_parse_of (fun _ nt' => P nt') p
  with Forall_parse_of_production_valid
             {str pat}
             (Hv : production_valid pat)
             (p : parse_of_production G str pat)
  : Forall_parse_of_production (fun _ nt' => P nt') p.
  Proof.
    { destruct p; simpl in *.
      { apply Forall_parse_of_production_valid.
        dependent destruction Hv; trivial. }
      { apply (fun Hv => Forall_parse_of_valid _ _ Hv p).
        dependent destruction Hv; trivial. } }
    { destruct p as [p|??? p0 p1]; simpl in *.
      { constructor. }
      { change (Forall_parse_of_item (fun _ nt' => P nt') p0
                * Forall_parse_of_production (fun _ nt' => P nt') p1).
        split.
        { apply Forall_parse_of_item_valid'; try assumption.
          dependent destruction Hv; trivial. }
        { apply Forall_parse_of_production_valid.
          dependent destruction Hv; trivial. } } }
  Defined.

  Definition Forall_parse_of_item_valid
             {str it}
             (Hit : item_valid it)
             (p : parse_of_item G str it)
  : Forall_parse_of_item (fun _ nt' => P nt') p
    := @Forall_parse_of_item_valid' (@Forall_parse_of_valid) str it Hit p.

  Global Instance item_valid_Proper_iff
  : Proper (item_code ==> iff) (@item_valid Char _).
  Proof.
    intros [?|?] [?|?] Heq; simpl in *; subst;
    try solve [ reflexivity
              | destruct Heq ].
  Qed.

  Global Instance production_valid_Proper_iff
  : Proper (production_code ==> iff) (@production_valid Char _).
  Proof.
    intros ?? Heq; induction Heq; try reflexivity.
    split; intro H'; inversion_clear H'; constructor;
    setoid_subst_rel (@item_code Char);
    try assumption;
    split_iff; unfold production_valid in *; eauto with nocore.
  Qed.

  Global Instance productions_valid_Proper_iff
  : Proper (productions_code ==> iff) (@productions_valid Char _).
  Proof.
    intros ?? Heq; induction Heq; try reflexivity.
    split; intro H'; inversion_clear H'; constructor;
    setoid_subst_rel (@production_code Char);
    try assumption;
    split_iff; unfold productions_valid in *; eauto with nocore.
  Qed.
End cfg.

Section uip.
  Context {Char : Type} {HSLM : StringLikeMin Char} (G : grammar Char)
          {predata : @parser_computational_predataT Char}.

  Lemma item_valid_proof_irrelevance {it : item Char} (x y : item_valid it)
  : x = y.
  Proof.
    destruct it; simpl in *;
    try destruct x, y; trivial.
    apply dec_eq_uip; decide equality.
  Qed.

  Lemma production_valid_proof_irrelevance
        {p : production Char} (x y : production_valid p)
  : x = y.
  Proof.
    apply Forall_proof_irrelevance, @item_valid_proof_irrelevance.
  Qed.

  Lemma productions_valid_proof_irrelevance
        {p : productions Char} (x y : productions_valid p)
  : x = y.
  Proof.
    apply Forall_proof_irrelevance, @production_valid_proof_irrelevance.
  Qed.
End uip.

Section app.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} (G : grammar Char)
          {predata : @parser_computational_predataT Char}.

  Lemma hd_production_valid
        (it : item Char)
        (its : production Char)
        (H : production_valid (it :: its))
  : item_valid it.
  Proof.
    unfold production_valid in *.
    inversion H; subst; assumption.
  Qed.

  Lemma production_valid_cons
        (it : item Char)
        (its : production Char)
        (H : production_valid (it :: its))
  : production_valid its.
  Proof.
    unfold production_valid in *.
    inversion H; subst; assumption.
  Qed.

  Lemma production_valid_app
        (pat pat' : production Char)
        (H : production_valid (pat ++ pat'))
  : production_valid pat'.
  Proof.
    induction pat; simpl in *; trivial.
    eapply IHpat, production_valid_cons; eassumption.
  Qed.

  Lemma hd_productions_valid
        (p : production Char)
        (ps : productions Char)
        (H : productions_valid (p :: ps))
  : production_valid p.
  Proof.
    unfold productions_valid in *.
    inversion H; subst; assumption.
  Qed.

  Lemma productions_valid_cons
        (p : production Char)
        (ps : productions Char)
        (H : productions_valid (p :: ps))
  : productions_valid ps.
  Proof.
    unfold productions_valid in *.
    inversion H; subst; assumption.
  Qed.

  Lemma productions_valid_app
        (pat pat' : productions Char)
        (H : productions_valid (pat ++ pat'))
  : productions_valid pat'.
  Proof.
    induction pat; simpl in *; trivial.
    eapply IHpat, productions_valid_cons; eassumption.
  Qed.

  (** Convenience lemmas *)
  Section convenience.
    Context {rdata : @parser_removal_dataT' _ G _}
            (Hvalid : grammar_valid G).

    Lemma reachable_production_valid
          (its : production Char)
          (Hreach : production_is_reachable G its)
    : production_valid its.
    Proof.
      destruct Hreach as [nt [prefix [Hreach Hreach']]].
      specialize (Hvalid nt Hreach).
      unfold productions_valid in Hvalid.
      rewrite Forall_forall in Hvalid.
      eapply production_valid_app.
      apply Hvalid; eassumption.
    Qed.
  End convenience.
End app.
