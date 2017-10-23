(** * Lemmas about the common part of the interface of the CFG parser *)
Require Import Coq.Classes.RelationClasses Coq.Setoids.Setoid.
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.BaseTypes.

Set Implicit Arguments.

Local Open Scope string_like_scope.

Local Coercion is_true : bool >-> Sortclass.

Section recursive_descent_parser.
  Context {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {G : grammar Char}
          {predata : @parser_computational_predataT Char}
          {rdata' : @parser_removal_dataT' _ G _}.

  Lemma remove_nonterminal_3
        {ls ps ps'} (H0 : is_valid_nonterminal ls ps = false)
  : is_valid_nonterminal (remove_nonterminal ls ps) ps' = is_valid_nonterminal ls ps'.
  Proof.
    case_eq (is_valid_nonterminal (remove_nonterminal ls ps) ps');
    case_eq (is_valid_nonterminal ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_nonterminal_1 in H''
          | apply remove_nonterminal_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_nonterminal_4
        {ls ps ps'} (H0 : is_valid_nonterminal (remove_nonterminal ls ps) ps')
  : ps <> ps'.
  Proof.
    intro H'.
    pose proof (proj2 (remove_nonterminal_2 ls _ _) (or_intror H')).
    congruence.
  Qed.

  Lemma remove_nonterminal_5
        {ls ps ps'} (H0 : ps <> ps')
  : is_valid_nonterminal (remove_nonterminal ls ps) ps' = is_valid_nonterminal ls ps'.
  Proof.
    case_eq (is_valid_nonterminal (remove_nonterminal ls ps) ps');
    case_eq (is_valid_nonterminal ls ps');
    intros H' H'';
    try reflexivity;
    exfalso;
    first [ apply remove_nonterminal_1 in H''
          | apply remove_nonterminal_2 in H''; destruct H''; subst ];
    congruence.
  Qed.

  Lemma remove_nonterminal_6
        ls ps
  : is_valid_nonterminal (remove_nonterminal ls ps) ps = false.
  Proof.
    apply remove_nonterminal_2; right; reflexivity.
  Qed.

  Global Instance sub_nonterminals_listT_Reflexive : Reflexive sub_nonterminals_listT
    := fun x y f => f.

  Global Instance sub_nonterminals_listT_Transitive : Transitive sub_nonterminals_listT.
  Proof.
    lazy; auto.
  Defined.

  Global Add Parametric Morphism : remove_nonterminal
  with signature sub_nonterminals_listT ==> eq ==> sub_nonterminals_listT
    as remove_nonterminal_mor.
  Proof.
    intros x y H0 z w H'.
    hnf in H0.
    pose proof (remove_nonterminal_4 H').
    apply remove_nonterminal_1 in H'.
    rewrite remove_nonterminal_5 by assumption.
    auto.
  Qed.

  Lemma sub_nonterminals_listT_remove ls ps
  : sub_nonterminals_listT (remove_nonterminal ls ps) ls.
  Proof.
    intros p.
    apply remove_nonterminal_1.
  Qed.

  Lemma sub_nonterminals_listT_remove_2 {ls ls' ps} (H : sub_nonterminals_listT ls ls')
  : sub_nonterminals_listT (remove_nonterminal ls ps) ls'.
  Proof.
    etransitivity; eauto using sub_nonterminals_listT_remove.
  Qed.

  Lemma sub_nonterminals_listT_remove_3 {ls ls' p}
        (H0 : is_valid_nonterminal ls p = false)
        (H1 : sub_nonterminals_listT ls ls')
  : sub_nonterminals_listT ls (remove_nonterminal ls' p).
  Proof.
    intros p' H'.
    rewrite remove_nonterminal_5; intuition (subst; eauto; congruence).
  Qed.

  Lemma remove_nonterminal_noninc' {ls nt}
  : nonterminals_length (remove_nonterminal ls nt) <= nonterminals_length ls.
  Proof.
    apply Nat.nlt_ge.
    apply remove_nonterminal_noninc.
  Qed.

  Lemma nonempty_nonterminals {ls nt} (H : is_valid_nonterminal ls nt)
  : 0 < nonterminals_length ls.
  Proof.
    eapply Lt.le_lt_trans;
    [ apply Le.le_0_n
    | exact (remove_nonterminal_dec ls nt H) ].
  Qed.

  Lemma nonempty_nonterminals' {ls nt} (H : is_valid_nonterminal ls nt)
  : negb (EqNat.beq_nat (nonterminals_length ls) 0).
  Proof.
    pose proof (nonempty_nonterminals H).
    destruct (nonterminals_length ls); simpl; try reflexivity; try omega.
  Qed.

  Lemma nonterminal_to_production_correct'
    : forall nt,
      is_valid_nonterminal initial_nonterminals_data nt
      -> List.map to_production (nonterminal_to_production nt)
         = Lookup G (to_nonterminal nt).
  Proof.
    intros nt H.
    rewrite <- (of_to_nonterminal nt) at 1 by assumption.
    rewrite nonterminal_to_production_correct by (apply initial_nonterminals_correct'; assumption).
    reflexivity.
  Qed.

  Lemma is_valid_nonterminal_of_to_nonterminal valids nt
    : sub_nonterminals_listT valids initial_nonterminals_data
      -> is_valid_nonterminal valids (of_nonterminal (to_nonterminal nt)) = is_valid_nonterminal valids nt.
  Proof.
    intro Hvalid.
    match goal with
    | [ |- ?lhs = ?rhs ] => destruct lhs eqn:?, rhs eqn:?; first [ reflexivity | exfalso ]
    end;
      repeat match goal with
             | [ H : is_valid_nonterminal _ _ = _ |- False ]
               => rewrite of_to_nonterminal in H
             | _ => congruence
             | _ => apply Hvalid; assumption
             | _ => rewrite initial_nonterminals_correct', <- initial_nonterminals_correct; apply Hvalid; assumption
             end.
  Qed.
End recursive_descent_parser.
