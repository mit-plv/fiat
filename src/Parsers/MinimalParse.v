(** * Definition of minimal parse trees *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.BaseTypes.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {Char} {HSL : StringLike Char} {G : grammar Char}.
  Context {predata : @parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}.

  Definition sub_nonterminals_listT (x y : nonterminals_listT) : Prop
    := forall p, is_valid_nonterminal x p -> is_valid_nonterminal y p.

  Lemma remove_nonterminal_3
        {ls ps ps'} (H : is_valid_nonterminal ls ps = false)
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
        {ls ps ps'} (H : is_valid_nonterminal (remove_nonterminal ls ps) ps')
  : ps <> ps'.
  Proof.
    intro H'.
    pose proof (proj2 (remove_nonterminal_2 ls _ _) (or_intror H')).
    congruence.
  Qed.

  Lemma remove_nonterminal_5
        {ls ps ps'} (H : ps <> ps')
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

  (** The [nonterminals_listT] is the current list of valid nonterminals to compare
      against; the extra [String] argument to some of these is the
      [String] we're using to do well-founded recursion, which the
      current [String] must be no longer than. *)

  Inductive minimal_parse_of
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      productions Char -> Type :=
  | MinParseHead : forall len0 valid str pat pats,
                     @minimal_parse_of_production len0 valid str pat
                     -> @minimal_parse_of len0 valid str (pat::pats)
  | MinParseTail : forall len0 valid str pat pats,
                     @minimal_parse_of len0 valid str pats
                     -> @minimal_parse_of len0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      production Char -> Type :=
  | MinParseProductionNil : forall len0 valid str,
                              length str = 0
                              -> @minimal_parse_of_production len0 valid str nil
  | MinParseProductionCons : forall len0 valid str n pat pats,
                               length str <= len0
                               -> @minimal_parse_of_item len0 valid (take n str) pat
                               -> @minimal_parse_of_production len0 valid (drop n str) pats
                               -> @minimal_parse_of_production len0 valid str (pat::pats)
  with minimal_parse_of_item
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      item Char -> Type :=
  | MinParseTerminal : forall len0 valid str ch,
                         str ~= [ ch ]
                         -> @minimal_parse_of_item len0 valid str (Terminal ch)
  | MinParseNonTerminal
    : forall len0 valid str (nt : String.string),
        @minimal_parse_of_nonterminal len0 valid str nt
        -> @minimal_parse_of_item len0 valid str (NonTerminal nt)
  with minimal_parse_of_nonterminal
  : forall (len0 : nat) (valid : nonterminals_listT)
           (str : String),
      String.string -> Type :=
  | MinParseNonTerminalStrLt
    : forall len0 valid (nt : String.string) str,
        length str < len0
        -> is_valid_nonterminal initial_nonterminals_data nt
        -> @minimal_parse_of (length str) initial_nonterminals_data str (Lookup G nt)
        -> @minimal_parse_of_nonterminal len0 valid str nt
  | MinParseNonTerminalStrEq
    : forall len0 str valid nonterminal,
        length str = len0
        -> is_valid_nonterminal initial_nonterminals_data nonterminal
        -> is_valid_nonterminal valid nonterminal
        -> @minimal_parse_of len0 (remove_nonterminal valid nonterminal) str (Lookup G nonterminal)
        -> @minimal_parse_of_nonterminal len0 valid str nonterminal.

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
    intros x y H z w H'.
    hnf in H.
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
    apply NPeano.Nat.nlt_ge.
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
End cfg.
