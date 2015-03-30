(** * Definition of minimal parse trees *)
Require Import Coq.Strings.String Coq.Lists.List Coq.Setoids.Setoid.
Require Import ADTSynthesis.Parsers.ContextFreeGrammar.
Require Import ADTSynthesis.Parsers.BaseTypes.

Local Coercion is_true : bool >-> Sortclass.

Set Implicit Arguments.
Local Open Scope string_like_scope.

Section cfg.
  Context {string} {HSL : StringLike string} {G : grammar string}.
  Context {predata : @parser_computational_predataT}
          {rdata' : @parser_removal_dataT' predata}.

  Definition sub_nonterminals_listT (x y : nonterminals_listT) : Prop
    := forall p, is_valid_nonterminal x p -> is_valid_nonterminal y p.

  Context (nonterminals_listT_R_respectful : forall x y,
                                        sub_nonterminals_listT x y
                                        -> x <> y
                                        -> nonterminals_listT_R x y).

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
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      productions string -> Type :=
  | MinParseHead : forall str0 valid str pat pats,
                     @minimal_parse_of_production str0 valid str pat
                     -> @minimal_parse_of str0 valid str (pat::pats)
  | MinParseTail : forall str0 valid str pat pats,
                     @minimal_parse_of str0 valid str pats
                     -> @minimal_parse_of str0 valid str (pat::pats)
  with minimal_parse_of_production
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      production string -> Type :=
  | MinParseProductionNil : forall str0 valid str,
                              length str = 0
                              -> @minimal_parse_of_production str0 valid str nil
  | MinParseProductionCons : forall str0 valid str n pat pats,
                               str ≤s str0
                               -> @minimal_parse_of_item str0 valid (take n str) pat
                               -> @minimal_parse_of_production str0 valid (drop n str) pats
                               -> @minimal_parse_of_production str0 valid str (pat::pats)
  with minimal_parse_of_item
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      item string -> Type :=
  | MinParseTerminal : forall str0 valid str ch,
                         str ~= [ ch ]
                         -> @minimal_parse_of_item str0 valid str (Terminal ch)
  | MinParseNonTerminal
    : forall str0 valid str (nt : String.string),
        @minimal_parse_of_nonterminal str0 valid str nt
        -> @minimal_parse_of_item str0 valid str (NonTerminal nt)
  with minimal_parse_of_nonterminal
  : forall (str0 : String) (valid : nonterminals_listT)
           (str : String),
      String.string -> Type :=
  | MinParseNonTerminalStrLt
    : forall str0 valid (nt : String.string) str,
        length str < length str0
        -> is_valid_nonterminal initial_nonterminals_data nt
        -> @minimal_parse_of str initial_nonterminals_data str (Lookup G nt)
        -> @minimal_parse_of_nonterminal str0 valid str nt
  | MinParseNonTerminalStrEq
    : forall str valid nonterminal,
        is_valid_nonterminal initial_nonterminals_data nonterminal
        -> is_valid_nonterminal valid nonterminal
        -> @minimal_parse_of str (remove_nonterminal valid nonterminal) str (Lookup G nonterminal)
        -> @minimal_parse_of_nonterminal str valid str nonterminal.

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
End cfg.
