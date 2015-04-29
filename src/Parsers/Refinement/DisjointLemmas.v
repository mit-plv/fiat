(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammar.
Require Import Fiat.Parsers.ContextFreeGrammarEquality.
Require Import Coq.Program.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Wf.
Require Import Fiat.Parsers.Splitters.RDPList.
Require Import Fiat.Parsers.Splitters.BruteForce.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Parsers.BaseTypes.
Require Import Fiat.Parsers.CorrectnessBaseTypes.
Require Import Fiat.Parsers.BooleanRecognizerFull.
Require Import Fiat.Parsers.BooleanRecognizerCorrect.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.StringLike.Core.
Require Import Fiat.Parsers.StringLike.String.
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.FoldGrammar.

Set Implicit Arguments.

Section all_possible.
  Context {Char : Type}.
  Definition possible_terminals := list Char.

  Local Instance all_possible_fold_data : fold_grammar_data Char possible_terminals
    := { on_terminal ch := [ch];
         on_redundant_nonterminal := nil;
         on_nil_production := nil;
         combine_production := @app _;
         on_nil_productions := nil;
         combine_productions := @app _ }.

  Definition possible_terminals_of : grammar Char -> String.string -> possible_terminals
    := fold_nt.
  Definition possible_terminals_of_productions : grammar Char -> productions Char -> possible_terminals
    := fold_productions.
  Definition possible_terminals_of_production : grammar Char -> production Char -> possible_terminals
    := fold_production.
End all_possible.

Section only_first.
  Record possible_first_terminals :=
    { actual_possible_first_terminals :> list Ascii.ascii;
      might_be_empty : bool }.

  Local Instance only_first_fold_data : fold_grammar_data Ascii.ascii possible_first_terminals
    := { on_terminal ch := {| actual_possible_first_terminals := [ch] ; might_be_empty := false |};
         on_redundant_nonterminal := {| actual_possible_first_terminals := nil ; might_be_empty := false |};
         on_nil_production := {| actual_possible_first_terminals := nil ; might_be_empty := true |};
         on_nil_productions := {| actual_possible_first_terminals := nil ; might_be_empty := false |};
         combine_production first_of_first first_of_rest
         := {| actual_possible_first_terminals
               := (actual_possible_first_terminals first_of_first)
                    ++ (if might_be_empty first_of_first
                        then actual_possible_first_terminals first_of_rest
                        else []);
               might_be_empty
               := (might_be_empty first_of_first && might_be_empty first_of_rest)%bool |};
         combine_productions first_of_first first_of_rest
         := {| actual_possible_first_terminals
               := (actual_possible_first_terminals first_of_first)
                    ++ (actual_possible_first_terminals first_of_rest);
               might_be_empty
               := (might_be_empty first_of_first || might_be_empty first_of_rest)%bool |} }.

  Definition possible_first_terminals_of : grammar Ascii.ascii -> String.string -> possible_first_terminals
    := fold_nt.
  Definition possible_first_terminals_of_productions : grammar Ascii.ascii -> productions Ascii.ascii -> possible_first_terminals
    := fold_productions.
  Definition possible_first_terminals_of_production : grammar Ascii.ascii -> production Ascii.ascii -> possible_first_terminals
    := fold_production.
End only_first.

Section reachable.
  Context {Char} {HSL : StringLike Char} {predata : parser_computational_predataT} (G : grammar Char).

  Context (ch : Char).

  (** Relation defining if a character is reachable *)
  Inductive reachable_from_productions : productions Char -> Prop :=
  | ReachableHead : forall pat pats, reachable_from_production pat
                                     -> reachable_from_productions (pat::pats)
  | ReachableTail : forall pat pats, reachable_from_productions pats
                                     -> reachable_from_productions (pat::pats)
  with reachable_from_production : production Char -> Type :=
  | ReachableProductionHead : forall it its, reachable_from_item it
                                             -> reachable_from_production (it::its)
  | ReachableProductionTail : forall it its, reachable_from_production its
                                             -> reachable_from_production (it::its)
  with reachable_from_item : item Char -> Prop :=
  | ReachableTerminal : reachable_from_item (Terminal ch)
  | ReachableNonTerminal : forall nt, is_valid_nonterminal initial_nonterminals_data nt
                                      -> reachable_from_productions (Lookup G nt)
                                      -> reachable_from_item (NonTerminal nt).

  (** Relation defining if a character is reachable *)
  Inductive min_reachable_from_productions : nonterminals_listT -> productions Char -> Prop :=
  | MinReachableHead : forall valid pat pats, min_reachable_from_production valid pat
                                              -> min_reachable_from_productions valid (pat::pats)
  | MinReachableTail : forall valid pat pats, min_reachable_from_productions valid pats
                                              -> min_reachable_from_productions valid (pat::pats)
  with min_reachable_from_production : nonterminals_listT -> production Char -> Type :=
  | MinReachableProductionHead : forall valid it its, min_reachable_from_item valid it
                                                      -> min_reachable_from_production valid (it::its)
  | MinReachableProductionTail : forall valid it its, min_reachable_from_production valid its
                                                      -> min_reachable_from_production valid (it::its)
  with min_reachable_from_item : nonterminals_listT -> item Char -> Prop :=
  | MinReachableTerminal : forall valid, min_reachable_from_item valid (Terminal ch)
  | MinReachableNonTerminal : forall valid nt, is_valid_nonterminal valid nt
                                               -> min_reachable_from_productions (remove_nonterminal valid nt) (Lookup G nt)
                                               -> min_reachable_from_item valid (NonTerminal nt).

  Lemma min_reachable_from_productions
 : productions Char -> Prop :=
  | ReachableHead : forall pat pats, reachable_from_production pat
                                     -> reachable_from_productions (pat::pats)
  | ReachableTail : forall pat pats, reachable_from_productions pats
                                     -> reachable_from_productions (pat::pats)
  with reachable_from_production : production Char -> Type :=
  | ReachableProductionHead : forall it its, reachable_from_item it
                                             -> reachable_from_production (it::its)
  | ReachableProductionTail : forall it its, reachable_from_production its
                                             -> reachable_from_production (it::its)
  with reachable_from_item : item Char -> Prop :=
  | ReachableTerminal : reachable_from_item (Terminal ch)
  | ReachableNonTerminal : forall nt, is_valid_nonterminal initial_nonterminals_data nt
                                      -> reachable_from_productions (Lookup G nt)
                                      -> reachable_from_item (NonTerminal nt).

  (** Relation defining if a character is reachable *)
  Inductive min_reachable_from_productions : nonterminals_listT -> productions Char -> Prop :=
  | MinReachableHead : forall valid pat pats, min_reachable_from_production valid pat
                                              -> min_reachable_from_productions valid (pat::pats)
  | MinReachableTail : forall valid pat pats, min_reachable_from_productions valid pats
                                              -> min_reachable_from_productions valid (pat::pats)
  with min_reachable_from_production : nonterminals_listT -> production Char -> Type :=
  | MinReachableProductionHead : forall valid it its, min_reachable_from_item valid it
                                                      -> min_reachable_from_production valid (it::its)
  | MinReachableProductionTail : forall valid it its, min_reachable_from_production valid its
                                                      -> min_reachable_from_production valid (it::its)
  with min_reachable_from_item : nonterminals_listT -> item Char -> Prop :=
  | MinReachableTerminal : forall valid, min_reachable_from_item valid (Terminal ch)
  | MinReachableNonTerminal : forall valid nt, is_valid_nonterminal valid nt
                                               -> min_reachable_from_productions (remove_nonterminal valid nt) (Lookup G nt)
                                               -> min_reachable_from_item valid (NonTerminal nt).

End reachable.
Section all_possible_correctness.
  Context {Char : Type} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}.
  Local Open Scope string_like_scope.

  Local Existing Instance all_possible_fold_data.

  Local Ltac dependent_destruction_head h :=
    idtac;
    match goal with
      | [ H : ?T |- _ ] => let x := head T in
                           constr_eq h x;
                             let H' := fresh in
                             rename H into H';
                               dependent destruction H'
    end.

  Local Instance all_possible_cdata : @fold_grammar_correctness_data Char _ all_possible_fold_data G
    := { Pnt valid0 nt ls
         := forall (str : String) (p : parse_of_item G str (NonTerminal nt)),
              Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p
              -> forall_chars__char_in str ls;
         Ppat valid0 pat ls
         := forall (str : String) (p : parse_of_production G str pat),
              Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p
              -> forall_chars__char_in str ls;
         Ppats valid0 pats ls
         := forall (str : String) (p : parse_of G str pats),
              Forall_parse_of (fun _ nt' => is_valid_nonterminal valid0 nt') p
              -> forall_chars__char_in str ls }.
  Proof.
    { simpl; intros valid0 nt value Hvalid Hnt str p Hp.
      dependent destruction p.
      simpl in Hp.
      destruct Hp as [Hp0 Hp1].
      specialize (Hnt _ p).
      apply Hnt.
      clear -Hp0 Hp1.
      admit. }
    { abstract (
          simpl; (intros ???? p H);
          dependent destruction p;
          simpl in H; destruct H; congruence
        ). }
    { abstract (
          simpl; (intros ?? p H);
          apply forall_chars__char_in_nil;
          dependent destruction p; trivial
        ). }
    { simpl combine_production.
      intros valid0 nt xs ls1 ls2 Hit Hits str p Hp.
      dependent destruction p.
      match type of Hp with
        | context[ParseProductionCons _ _ ?p ?p1]
          => change (Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p
                     * Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p1)%type in Hp
      end.
      simpl in Hp; destruct Hp as [Hp0 Hp1].
      apply (forall_chars__char_in__split n); split;
      apply forall_chars__char_in__or_app; [ left | right ]; eauto. }
    { simpl combine_production; simpl on_terminal; cbv beta.
      intros valid0 nt xs ls Hits str p Hp.
      dependent destruction p.
      match type of Hp with
        | context[ParseProductionCons _ _ ?p ?p1]
          => change (Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p
                     * Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p1)%type in Hp
      end.
      simpl in Hp.
      destruct Hp as [Hp0 Hp1].
      apply (forall_chars__char_in__split n); split;
      apply forall_chars__char_in__or_app; [ left | right ]; eauto; [].
      dependent_destruction_head (@parse_of_item).
      erewrite forall_chars__char_in_singleton_str by eassumption.
      left; reflexivity. }
    { abstract (
          simpl; (intros ?? p);
          dependent destruction p
        ). }
    { abstract (
          simpl; intros ????? IH1 IH2 ? p H';
          apply forall_chars__char_in__or_app;
          dependent destruction p; [ left | right ]; eauto
        ). }
  Defined.

  Lemma possible_terminals_of_production'_correct (G : grammar Char)
        (predata := @rdp_list_predata _ G)
        pat ptont
        (valid0 : nonterminals_listT)
        (IH : forall nt, Pnt valid0 nt (ptont nt))
  : Ppat valid0 pat (fold_production' ptont pat).
  Proof.
    unfold fold_production'; simpl in *.
    induction pat as [ | x xs IHxs ]; intros str p Hp.
    { dependent destruction p; simpl in *.
      apply forall_chars__char_in_nil; assumption. }
    { dependent destruction p; simpl in *.
      match type of Hp with
        | context[ParseProductionCons _ _ ?p ?p1]
          => change (Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p
                     * Forall_parse_of_production (fun _ nt' => is_valid_nonterminal valid0 nt') p1)%type in Hp
      end.
      simpl in Hp.
      destruct (Compare_dec.lt_dec (length str) n).
      { apply forall_chars__char_in__or_app; left.
        dependent_destruction_head (@parse_of_item).
        { clear Hp.
          repeat match goal with
                   | [ H : _ |- _ ] => rewrite take_long in H by omega
                 end.
          erewrite forall_chars__char_in_singleton_str; intuition. }
        { apply (forall_chars__char_in__split n); split.
          { eapply IH.
            exact (fst Hp). }
          { apply forall_chars__char_in_empty.
            rewrite drop_length; omega. } } }
      { apply (forall_chars__char_in__split n); split;
        apply forall_chars__char_in__or_app; [ left | right ].
        { dependent_destruction_head (@parse_of_item).
          { eapply forall_chars__char_in_singleton_str; try eassumption; left; reflexivity. }
          { eapply IH.
            exact (fst Hp). } }
        { eapply IHxs.
          exact (snd Hp). } } }
  Qed.

  Lemma possible_terminals_of_productions'_correct (G : grammar Char)
        (predata := @rdp_list_predata _ G)
        pats ptont
        (valid0 : nonterminals_listT)
        (IH : forall nt, Pnt valid0 nt (ptont nt))
  : Ppats valid0 pats (fold_productions' ptont pats).
  Proof.
    apply fold_productions'_correct; trivial; [].
    intro; apply possible_terminals_of_production'_correct; assumption.
  Qed.

  Lemma Fix_possible_terminals_of_nt_step_correct (G : grammar Char)
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (valid0 : nonterminals_listT)
        (p : parse_of_item G str (NonTerminal nt))
        (Hp : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal valid0 nt') p)
  : forall_chars__char_in
      str
      (Fix ntl_wf (fun _ : nonterminals_listT => string -> possible_terminals)
           (possible_terminals_of_nt_step (G:=G)) valid0 nt).
  Proof.
    generalize dependent str; generalize dependent nt.
    induction (ntl_wf valid0) as [ ? ? IH ]; intros.
    rewrite Fix1_eq; [ | apply possible_terminals_of_nt_step_ext ]; [].
    unfold possible_terminals_of_nt_step at 1; cbv beta zeta.
    dependent destruction p; destruct Hp as [Hpi Hpp]; [].
    edestruct dec; [ | simpl in *; congruence ].
    let H := match goal with H : is_valid_nonterminal ?x ?nt = true |- _ => constr:H end in
    specialize (IH _ (remove_nonterminal_dec _ _ H)).
    generalize dependent (G nt); intros ? p.
    destruct p;
      (eapply possible_terminals_of_productions'_correct).
    intros.
    specialize (IH nt0 str0).
    specialize (IH p0).
    apply IH.
    admit.
    admit.
  Qed.

  Lemma possible_terminals_of_correct (G : grammar Char)
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (p : parse_of_item G str (NonTerminal nt))
        (Hp : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal initial_nonterminals_data nt') p)
  : forall_chars__char_in str (possible_terminals_of G nt).
  Proof.
    unfold possible_terminals_of, possible_terminals_of_nt.
    eapply Fix_possible_terminals_of_nt_step_correct; eassumption.
  Qed.
End all_possible_correctness.

Section only_first_correctness.
  Local Open Scope string_like_scope.

  Lemma production_is_reachable_iff {Char} {G : grammar Char} {its}
        (predata := @rdp_list_predata _ G)
  : production_is_reachable G its
    <-> (exists (nt : string) (prefix : production Char),
           is_valid_nonterminal initial_nonterminals_data nt /\ In (prefix ++ its) (G nt)).
  Proof.
    split; intro; destruct_head_hnf ex; destruct_head and; do 2 eexists; split; try eassumption.
    { apply list_in_lb; [ apply (@string_lb) | assumption ]. }
    { eapply list_in_bl; [ apply (@string_bl) | assumption ]. }
  Qed.

  Lemma might_be_empty_possible_first_terminals_of_production_from_parse {G : grammar Ascii.ascii}
        {its}
        (predata := @rdp_list_predata _ G)
        (H_reachable : production_is_reachable G its)
        (pits : parse_of_production G ""%string its)
        (Hpits : Forall_parse_of_production (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt) pits)
  : might_be_empty (possible_first_terminals_of_production G its).
  Proof.
    apply production_is_reachable_iff in H_reachable.
    eapply parse_production_complete; eassumption.
  Qed.

  Lemma might_be_empty_possible_first_terminals_of_production_to_parse {G : grammar Ascii.ascii}
        {its}
        (H_reachable : production_is_reachable G its)
        (H : might_be_empty (possible_first_terminals_of_production G its))
  : parse_of_production G ""%string its.
  Proof.
    eapply parse_production_sound.
    exact H.
  Defined.

  Lemma forall_is_valid_production {Char} {G : grammar Char}
        {nt}
        (predata := @rdp_list_predata _ G)
        (H : is_valid_nonterminal initial_nonterminals_data nt)
  : List.Forall (production_is_reachable G) (G nt).
  Proof.
    simpl in H.
    apply (list_in_bl (@string_bl)) in H.
    unfold production_is_reachable.
    apply Forall_forall.
    intros p H'.
    exists nt.
    induction (G nt); simpl in *; destruct_head False; [].
    destruct_head or; subst.
    { eexists nil; simpl; intuition. }
    { intuition; destruct_head ex; destruct_head and.
      eexists; split; [ | right ]; eassumption. }
  Qed.

  Global Arguments forall_is_valid_production {_ _ _} _. (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4191 *)

  Lemma might_be_empty_Fix_possible_first_terminals_of_nt_step_from_parse {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        {nt}
        (valid0 : nonterminals_listT)
        (p : parse_of_item G ""%string (NonTerminal nt))
        (Hpits : Forall_parse_of_item (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt) p)
  : might_be_empty
      (Fix ntl_wf
           _
           (possible_first_terminals_of_nt_step (G:=G))
           valid0 nt).
  Proof.
    rewrite Fix1_eq; [ | apply possible_first_terminals_of_nt_step_ext ]; [].
    unfold possible_first_terminals_of_nt_step at 1; simpl.
    dependent destruction p.
    edestruct dec; simpl;
    [
    | apply (parse_nonterminal_complete (p := p)); assumption ].
    rewrite map_map; simpl.
    simpl in Hpits.
    destruct Hpits as [Hvalid ?].
    pose proof (forall_is_valid_production Hvalid) as H_reachable.
    induction (G nt); simpl in *.
    { dependent destruction p. }
    { apply Bool.orb_true_iff.
      dependent destruction H_reachable.
      dependent destruction p; [ left | right ].
      { match goal with
          | [ H : production_is_reachable _ _ |- _ ] => apply production_is_reachable_iff in H
        end.
        eapply parse_production_complete; eassumption. }
      { eapply IHp0; eassumption. } }
  Qed.

  Lemma might_be_empty_Fix_possible_first_terminals_of_nt_step_to_parse {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        {nt}
        (valid0 : nonterminals_listT)
        (Hvalid : is_valid_nonterminal valid0 nt)
        (H : might_be_empty
               (Fix ntl_wf
                    _
                    (possible_first_terminals_of_nt_step (G:=G))
                    valid0 nt))
  : parse_of_item G ""%string (NonTerminal nt).
  Proof.
    rewrite Fix1_eq in H; [ | apply possible_first_terminals_of_nt_step_ext ]; [].
    unfold possible_first_terminals_of_nt_step at 1 in H; simpl in *.
    rewrite Hvalid in H; simpl in *.
    constructor.
    induction (G nt); simpl in *; [ congruence | ].
    apply Bool.orb_true_iff in H.
    match goal with
      | [ H : ?b = true \/ ?A |- _ ]
        => let H' := fresh in
           let H'' := fresh in
           revert H; case_eq b;
           [ intros H _
           | intros H'' H'; assert (H : A) by (destruct H'; (congruence || assumption)); clear H' ]
    end;
      [ left | right ].
    { eapply parse_production_sound; try eassumption; exact H. }
    { apply IHp; trivial. }
  Qed.

  Lemma might_be_empty_possible_first_terminals_of_from_parse {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        {nt}
        (p : parse_of_item G ""%string (NonTerminal nt))
        (Hpits : Forall_parse_of_item (fun _ nt => is_valid_nonterminal initial_nonterminals_data nt) p)
  : might_be_empty (possible_first_terminals_of G nt).
  Proof.
    simpl.
    unfold possible_first_terminals_of.
    eapply might_be_empty_Fix_possible_first_terminals_of_nt_step_from_parse; eassumption.
  Qed.

  Lemma might_be_empty_possible_first_terminals_of_to_parse {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        {nt}
        (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
        (H : might_be_empty (possible_first_terminals_of G nt))
  : parse_of_item G ""%string (NonTerminal nt).
  Proof.
    unfold possible_first_terminals_of, possible_first_terminals_of_nt in *.
    eapply might_be_empty_Fix_possible_first_terminals_of_nt_step_to_parse; eassumption.
  Qed.

  Local Ltac t_str :=
    repeat match goal with
             | _ => progress simpl in *
             | _ => congruence
             | _ => progress subst
             | [ |- _ \/ False ] => left
             | _ => reflexivity
             | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
             | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
             | [ H : substring _ _ ?str = String.String _ _ |- _ ] => atomic str; destruct str
             | [ H : _ |- _ ] => rewrite substring_correct3' in H
             | [ |- _ ] => progress rewrite ?substring_correct0, ?(ascii_lb eq_refl)
             | [ H : _ <= 0 |- _ ] => apply Le.le_n_0_eq in H
             | [ H : match ?n with _ => _ end = String.String _ _ |- _ ] => atomic n; destruct n
           end.

  Local Ltac dependent_destruction_head h :=
    idtac;
    match goal with
      | [ H : ?T |- _ ] => let x := head T in
                           constr_eq h x;
                             let H' := fresh in
                             rename H into H';
                               dependent destruction H'
    end.

  Lemma Fix_possible_first_terminals_of_production'_In
        {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        {ch pat}
        (pftont : String.string -> possible_first_terminals)
        (valid' : nonterminals_listT)
        (*IH : forall str,
                minimal_parse_of_nonterminal (G := G) (length str) valid' str nt ->
                take 1 str ~= [ch] ->
                In ch (pftont nt)*)
        (IHe : forall nt (p : parse_of_item G ""%string (NonTerminal nt)),
                 Forall_parse_of_item (fun _ => is_valid_nonterminal initial_nonterminals_data) p
                 -> might_be_empty (pftont nt))
        (str : @String _ string_stringlike)
        (p : minimal_parse_of_production (G := G) (length str) valid' str pat)
        (H : take 1 str ~= [ch])
  : In ch (possible_first_terminals_of_production' G pftont pat).
  Proof.
    unfold possible_first_terminals_of_production'; simpl in *.
    set (len0 := String.length str) in *.
    assert (String.length str <= len0) by reflexivity.
    clearbody len0.
    generalize dependent str; generalize dependent len0; generalize dependent ch;
    induction pat as [ | x xs IHxs ]; simpl in *; intros.
    { dependent destruction p; t_str. }
    { dependent destruction p.
      dependent_destruction_head (@minimal_parse_of_item).
      { t_str. }
      { simpl in *.
        apply in_or_app.
        destruct n; [ right | ].
        (*generalize dependent str; generalize dependent len0;
        let n := match goal with n : nat |- _ => constr:n end in
        induction n as [ | n IHn ]; intros; [ right | ].*)
        { repeat match goal with
                   | [ H : _ |- _ ] => progress rewrite ?substring_correct3', ?substring_correct0, ?substring_correct3 in H by omega
                   | [ H : minimal_parse_of_nonterminal _ _ _ _ |- _ ]
                     => specialize (IHe _ _ (projT2 (parse_of_item_nonterminal__of__minimal_parse_of_nonterminal H)))
                   | _ => rewrite IHe; []
                   | [ H : _ <= 0 |- _ ] => apply Le.le_n_0_eq in H
                   | [ H : _ |- _ ] => eapply H; eassumption
                   | _ => congruence
                   | [ H : 0 = String.length ?str |- _ ] => atomic str; destruct str; simpl in H
                 end. }
        { t_str.
          right.

          eapply IHn.
          rewrite (ascii_lb eq_refl).
          match goal with
            | [ p : minimal_parse_of_production _ _ _ _ |- _ ]
              => specialize (IHxs (String.String _ _) p)
          end.
          simpl in *.
          specialize
          apply in_or_app.

          (IHe : forall
        (Hvalid : is_valid_nonterminal initial_nonterminals_data nt)
        (H : might_be_empty (possible_first_terminals_of G nt))
  : parse_of_item G ""%string (NonTerminal nt).


          SearchAbout might_be_empty.


  Lemma Fix_possible_first_terminals_of_productions'_In
        {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        {nt ch prods}
        (pftont : String.string -> possible_first_terminals)
        (valid' : nonterminals_listT)
        (IH : forall str,
                minimal_parse_of_nonterminal (G := G) (length str) valid' str nt ->
                take 1 str ~= [ch] ->
                In ch (pftont nt))
        (str : @String _ string_stringlike)
        (p : minimal_parse_of (G := G) (length str) valid' str prods)
        (H : take 1 str ~= [ch])
  : In ch (possible_first_terminals_of_productions' G pftont prods).
  Proof.
    unfold possible_first_terminals_of_productions'; simpl.
    Opaque possible_first_terminals_of_production'.
    generalize dependent str; induction prods as [ | x xs IHxs ]; simpl in *; intros.
    { dependent destruction p. }
    { apply in_or_app.
      dependent destruction p; simpl in *; [ left | right ].
      { generalize dependent str; induction x; simpl in *; intros.
        { dependent_destruction_head (@minimal_parse_of_production).
          t_str. }
        { dependent_destruction_head (@minimal_parse_of_production).
          dependent_destruction_head (@minimal_parse_of_item).
          { t_str. }
          { apply in_or_app.
let p := match goal with H : minimal_parse_of_production _ _ _ _ |- _ => constr:H end in
        let H := fresh in
        rename p into H;
          dependent destruction H.


  H0 : forall str : String,
       minimal_parse_of_nonterminal (length str) (remove_nonterminal x nt)
         str nt ->
       take 1 str ~= [ch] ->
       In ch
         (Fix ntl_wf
            (fun _ : nonterminals_listT => string -> possible_first_terminals)
            (possible_first_terminals_of_nt_step (G:=G))
            (remove_nonterminal x nt) nt)
  str : String
  p : minimal_parse_of_nonterminal (length str) x str nt
  H1 : take 1 str ~= [ch]
  e : rdp_list_is_valid_nonterminal x nt = true
  ============================
   In ch
     (possible_first_terminals_of_productions' G
        (Fix ntl_wf
           (fun _ : rdp_list_nonterminals_listT =>
            string -> possible_first_terminals)
           (possible_first_terminals_of_nt_step (G:=G))
           (rdp_list_remove_nonterminal x nt)) (G nt))
*)

  Lemma Fix_possible_first_terminals_of_nt_step_In {G : grammar Ascii.ascii}
        (predata := @rdp_list_predata _ G)
        (str : @String _ string_stringlike) {nt}
        (valid0 : nonterminals_listT)
        (p : minimal_parse_of_nonterminal (G := G) (length str) valid0 str nt)
        (ch : Ascii.ascii)
        (H : take 1 str ~= [ch])
  : In ch (Fix ntl_wf
        (fun _ : nonterminals_listT => string -> possible_first_terminals)
        (possible_first_terminals_of_nt_step (G:=G))
        valid0 nt).
  Proof.
    generalize dependent str; induction (ntl_wf valid0); intros.
    rewrite Fix1_eq; [ | apply possible_first_terminals_of_nt_step_ext ].
    unfold possible_first_terminals_of_nt_step at 1; simpl.
    edestruct dec; [ | dependent destruction p; simpl in *; try omega; congruence ].
    specialize (H0 (remove_nonterminal x nt)).
    specialize (H0 (remove_nonterminal_dec x _ e)).
    unfold possible_first_terminals_of_productions'; simpl.
    Require Import Fiat.Common.List.FlattenList.
    rewrite flat_map_flatten, map_map, <- flat_map_flatten.
    unfold possible_first_terminals_of_production'; simpl.
    dependent destruction p; try omega; [].
    match goal with
      | [ |- context[Lookup G ?nt] ] => induction (G nt) as [ | gnt gnts IHgnts ]
    end;
      simpl in *;
      (let p := match goal with H : minimal_parse_of _ _ _ _ |- _ => constr:H end in
       let H := fresh in
       rename p into H;
       dependent destruction H);
      apply in_or_app; [ left | right; apply IHgnts ]; clear IHgnts; trivial;
      [].
    induction gnt as [ | k ks IHks ]; simpl in *;
    (let p := match goal with H : minimal_parse_of_production _ _ _ _ |- _ => constr:H end in
     let H := fresh in
     rename p into H;
     dependent destruction H).
    {  }
    { (let p := match goal with H : minimal_parse_of_item _ _ _ _ |- _ => constr:H end in
       let H := fresh in
       rename p into H;
       dependent destruction H).
      { repeat match goal with
                 | _ => progress simpl in *
                 | _ => congruence
                 | _ => progress subst
                 | [ |- _ \/ False ] => left
                 | _ => reflexivity
                 | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                 | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
                 | [ H : substring _ _ ?str = String.String _ _ |- _ ] => atomic str; destruct str
                 | [ H : match ?n with _ => _ end = String.String _ _ |- _ ] => atomic n; destruct n
               end. }
      { apply in_or_app.

    {              | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H


    Focus 2.
    assumption.
    2:apply I
Focus

   In ch




  Lemma possible_first_terminals_of_nt_In {G : grammar Ascii.ascii}
        (str : @String _ string_stringlike) {nt}
        (p : parse_of_item G str (NonTerminal nt))
        (Hp : Forall_parse_of_item
                (fun (_ : String) (nt : string) => In nt (Valid_nonterminals G))
                p)
        (ch : Ascii.ascii)
        (H : take 1 str ~= [ch])
  : In ch (possible_first_terminals_of_nt (G := G) initial_nonterminals_data nt).
  Proof.
    unfold possible_first_terminals_of_nt.
    repeat match goal with
             | _ => progress simpl in *
             | _ => congruence
             | _ => progress subst
             | [ |- _ \/ False ] => left
             | _ => reflexivity
             | [ H : appcontext[Forall_parse_of_production] |- _ ] => clear H
             | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
             | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
             | [ H : substring _ _ ?str = String.String _ _ |- _ ] => atomic str; destruct str
             | [ H : match ?n with _ => _ end = String.String _ _ |- _ ] => atomic n; destruct n
           end.


  Lemma possible_first_terminals_of_production_In {G : grammar Ascii.ascii}
        (str : @String _ string_stringlike) {its}
        (pits : parse_of_production G str its)
        (Hpits : Forall_parse_of_production
                   (fun (_ : String) (nt : string) => In nt (Valid_nonterminals G))
                   pits)
        (ch : Ascii.ascii)
        (H : take 1 str ~= [ch])
  : In ch (possible_first_terminals_of_production G its).
  Proof.
    simpl in H; apply string_bl in H.
    induction pits; simpl in *.
    { destruct str; simpl in *; congruence. }
    { dependent destruction p; simpl in *.
      { repeat match goal with
                 | _ => progress simpl in *
                 | _ => congruence
                 | _ => progress subst
                 | [ |- _ \/ False ] => left
                 | _ => reflexivity
                 | [ H : appcontext[Forall_parse_of_production] |- _ ] => clear H
                 | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                 | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
                 | [ H : substring _ _ ?str = String.String _ _ |- _ ] => atomic str; destruct str
                 | [ H : match ?n with _ => _ end = String.String _ _ |- _ ] => atomic n; destruct n
               end. }
      { apply in_or_app.
        lazymatch goal with
| [ H : substring _ _ ?str = String.String _ _ |- _ ] => atomic str; destruct str
end.
        try match goal with
          | [ H : ?T |- _ ] => idtac H ":" T; fail
        end.
        apply string_bl in i.
    unfold possible_first_terminals_of_production.
    unfold possible_first_terminals_of_production'; simpl.
    simpl in H.
    apply string_bl in H.
    destruct str; simpl in *; try discriminate.
  inversion H; subst; clear H.
  induction its; simpl; intros.
  { dependent destruction pits. }
  { edestruct (_ : item _); simpl in *;
    dependent destruction pits;
    [ clear Hpits
    | ];
    repeat match goal with
             | _ => reflexivity
             | [ p : parse_of_item _ _ (Terminal _) |- _ ]
               => (let H := fresh in
                   rename p into H;
                   dependent destruction H)
             | _ => progress simpl in *
             | [ H : _ |- _ ] => apply string_bl in H
             | [ H : context[match ?x with _ => _ end] |- _ ] => destruct n eqn:?
             | _ => discriminate
             | _ => progress subst
             | [ H : String.String _ _ = String.String _ _ |- _ ] => inversion H; clear H
             | [ |- _ \/ False ] => left
           end.
    simpl.


    unfold possible_first_terminals_of; simpl.
    unfold possible_first_terminals_of_nt.
    rewrite might_be_empty_possible_first_terminals_of_production_from_parse.


 }
move i at bottom.
apply string_bl in i.
lazymatch goal with
               | [ H : string_beq _ _ |- _ ] => apply string_bl in H
               | [ H : @string_beq _ _ |- _ ] => idtac
end.

      simpl in *.
      match goal with
        | [ H :
    destruct str; simpl in *; discriminate. }
  {

*)


  Definition forall_chars (str : String) (P : Char -> Prop)
    := forall n ch,
         take 1 (drop n str) ~= [ ch ]
         -> P ch.

  Definition forall_chars__char_in (str : String) (ls : list Char)
    := forall_chars str (fun ch => List.In ch ls).

  Lemma Fix_possible_terminals_of_nt_step_correct (G : grammar Char)
        (predata := @rdp_list_predata _ G)
        (str : String) (len0 : nat) nt
        (valid0 : nonterminals_listT)
        (p : minimal_parse_of_nonterminal (G := G) len0 valid0 str nt)
  : forall_chars__char_in
      str
      (Fix ntl_wf (fun _ : nonterminals_listT => string -> possible_terminals)
           (possible_terminals_of_nt_step (G:=G)) valid0 nt).
  Proof.
    induction (ntl_wf valid0).
    rewrite Fix1_eq; [ | apply possible_terminals_of_nt_step_ext ]; [].
    unfold possible_terminals_of_nt_step.
    edestruct dec.
    Focus 2.
    dependent destruction p; try congruence.
    cong

    dependent destruction p.
    generalize dependent (G nt); intros prods p.
    Focus 2.
    congruence.
    hnf.


  ============================
   forall_chars__char_in str
     (Fix ntl_wf (fun _ : nonterminals_listT => string -> possible_terminals)
        (possible_terminals_of_nt_step (G:=G)) initial_nonterminals_data nt)

  Lemma possible_terminals_of_correct (G : grammar Char)
        (str : String) nt (p : parse_of_item G str (NonTerminal nt))
  : forall_chars__char_in str (possible_terminals_of G nt).
  Proof.
    unfold possible_terminals_of, possible_terminals_of_nt.
    match goal with
      | [ |- appcontext[Fix ?wf _ _ ?a] ]
        => generalize a;
          let H := fresh in
          intro H;
            induction (wf H)
    end.
    rewrite Fix1_eq


list_bin ascii_beq ch (possible_terminals_of G nt)

  Definition possible_terminals_of (G : grammar Char) : String.string -> possible_terminals
    := @possible_terminals_of_nt G initial_nonterminals_data.



  Definition possible_terminals_of_production' (terminals_of_nt : String.string -> possible_terminals)
             (its : production Char)
  : possible_terminals
    := flat_map
         (fun it =>
            match it with
              | Terminal ch => [ch]
              | NonTerminal nt => terminals_of_nt nt
            end)
         its.



Local Open Scope string_like_scope.

Local Arguments string_beq : simpl never.

Lemma terminals_disjoint_search_for_not {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: (forall n' ch, n' < n
                        -> (take 1 (drop n' str)) ~= [ ch ]
                        -> list_bin ascii_beq ch (possible_terminals_of G nt))
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (forall ch, (take 1 (drop n str)) ~= [ ch ]
                     -> (negb (list_bin ascii_beq ch (possible_terminals_of G nt))))).
Proof.
  destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
  apply and_comm; split.
  { destruct (Compare_dec.le_dec (length str) n); [ left | right ].
    { split; trivial.
      pose proof (drop_length str n) as H.
      rewrite (proj2 (Nat.sub_0_le (length str) n)) in H by assumption.
      generalize dependent (drop n str); clear -Hpit HinV HinL.
      intros.
      destruct s; try (simpl in *; discriminate); [].
      clear H.
      eapply parse_production_complete.
      { eexists; eexists (prefix ++ [NonTerminal _]); split; simpl.
        { unfold rdp_list_is_valid_nonterminal.
          apply list_in_lb; try apply @string_lb; []; eassumption. }
        { rewrite <- app_assoc; simpl; eassumption. } }
      { eapply expand_forall_parse_of_production;
        [
        | rewrite parse_of_production_respectful_refl; eassumption ].
        intros; simpl in *.
        apply list_in_lb; try apply @string_lb; []; eassumption. } }
    { intros.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H'.
      apply list_in_bl in H'; [ | apply (@ascii_bl) ].
      apply (disjoint_bl (@ascii_lb) _ _ H_disjoint _ H').
      clear -pits Hpits H.
      unfold possible_first_terminals_of_production.
      SearchAbout disjoint.
      SearchAbout (_ = false) (_ <> true).
SearchAbout Forall_parse_of_production.
      unfold possible_first_terminals_of_production, possible_first_terminals_of_production', brute_force_parse_production; simpl.
      intros.
      unfold brute_force_parse_nonterminal.
      unfold BooleanRecognizer.parse_nonterminal.
      eapply parse_production_complete.
        [ ..
        | refine ((fun pf =>
                     projT1 (@alt_all_elim
                               _ _ G (@rdp_list_predata _ G) _ _ _
                               (@minimal_parse_of_production__of__parse_of_production
                                  _ _ _ G (@rdp_list_predata _ G) ""%string (S (WellFoundedParse.size_of_parse_production pits))
                                  (fun _ _ => @minimal_parse_of_nonterminal__of__parse_of_nonterminal _ _ _ _ _ _ _)
                                  ""%string
                                  (@reflexivity _ _ str_le_refl _)
                                  initial_nonterminals_data
                                  _ pits
                                  (Lt.lt_n_Sn _)
                                  (reflexivity _)
                                  pf))) _) ];
        eauto.
      { let p := match goal with p : parse_of_item _ _ _ |- _ => constr:p end in
        let H := fresh in
        rename p into H;
          dependent destruction H; []; simpl in *; destruct_head prod.
        unfold brute_force_parse_nonterminal.
        repeat intro.
        assert (str0 = ""%string)
          by (destruct_head_hnf or; subst; trivial; try omega;
              apply string_bl; assumption); subst.
        let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
        destruct (@parse_of_item_nonterminal__of__minimal_parse_of_nonterminal
                    _ _ G (@rdp_list_predata _ G) _ _ _ _ p)
          as [p' Hp'].
        dependent destruction p'.
        exact (@parse_nonterminal_complete
                 _ _ _ G _ (brute_force_cdata G) rdp_list_rdata'
                 _ _ _ Hp'). }
      { intros.
        refine (I : (fun _ _ _ => True) _ _ _). }
      { intros str0 valid str1 pf.
        eapply list_in_lb in HinV; [ | exact (@string_lb) ].
        pose proof (@split_string_for_production_complete
                      _ _  G _ (brute_force_cdata G)
                      str0 valid str1 pf nt' HinV) as X.
        induction (G nt'); simpl in *; destruct_head False; []; destruct_head prod.
        match goal with
          | [ H : ?a = ?b \/ ?H' |- _ ]
            => let n := fresh in
               destruct (@production_eq_dec' _ (@ascii_eq_dec) a b);
              [ clear H; subst
              | assert H' by intuition; clear H ]
        end.
        { match goal with
            | [ H : Forall_tails ?f (?ls ++ ?x::?xs)
                |- Forall_tails ?f ?xs ]
              => clear -H;
                revert H;
                change (Forall_tails f (ls ++ x::xs) -> Forall_tails f xs);
                generalize f;
                clear;
                intros ? H;
                induction ls; simpl in *; intuition
          end. }
        { intuition. } }
      { erewrite <- parse_of_production_respectful_refl.
        erewrite <- parse_of_production_respectful_refl in Hpits.
        revert Hpits.
        apply (@expand_forall_parse_of_production
                 _ _ _ G); simpl.
        intros ????? H'.
        apply list_in_lb; trivial; apply (@string_lb). } }
    { clear -pits Hpits H_disjoint.
      generalize dependent (drop n str).
      generalize dependent (possible_terminals_of G nt).
      intros terms H_disjoint str' pits Hpits ch H'.
      simpl in *.
      apply string_bl in H'.
      inversion H'; subst; clear -pits H_disjoint H' Hpits.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H.
      eapply list_in_bl in H; [ | exact (@ascii_bl) ].
      eapply disjoint_bl in H_disjoint; try eassumption; try exact (@ascii_lb); [].
      clear H_disjoint.
      generalize dependent str'.
      induction its; simpl.
      { intros ? p.
        dependent destruction p.
        destruct str'; simpl in *; congruence. }
      { intros str' pits Hpits H'.
        dependent destruction pits; simpl in *.
        edestruct (_ : item _);
          repeat match goal with
                   | [ H : Forall_parse_of_production ?f (ParseProductionCons _ _ ?p ?ps) |- _ ]
                     => change (Forall_parse_of_item f p * Forall_parse_of_production f ps)%type in H
                   | [ H : prod _ _ |- _ ] => destruct H
                   | [ H : parse_of_item _ _ (Terminal _) |- _ ]
                     => let H' := fresh in
                        rename H into H';
                          dependent destruction H'
                   | [ H : parse_of_item _ _ (NonTerminal _) |- _ ]
                     => let H' := fresh in
                        rename H into H';
                          dependent destruction H'
                   | _ => progress simpl in *
                   | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                   | [ |- _ \/ False ] => left
                 end.
        { destruct str' as [| ? str' ]; simpl in *; try congruence; [].
          repeat match goal with
                   | [ H : context[match ?e with _ => _ end] |- _ ] => atomic e; destruct e
                   | _ => progress simpl in *
                   | _ => congruence
                   | [ H : is_true (string_beq _ _) |- _ ] => apply string_bl in H
                 end. }
        { apply in_or_app.
          let n := match type of pits with parse_of_production _ (substring ?n _ _) _ => constr:n end in
          destruct n.
          { repeat match goal with H : _ |- _ => generalize dependent H; rewrite substring_correct0; intros end.
            right.
            match goal with
              | [ |- context[might_be_empty ?e] ]
                => destruct (might_be_empty e) eqn:?
            end.
            { eapply IHits; [ eassumption | ].
              rewrite substring_correct3'; trivial. }
            {
              lazymatch goal with
                | [ H : parse_of ?G ""%string (Lookup ?G ?s), H' : might_be_empty (possible_first_terminals_of ?G ?s) = false, H'' : In ?s (Valid_nonterminals ?G) |- _ ]
                  => exfalso; clear -s H H' H''; revert s H H' H''
              end.
              intros s p H H'.
              unfold possible_first_terminals_of in *.
              unfold possible_first_terminals_of_nt in *.
              rewrite Fix1_eq in H by apply possible_first_terminals_of_nt_step_ext.
              simpl in *.
              unfold possible_first_terminals_of_nt_step in *.
              simpl in *.
              edestruct dec;
                [
                | eapply list_in_lb in H'; [ | exact (@string_lb) ];
                  unfold rdp_list_is_valid_nonterminal in *; congruence ].
              simpl in *.
              clear -p H.
              induction (G s) as [ | x xs IHGs ]; simpl in *.
              { dependent destruction p. }
              { apply Bool.orb_false_iff in H.
                destruct H as [H ?].
                dependent destruction p.

              Focus 2.

              SearchAbout (substring 0).
            eauto.

            unfold possible_first_terminals_of at 1; simpl.
            unfold possible_first_terminals_of_nt; simpl.
            unfold possible_first_terminals_of_nt_step; simpl.
            destruct (Valid_nonterminals G); simpl.
          SearchAbout (substring _ 0).
          { right; eauto.
            eapply IHits.
            eassumption.

          edestruct might_be_empty.
          {
SearchAbout (In _ (_ ++ _)).
          simpl in *.


      dependent destruction pits; simpl.
      SearchAbout true false.
      dependent destruction
      rewrite substring_substring in H'; simpl in H'.

induction prefix; simpl in *; destruct_head prod; eauto.
        simpl in *.
        intros str0 valid str1 pf0.
        specialize (pf str0 valid str1 pf0).
        induction (Valid_nonterminals G); simpl in *.
        { exfalso; destruct_head ex; intuition. }
        {

).




          try eassumption; []; simpl.
        apply and_assoc; split; [ | reflexivity ].
        split.
        { let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
          destruct p; assumption. }
        { destruct X.
          destruct m.
        let p :=


        hnf; intros; simpl in *.
                     pose proof (@parse_nonterminal_complete
                                   _ _ _ G _ (brute_force_cdata G) rdp_list_rdata').
        s
 (@rdp_list_predata _ G)).
        apply parse_nonterminal_complete; try eassumption.
        { apply brute_force_cdata. }
        { apply rdp_list_rdata'. }
        { simpl.
          split.
          { let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
            destruct p; assumption. }
          {

rewrite <- (parse_of_respectful_refl (pf := reflexivity _)).
lazymatch goal with
               | [ H : Forall_parse_of _ ?x |- _ ]
                 => atomic x; rewrite <- (parse_of_respectful_refl (pf := reflexivity _)) in H
            end.

let p := match goal with p : minimal_parse_of_nonterminal _ _ _ _ |- _ => constr:p end in
            destruct p; assumption. }
 }
        as X; simpl in *.
      pose ().


SearchAbout (?x < S ?x).
      specialize (X (reflexivity _)).
                 (reflexivity );
        simpl in *.
                                                                  (@minimal_parse_of_production__of__parse_of));
      simpl in *.
      SearchAbout (_ - _ = 0).
      Check drop_length.
      SearchAbout length drop.

{ splits : list nat
                                       | forall n,
                                           n <= ilength s
                                           -> parse_of_item G (take n (string_of_indexed s)) (NonTerminal nt)
                                           -> parse_of_production G (drop n (string_of_indexed s)) p'
                                           -> List.In n splits }%comp
Definition possible_terminals_of_production' (terminals_of_nt : String.string -> possible_terminals)
           (its : production Char)
: possible_terminals
  := flat_map
       (fun it =>
          match it with
            | Terminal ch => [ch]
            | NonTerminal nt => terminals_of_nt nt
          end)
       its.




Lemma has_only_terminals_parse_of_production_length (G : grammar Ascii.ascii) {n}
      f pat
      (H_f : forall nt str n', f nt = same_length n' -> parse_of G str (Lookup G nt) -> String.length str = n')
      (H : possible_first_terminals_of_production' f pat = same_length n)
      str
      (p : parse_of_production G str pat)
: String.length str = n.
Proof.
  revert n H; induction p; simpl in *.
  { congruence. }
  { edestruct (_ : item _).
    { match goal with
        | [ H : context[possible_first_terminals_of_production' ?f ?p] |- _ ] => revert H; case_eq (possible_first_terminals_of_production' f p); intros
      end;
      repeat match goal with
               | [ H : ?x = ?x |- _ ] => clear H
               | [ H : ?x = _ :> length_result, H' : context[?x] |- _ ] => rewrite H in H'
               | _ => exfalso; discriminate
               | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
               | _ => progress subst
               | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
               | [ H : is_true (_ ~= [ _ ])%string_like |- _ ] => apply length_singleton in H
               | [ H : _ |- _ ] => progress rewrite ?(@take_length _ string_stringlike _), ?(@drop_length _ string_stringlike _), ?substring_length, ?Plus.plus_0_r, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.add_sub in H
               | [ H : context[min ?x (?y + ?z) - ?z] |- _ ] => rewrite <- (@NPeano.Nat.sub_min_distr_r x (y + z) z) in H
               | [ H : context[min ?x ?y], H' : ?x <= ?y |- _ ] => rewrite (@Min.min_l x y) in H by assumption
               | [ H : context[min ?x ?y], H' : ?y <= ?x |- _ ] => rewrite (@Min.min_r x y) in H by assumption
               | [ H : context[min (?x - ?y) ?x] |- _ ] => rewrite (@Min.min_l (x - y) x) in H by (clear; omega)
               | [ H : forall n, same_length _ = same_length n -> _ |- _ ] => specialize (H _ eq_refl)
               | [ H : context[min _ _] |- _ ] => revert H; apply Min.min_case_strong; intros; omega
             end. }
    { intros.
      match goal with
        | [ H : context[f ?x] |- _ ] => revert H; case_eq (f x); intros
      end;
        match goal with
          | [ H : context[possible_first_terminals_of_production' ?f ?p] |- _ ] => revert H; case_eq (possible_first_terminals_of_production' f p); intros
        end;
        repeat match goal with
                 | [ H : ?x = ?x |- _ ] => clear H
                 | [ H : ?x = _ :> length_result, H' : context[?x] |- _ ] => rewrite H in H'
                 | _ => exfalso; discriminate
                 | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
                 | _ => progress subst
                 | [ H : forall n, same_length _ = same_length n -> _ |- _ ] => specialize (H _ eq_refl)
                 | _ => progress rewrite ?(@take_length _ string_stringlike _), ?(@drop_length _ string_stringlike _), ?substring_length, ?Plus.plus_0_r, ?NPeano.Nat.sub_0_r, ?NPeano.Nat.add_sub
                 | [ |- context[min ?x (?y + ?z) - ?z] ] => rewrite <- (@NPeano.Nat.sub_min_distr_r x (y + z) z)
                 | [ |- context[min (?x - ?y) ?x] ] => rewrite (@Min.min_l (x - y) x) by (clear; omega)
                 | [ H : parse_of_item _ _ (Terminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
                 | [ H : parse_of_item _ _ (NonTerminal _) |- _ ] => let p := fresh in rename H into p; dependent destruction p
                 | [ H : parse_of _ _ _ |- _ ] => eapply H_f in H; [ | eassumption.. ]
                 | _ => apply Min.min_case_strong; omega
               end. } }
Qed.

Lemma has_only_terminals_parse_of_length (G : grammar Ascii.ascii) {n}
      nt
      (H : possible_first_terminals_of G nt = same_length n)
      str
      (p : parse_of G str (Lookup G nt))
: String.length str = n.
Proof.
  unfold possible_first_terminals_of, possible_first_terminals_of_nt in H.
  revert n nt H str p.
  match goal with
    | [ |- forall a b, Fix ?wf _ _ ?x _ = _ -> _ ]
      => induction (wf x)
  end.
  intros ? ?.
  rewrite Fix1_eq by apply possible_first_terminals_of_nt_step_ext.
  unfold possible_first_terminals_of_nt_step at 1; simpl.
  edestruct dec; simpl;
  [
  | solve [ intros; discriminate ] ].
  generalize dependent (G nt).
  intros.
  unfold possible_first_terminals_of_productions' in *.
  let p := match goal with H : parse_of _ _ _ |- _ => constr:H end in
  let H := fresh in
  rename p into H;
    induction H; simpl in *.
  { match goal with
      | [ H : context[possible_first_terminals_of_production' ?f ?p] |- _ ] => revert H; case_eq (possible_first_terminals_of_production' f p); intros
    end;
    repeat match goal with
             | [ H' : rdp_list_is_valid_nonterminal ?x ?nt = true,
                      H : forall y, rdp_list_nonterminals_listT_R y ?x -> _ |- _ ]
               => specialize (fun nt' str0 n' H0 => H _ (@rdp_list_remove_nonterminal_dec _ nt H') n' nt' H0 str0)
             | [ H : possible_first_terminals_of_production' _ _ = same_length _ |- _ ] => eapply has_only_terminals_parse_of_production_length in H; [ | eassumption.. ]
             | _ => reflexivity
             | _ => discriminate
             | _ => progress subst
             | [ H : possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length in H
             | [ H : same_length _ = same_length _ |- _ ] => inversion H; clear H
             | [ H : _ /\ _ |- _ ] => destruct H
             | [ H : _ \/ _ |- _ ] => destruct H; [ (discriminate || congruence) | ]
             | [ H : _ \/ _ |- _ ] => destruct H; [ | (discriminate || congruence) ]
             | [ H : ?x = same_length _, H' : context[?x] |- _ ] => rewrite H in H'
             | [ H : fold_right possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length_fold_right in H
           end. }
  { edestruct (_ : productions _).
    { match goal with
        | [ H : parse_of _ _ [] |- _ ] => inversion H
      end. }
    { repeat match goal with
               | _ => progress simpl in *
               | [ H : possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : fold_right possible_first_terminals_of_productions'_f _ _ = same_length _ |- _ ] => apply possible_first_terminals_of_productions'_f_same_length_fold_right in H
               | [ H : fold_right possible_first_terminals_of_productions'_f _ _ = same_length _ -> _ |- _ ]
                 => specialize (fun H' => H (proj2 possible_first_terminals_of_productions'_f_same_length_fold_right H'))
               | _ => progress eauto
             end. } }
Qed.
