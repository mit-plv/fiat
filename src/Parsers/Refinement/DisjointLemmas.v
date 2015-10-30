(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
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
Require Import Fiat.Parsers.StringLike.ForallChars.
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.StringLike.FirstCharSuchThat.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Fiat.Parsers.Reachable.All.MinimalReachable.
Require Fiat.Parsers.Reachable.All.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.All.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.ReachableParse.
Require Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Fiat.Parsers.Reachable.MaybeEmpty.OfParse.

Set Implicit Arguments.

Local Ltac find_production_valid
  := repeat match goal with
              | [ H : grammar_valid ?G, HinL : In (_ ++ _::?its) (Lookup ?G ?nt), HinV' : is_true (is_valid_nonterminal _ ?nt) |- production_valid ?its ]
                => specialize (H nt HinV')
              | [ H : grammar_valid ?G, HinL : In (_ ++ (NonTerminal ?x)::_) (Lookup ?G ?nt), HinV' : is_true (is_valid_nonterminal _ ?nt) |- is_true (is_valid_nonterminal _ ?x) ]
                => specialize (H nt HinV')
              | _ => progress unfold productions_valid in *
              | [ H : Forall _ _ |- _ ] => rewrite Forall_forall in H
              | [ H : In _ (Lookup ?G ?nt), H' : forall ls, In _ (Lookup ?G ?nt) -> _ |- _ ]
                => specialize (H' _ H)
              | [ H : production_valid (_ ++ _::?x) |- production_valid ?x ]
                => apply production_valid_app in H
              | [ H : production_valid (_ ++ (NonTerminal ?x)::_) |- is_true (is_valid_nonterminal _ ?x) ]
                => apply production_valid_app in H
              | [ H : production_valid (_::?x) |- production_valid ?x ]
                => apply production_valid_cons in H
              | [ H : production_valid (?x::_) |- _ ]
                => inversion H; subst; clear H
              | _ => assumption
            end.

Section all_possible.
  Context {Char : Type}.
  Definition possible_terminals := list Char.

  Local Instance all_possible_fold_data : fold_grammar_data Char possible_terminals
    := { on_terminal ch := [ch];
         on_redundant_nonterminal nt := nil;
         on_nil_production := nil;
         combine_production := @app _;
         on_nil_productions := nil;
         combine_productions := @app _;
         on_nonterminal nt v := v }.

  Definition possible_terminals_of : grammar Char -> String.string -> possible_terminals
    := @fold_nt _ _ all_possible_fold_data.
  Definition possible_terminals_of_productions : grammar Char -> productions Char -> possible_terminals
    := @fold_productions _ _ all_possible_fold_data.
  Definition possible_terminals_of_production : grammar Char -> production Char -> possible_terminals
    := @fold_production _ _ all_possible_fold_data.
End all_possible.

Section only_first.
  Context (G : grammar Ascii.ascii)
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}.

  Record possible_first_terminals :=
    { actual_possible_first_terminals :> list Ascii.ascii;
      might_be_empty : bool }.

  Local Instance only_first_fold_data (predata := @rdp_list_predata _ G) : fold_grammar_data Ascii.ascii possible_first_terminals
    := { on_terminal ch := {| actual_possible_first_terminals := [ch] ; might_be_empty := false |};
         on_redundant_nonterminal nt := {| actual_possible_first_terminals := nil ; might_be_empty := is_valid_nonterminal initial_nonterminals_data nt && brute_force_parse_nonterminal G (of_string nil) nt |};
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
               := (might_be_empty first_of_first || might_be_empty first_of_rest)%bool |};
         on_nonterminal nt v := v }.

  Definition possible_first_terminals_of : String.string -> possible_first_terminals
    := @fold_nt _ _ only_first_fold_data G.
  Definition possible_first_terminals_of_productions : productions Ascii.ascii -> possible_first_terminals
    := @fold_productions _ _ only_first_fold_data G.
  Definition possible_first_terminals_of_production : production Ascii.ascii -> possible_first_terminals
    := @fold_production _ _ only_first_fold_data G.
End only_first.

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

  Local Ltac ddestruction H
    := let p := fresh in rename H into p; dependent destruction p.

  Local Ltac t' :=
    idtac;
    match goal with
      | _ => rewrite in_app_iff
      | _ => progress simpl in *
      | _ => intro
      | _ => progress destruct_head inhabited
      | _ => progress destruct_head iff
      | _ => progress subst
      | _ => reflexivity
      | _ => congruence
      | _ => tauto
      | [ ch : Char, H : forall ch : Char, _ |- _ ] => specialize (H ch)
      | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
      | _ => progress destruct_head or
      | [ |- _ <-> _ ] => split
      | [ |- inhabited _ ] => constructor
      | _ => assumption
      | _ => left; assumption
      | _ => right; assumption
      | [ H : ?A -> ?B |- ?B ] => apply H; clear H
      | [ H : All.MinimalReachable.minimal_reachable_from_item _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_item _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_production _ _ nil |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_production _ _ (_::_) |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_productions _ _ nil |- _ ] => ddestruction H
      | [ H : All.MinimalReachable.minimal_reachable_from_productions _ _ (_::_) |- _ ] => ddestruction H
    end.

  Local Ltac t := repeat first [ t' | left; solve [ t ] | right; solve [ t ] ].

  Local Instance all_possible_ccdata : @fold_grammar_correctness_computational_data Char _ G
    := { Pnt valid0 nt ls
         := forall ch : Char, List.In ch ls <-> inhabited (All.MinimalReachable.minimal_reachable_from_item (G := G) ch valid0 (NonTerminal nt));
         Ppat valid0 pat ls
         := forall ch : Char, List.In ch ls <-> inhabited (All.MinimalReachable.minimal_reachable_from_production (G := G) ch valid0 pat);
         Ppats valid0 pats ls
         := forall ch : Char, List.In ch ls <-> inhabited (All.MinimalReachable.minimal_reachable_from_productions (G := G) ch valid0 pats) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.

  Local Instance all_possible_cdata : @fold_grammar_correctness_data Char _ all_possible_fold_data G
    := { fgccd := all_possible_ccdata }.
  Proof.
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
  Defined.

  Lemma possible_terminals_of_correct (G : grammar Char)
        (Hvalid : grammar_rvalid G)
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (His_valid : is_valid_nonterminal initial_nonterminals_data nt)
        (p : parse_of_item G str (NonTerminal nt))
  : forall_chars__char_in str (possible_terminals_of G nt).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of.
    pose proof (fun k => All.ReachableParse.forall_chars_reachable_from_parse_of_item p (Forall_parse_of_item_valid Hvalid' k p)) as H.
    specialize (H His_valid).
    revert H.
    setoid_rewrite All.MinimalReachableOfReachable.minimal_reachable_from_item__iff__reachable_from_item.
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    let f := constr:(fold_nt_correct (G := G) nt) in
    apply (f ch).
  Qed.
End all_possible_correctness.

Section only_first_correctness.
  Context (G : grammar Ascii.ascii)
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}
          (Hvalid : grammar_rvalid G).
  Local Open Scope string_like_scope.

  Local Existing Instance only_first_fold_data.

  Local Ltac dependent_destruction_head h :=
    idtac;
    match goal with
      | [ H : ?T |- _ ] => let x := head T in
                           constr_eq h x;
                             let H' := fresh in
                             rename H into H';
                               dependent destruction H'
    end.

  Local Ltac ddestruction H
    := let p := fresh in rename H into p; dependent destruction p.

  Local Ltac t' :=
    idtac;
    match goal with
      | [ Hvalid : is_true (grammar_rvalid G) |- grammar_valid G ] => apply grammar_rvalid_correct; assumption
      | _ => rewrite in_app_iff
      | _ => progress simpl in *
      | [ H : context[?b = true] |- _ ] => change (b = true) with (is_true b) in H
      | _ => intro
      | _ => progress destruct_head inhabited
      | _ => progress destruct_head iff
      | _ => progress destruct_head and
      | _ => progress subst
      | _ => reflexivity
      | _ => congruence
      | _ => tauto
      | _ => assumption
      | _ => left; assumption
      | _ => right; assumption
      | _ => constructor; assumption
      | _ => solve [ constructor ]
      | _ => progress unfold brute_force_parse_nonterminal in *
      | [ ch : Ascii.ascii, H : forall ch : Ascii.ascii, _ |- _ ] => specialize (H ch)
      | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
      | [ H : _, H' : ?A -> ?B |- _ ] => specialize (H' (sub_nonterminals_listT_remove_2 H))
      | [ H : is_true (is_valid_nonterminal ?v ?nt), H' : sub_nonterminals_listT ?v _ |- _ ]
        => unique pose proof (H' _ H)
      | [ H : is_valid_nonterminal ?v ?nt = true, H' : sub_nonterminals_listT ?v _ |- _ ]
        => unique pose proof (H' _ H)
      | [ H : is_true (andb _ _) |- _ ] => apply Bool.andb_true_iff in H
      | [ |- is_true (andb _ _) ] => apply Bool.andb_true_iff
      | [ H : is_true (orb _ _) |- _ ] => apply Bool.orb_true_iff in H
      | [ |- is_true (orb _ _) ] => apply Bool.orb_true_iff
      | _ => progress destruct_head or
      | [ |- _ <-> _ ] => split
      | [ |- _ /\ _ ] => split
      | [ H : appcontext[if ?e then _ else _] |- _ ] => revert H; case_eq e
      | [ H : inhabited ?A -> ?B |- _ ] => specialize (fun a => H (inhabits a))
      | [ |- inhabited _ ] => constructor
      | [ |- appcontext[if ?e then _ else _] ] => case_eq e
      | [ |- _ \/ False ] => left
      | [ H : is_true (BooleanRecognizer.parse_nonterminal _ _) |- _ ]
        => apply parse_nonterminal_sound in H
      | [ H : ?A -> ?B |- ?B ] => apply H; clear H
      | [ H : OnlyFirst.MinimalReachable.minimal_reachable_from_item _ _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : OnlyFirst.MinimalReachable.minimal_reachable_from_item _ _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : OnlyFirst.MinimalReachable.minimal_reachable_from_production _ _ _ nil |- _ ] => ddestruction H
      | [ H : OnlyFirst.MinimalReachable.minimal_reachable_from_production _ _ _ (_::_) |- _ ] => ddestruction H
      | [ H : OnlyFirst.MinimalReachable.minimal_reachable_from_productions _ _ _ nil |- _ ] => ddestruction H
      | [ H : OnlyFirst.MinimalReachable.minimal_reachable_from_productions _ _ _ (_::_) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_item _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_item _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_production _ _ nil |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_production _ _ (_::_) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_productions _ _ nil |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_productions _ _ (_::_) |- _ ] => ddestruction H
      | _ => right; eauto;
             apply MaybeEmpty.MinimalOfCore.minimal_maybe_empty_item__of__maybe_empty_item;
             constructor; assumption
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_item _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_item__of__minimal_maybe_empty_item in H; [ | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_production _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_production__of__minimal_maybe_empty_production in H; [ | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_productions _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_productions__of__minimal_maybe_empty_productions in H; [ | reflexivity ]
      | [ m : MaybeEmpty.Core.maybe_empty_productions _ _ _ |- _ ]
        => let f := constr:(@MaybeEmpty.OfParse.parse_empty_from_maybe_empty_parse_of_productions _ _ _) in
           eapply f with (str := of_string nil) in m; [ | (assumption || (rewrite ?of_string_length; reflexivity)).. ];
           eapply parse_nonterminal_complete; destruct_head sigT; eassumption
      | [ Hvalid : is_true (grammar_rvalid G) |- _ ] => apply grammar_rvalid_correct in Hvalid
      | [ Hvalid : grammar_valid G, Hnt : is_true (is_valid_nonterminal _ _), p : parse_of_item _ _ _ |- _ ]
        => idtac;
          let pf := constr:(fun k => Forall_parse_of_item_valid Hvalid k p) in
          let pf' := constr:(pf Hnt) in
          let T := (type of pf') in
          let T' := (eval simpl in T) in
          unique pose proof (pf' : T')
      | _ => eapply MaybeEmpty.OfParse.parse_empty_maybe_empty_parse_of_item; try eassumption; rewrite ?of_string_length; reflexivity
    end.

  Local Ltac t := repeat first [ t' | left; solve [ t ] | right; solve [ t ] ].

  Local Instance only_first_ccdata
        (predata := @rdp_list_predata _ G)
  : @fold_grammar_correctness_computational_data Ascii.ascii possible_first_terminals G
    := { Pnt valid0 nt pft
         := forall ch : Ascii.ascii,
              sub_nonterminals_listT valid0 initial_nonterminals_data
              -> (List.In ch pft <-> inhabited (OnlyFirst.MinimalReachable.minimal_reachable_from_item (G := G) initial_nonterminals_data ch valid0 (NonTerminal nt)))
                 /\ (might_be_empty pft <-> inhabited (MaybeEmpty.Core.maybe_empty_item G initial_nonterminals_data (NonTerminal nt)));
         Ppat valid0 pat pft
         := forall ch : Ascii.ascii,
              sub_nonterminals_listT valid0 initial_nonterminals_data
              -> (List.In ch pft <-> inhabited (OnlyFirst.MinimalReachable.minimal_reachable_from_production (G := G) initial_nonterminals_data ch valid0 pat))
                 /\ (might_be_empty pft <-> inhabited (MaybeEmpty.Core.maybe_empty_production G initial_nonterminals_data pat));
         Ppats valid0 pats pft
         := forall ch : Ascii.ascii,
              sub_nonterminals_listT valid0 initial_nonterminals_data
              -> (List.In ch pft <-> inhabited (OnlyFirst.MinimalReachable.minimal_reachable_from_productions (G := G) initial_nonterminals_data ch valid0 pats))
                 /\ (might_be_empty pft <-> inhabited (MaybeEmpty.Core.maybe_empty_productions G initial_nonterminals_data pats)) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.
  Local Arguments initial_nonterminals_data : simpl never.

  Local Instance only_first_cdata
        (rdata := rdp_list_rdata' (G := G))
        (cdata := brute_force_cdata G)
  : @fold_grammar_correctness_data Ascii.ascii possible_first_terminals (only_first_fold_data G) G
    := { fgccd := only_first_ccdata }.
  Proof.
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
  Defined.

  Lemma possible_first_terminals_of_production_correct
        (predata := @rdp_list_predata _ G)
        (str : String) pat
        (p : parse_of_production G str pat)
        (His_valid : production_valid pat)
  : first_char_in str (possible_first_terminals_of_production G pat).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of_production.
    generalize (OnlyFirst.ReachableParse.for_first_char_reachable_from_parse_of_production (reflexivity _) p).
    setoid_rewrite OnlyFirst.MinimalReachableOfReachable.minimal_reachable_from_production__iff__reachable_from_production.
    intro H; specialize (H (Forall_parse_of_production_valid Hvalid' His_valid p)); revert H.
    apply for_first_char__impl__first_char_in.
    intro ch.
    apply (fold_production_correct (FGCD := only_first_cdata) pat); reflexivity.
  Qed.

  Lemma possible_first_terminals_of_production_empty_correct
        (predata := @rdp_list_predata _ G)
        (str : String) (Hlen : length str = 0) pat
        (p : parse_of_production G str pat)
        (His_valid : production_valid pat)
  : might_be_empty (possible_first_terminals_of_production G pat).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of_production.
    apply (fold_production_correct (FGCD := only_first_cdata) pat).
    { repeat constructor. }
    { reflexivity. }
    { constructor.
      eapply MaybeEmpty.OfParse.parse_empty_maybe_empty_parse_of_production;
        try (eassumption || (apply Forall_parse_of_production_valid; assumption) || reflexivity).
      Grab Existential Variables.
      assumption. }
  Qed.
End only_first_correctness.

Local Open Scope string_like_scope.

Local Arguments string_beq : simpl never.

Lemma terminals_disjoint_search_for_not' {G : grammar Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      (Hvalid : grammar_rvalid G)
      (str : @String Ascii.ascii HSL)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
: forall_chars__char_in (take n str) (possible_terminals_of G nt)
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (for_first_char
            (drop n str)
            (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of G nt)))
          /\ n < length str)).
Proof.
  pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
  destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
  pose proof HinV as HinV';
    rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
  apply and_comm; split.
  { destruct (Compare_dec.le_dec (length str) n); [ left | right ].
    { split; trivial.
      pose proof (drop_length str n) as H.
      rewrite (proj2 (Nat.sub_0_le (length str) n)) in H by assumption.
      generalize dependent (drop n str); clear -pit HinV' HinL Hvalid Hvalid' HSLP HSIP.
      intros.
      eapply possible_first_terminals_of_production_empty_correct; try eassumption.
      find_production_valid. }
    { split; try omega; [].
      eapply first_char_in__impl__for_first_char;
      [
      | apply possible_first_terminals_of_production_correct; [ .. | eassumption | ];
        find_production_valid ];
      [].
      intros ch H'.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H''.
      apply list_in_bl in H''; [ | apply (@ascii_bl) ].
      eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
      apply H_disjoint.
      apply list_in_lb; [ apply (@ascii_lb) | assumption ]. } }
  { apply (fun x y => possible_terminals_of_correct x y pit);
    try assumption;
    find_production_valid. }
Qed.

Lemma terminals_disjoint_search_for_not {G : grammar Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      (Hvalid : grammar_rvalid G)
      (str : @String Ascii.ascii HSL)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
: is_first_char_such_that
    (might_be_empty (possible_first_terminals_of_production G its))
    str
    n
    (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of G nt))).
Proof.
  pose proof (terminals_disjoint_search_for_not' Hvalid _ H_disjoint pit pits H_reachable) as H.
  split;
    [ destruct H as [H0 H1]
    | destruct H as [H0 [[H1 H2] | H1]]; solve [ left; eauto | right; eauto ] ].
  revert H0.
  apply forall_chars__char_in__impl__forall_chars.
  intros ch H' H''.
  apply Bool.negb_true_iff, Bool.not_true_iff_false in H''.
  apply H''.
  apply list_in_lb; [ apply (@ascii_lb) | ]; assumption.
Qed.

Lemma terminals_disjoint_search_for' {G : grammar Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      (Hvalid : grammar_rvalid G)
      (str : @String Ascii.ascii HSL)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
: forall_chars (take n str)
               (fun ch => negb (list_bin ascii_beq ch (possible_first_terminals_of_production G its)))
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (first_char_in
            (drop n str)
            (possible_first_terminals_of_production G its)
          /\ n < length str)).
Proof.
  pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
  destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
  pose proof HinV as HinV';
    rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
  apply and_comm; split.
  { destruct (Compare_dec.le_dec (length str) n); [ left | right ].
    { split; trivial.
      pose proof (drop_length str n) as H.
      rewrite (proj2 (Nat.sub_0_le (length str) n)) in H by assumption.
      generalize dependent (drop n str); clear -pit HinV' HinL Hvalid Hvalid' HSLP HSIP.
      intros.
      eapply possible_first_terminals_of_production_empty_correct; try eassumption.
      find_production_valid. }
    { split; try omega; try assumption.
      apply possible_first_terminals_of_production_correct; try assumption.
      find_production_valid. } }
  { eapply forall_chars__char_in__impl__forall_chars.
    { intros ch H'.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H''.
      apply list_in_bl in H''; [ | apply (@ascii_bl) ].
      eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
      apply H_disjoint.
      apply list_in_lb; [ apply (@ascii_lb) | assumption ]. }
    { apply possible_terminals_of_correct; try assumption.
      find_production_valid. } }
Qed.

Lemma terminals_disjoint_search_for {G : grammar Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      (Hvalid : grammar_rvalid G)
      (str : @String Ascii.ascii HSL)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
: is_first_char_such_that
    (might_be_empty (possible_first_terminals_of_production G its))
    str
    n
    (fun ch => list_bin ascii_beq ch (possible_first_terminals_of_production G its)).
Proof.
  pose proof (terminals_disjoint_search_for' Hvalid _ H_disjoint pit pits H_reachable) as H.
  split;
    [ destruct H as [H0 H1]
    | destruct H as [H0 [[H1 H2] | [H1 ?]]]; [ right | left; split ]; eauto ].
  { revert H0.
    apply forall_chars_Proper; [ reflexivity | ].
    intros ch H' H''.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in H'.
    apply H'.
    assumption. }
  { revert H1.
    apply first_char_in__impl__for_first_char.
    intros ch H'.
    apply list_in_lb; [ apply (@ascii_lb) | ]; assumption. }
Qed.
