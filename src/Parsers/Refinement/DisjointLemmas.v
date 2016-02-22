(** Sharpened ADT for an expression grammar with parentheses *)
Require Import Coq.Init.Wf Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Fiat.Parsers.ContextFreeGrammar.Core.
Require Import Fiat.Parsers.ContextFreeGrammar.PreNotations.
Require Import Fiat.Parsers.ContextFreeGrammar.Equality.
Require Import Coq.Program.Equality.
Require Import Fiat.Common.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.Wf.
Require Import Fiat.Common.Enumerable.
Require Import Fiat.Common.LogicFacts.
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
Require Import Fiat.Parsers.StringLike.LastChar.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammar.Properties.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Parsers.BaseTypesLemmas.
Require Import Fiat.Parsers.ContextFreeGrammar.Valid.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidProperties.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Common.BoolFacts.
Require Fiat.Parsers.Reachable.All.MinimalReachable.
Require Fiat.Parsers.Reachable.All.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.All.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyFirst.ReachableParse.
Require Fiat.Parsers.Reachable.OnlyLast.MinimalReachable.
Require Fiat.Parsers.Reachable.OnlyLast.MinimalReachableOfReachable.
Require Fiat.Parsers.Reachable.OnlyLast.ReachableParse.
Require Fiat.Parsers.Reachable.MaybeEmpty.Core.
Require Fiat.Parsers.Reachable.MaybeEmpty.MinimalOfCore.
Require Fiat.Parsers.Reachable.MaybeEmpty.OfParse.

Set Implicit Arguments.

Local Ltac find_production_valid
  := repeat match goal with
              | [ H : is_true (is_valid_nonterminal initial_nonterminals_data _) |- _ ]
                => apply initial_nonterminals_correct in H
              | [ H : grammar_valid ?G, HinL : In (_ ++ _::?its) (Lookup ?G ?nt), HinV' : List.In ?nt (Valid_nonterminals ?G) |- production_valid ?its ]
                => specialize (H nt HinV')
              | [ H : grammar_valid ?G, HinL : In (_ ++ (NonTerminal ?x)::_) (Lookup ?G ?nt), HinV' : List.In ?nt (Valid_nonterminals ?G) |- is_true (is_valid_nonterminal _ (of_nonterminal ?x)) ]
                => specialize (H nt HinV')
              | _ => progress unfold productions_valid in *
              | [ H : Forall _ _ |- _ ] => rewrite Forall_forall in H
              | [ H : In _ (Lookup ?G ?nt), H' : forall ls, In _ (Lookup ?G ?nt) -> _ |- _ ]
                => specialize (H' _ H)
              | [ H : production_valid (_ ++ _::?x) |- production_valid ?x ]
                => apply production_valid_app in H
              | [ H : production_valid (_ ++ (NonTerminal ?x)::_) |- is_true (is_valid_nonterminal _ (of_nonterminal ?x)) ]
                => apply production_valid_app in H
              | [ H : production_valid (_::?x) |- production_valid ?x ]
                => apply production_valid_cons in H
              | [ H : production_valid (?x::_) |- _ ]
                => inversion H; subst; clear H
              | _ => assumption
            end.

Section maybe_empty.
  Context {Char : Type}.

  Local Instance maybe_empty_fold_data : fold_grammar_data Char bool
    := { on_terminal P := false;
         on_redundant_nonterminal nt := false;
         on_nil_production := true;
         combine_production := andb;
         on_nil_productions := false;
         combine_productions := orb;
         on_nonterminal nt v := v }.

  Definition maybe_empty_of : pregrammar Char -> String.string -> bool
    := @fold_nt _ _ maybe_empty_fold_data.
  Definition maybe_empty_of_productions : pregrammar Char -> productions Char -> bool
    := @fold_productions _ _ maybe_empty_fold_data.
  Definition maybe_empty_of_production : pregrammar Char -> production Char -> bool
    := @fold_production _ _ maybe_empty_fold_data.
End maybe_empty.

Section all_possible.
  Context {Char : Type} {HEC : Enumerable Char}.
  Definition possible_terminals := list Char.

  Local Instance all_possible_fold_data : fold_grammar_data Char possible_terminals
    := { on_terminal P := filter P (Enumerable.enumerate Char);
         on_redundant_nonterminal nt := nil;
         on_nil_production := nil;
         combine_production := @app _;
         on_nil_productions := nil;
         combine_productions := @app _;
         on_nonterminal nt v := v }.

  Definition possible_terminals_of : pregrammar Char -> String.string -> possible_terminals
    := @fold_nt _ _ all_possible_fold_data.
  Definition possible_terminals_of_productions : pregrammar Char -> productions Char -> possible_terminals
    := @fold_productions _ _ all_possible_fold_data.
  Definition possible_terminals_of_production : pregrammar Char -> production Char -> possible_terminals
    := @fold_production _ _ all_possible_fold_data.
End all_possible.

Section only_first.
  Context (G : pregrammar Ascii.ascii)
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}.

  Record possible_first_terminals :=
    { actual_possible_first_terminals :> list Ascii.ascii;
      might_be_empty : bool }.

  Local Instance only_first_fold_data (predata := @rdp_list_predata _ G) : fold_grammar_data Ascii.ascii possible_first_terminals
    := { on_terminal P
         := {| actual_possible_first_terminals := filter P (Enumerable.enumerate Ascii.ascii);
               might_be_empty := false |};
         on_redundant_nonterminal nt := {| actual_possible_first_terminals := nil ; might_be_empty := maybe_empty_of G nt |};
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

Section only_last.
  Context (G : pregrammar Ascii.ascii)
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}.

  Record possible_last_terminals :=
    { actual_possible_last_terminals :> list Ascii.ascii;
      might_be_empty' : bool }.

  Local Instance only_last_fold_data (predata := @rdp_list_predata _ G) : fold_grammar_data Ascii.ascii possible_last_terminals
    := { on_terminal P
         := {| actual_possible_last_terminals := filter P (Enumerable.enumerate Ascii.ascii);
               might_be_empty' := false |};
         on_redundant_nonterminal nt := {| actual_possible_last_terminals := nil ; might_be_empty' := maybe_empty_of G nt |};
         on_nil_production := {| actual_possible_last_terminals := nil ; might_be_empty' := true |};
         on_nil_productions := {| actual_possible_last_terminals := nil ; might_be_empty' := false |};
         combine_production last_of_first last_of_rest
         := {| actual_possible_last_terminals
               := (actual_possible_last_terminals last_of_rest)
                    ++ (if might_be_empty' last_of_rest
                        then actual_possible_last_terminals last_of_first
                        else []);
               might_be_empty'
               := (might_be_empty' last_of_first && might_be_empty' last_of_rest)%bool |};
         combine_productions last_of_first last_of_rest
         := {| actual_possible_last_terminals
               := (actual_possible_last_terminals last_of_first)
                    ++ (actual_possible_last_terminals last_of_rest);
               might_be_empty'
               := (might_be_empty' last_of_first || might_be_empty' last_of_rest)%bool |};
         on_nonterminal nt v := v }.

  Definition possible_last_terminals_of : String.string -> possible_last_terminals
    := @fold_nt _ _ only_last_fold_data G.
  Definition possible_last_terminals_of_productions : productions Ascii.ascii -> possible_last_terminals
    := @fold_productions _ _ only_last_fold_data G.
  Definition possible_last_terminals_of_production : production Ascii.ascii -> possible_last_terminals
    := @fold_production _ _ only_last_fold_data G.
End only_last.

Section maybe_empty_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {HEC : Enumerable Char}.
  Local Open Scope string_like_scope.

  Local Existing Instance maybe_empty_fold_data.

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
      | _ => progress bool_congr
      | _ => progress specialize_by ltac:(exact eq_refl)
      | _ => progress specialize_by assumption
      | _ => progress specialize_by ltac:(constructor; assumption)
      | _ => progress destruct_head iff
      | _ => progress destruct_head and
      | _ => progress destruct_head inhabited
      | _ => progress subst
      | _ => reflexivity
      | _ => congruence
      | _ => tauto
      | [ ch : Char, H : forall ch : Char, _ |- _ ] => specialize (H ch)
      | [ H : ?A, H' : ?A -> ?B |- _ ] => specialize (H' H)
      | _ => progress destruct_head or
      | [ |- _ <-> _ ] => split
      | [ |- _ /\ _ ] => split
      | [ |- inhabited _ ] => constructor
      | _ => assumption
      | _ => constructor; assumption
      | _ => left; assumption
      | _ => right; assumption
      | [ H : ?A -> ?B |- ?B ] => apply H; clear H
      | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
      | [ |- context[In _ (filter _ _)] ] => rewrite filter_In
      | [ |- In _ (Enumerable.enumerate _) ] => apply enumerate_correct
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_item _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_item _ (Terminal _) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_production _ nil |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_production _ (_::_) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_productions _ nil |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_productions _ (_::_) |- _ ] => ddestruction H
    end.

  Local Ltac t := repeat first [ t' | left; solve [ t ] | right; solve [ t ] ].

  Local Instance maybe_empty_ccdata : @fold_grammar_correctness_computational_data Char _ G
    := { Pnt valid0 nt b
         := b = true <-> inhabited (MaybeEmpty.Minimal.minimal_maybe_empty_item (G := G) valid0 (NonTerminal nt));
         Ppat valid0 pat b
         := b = true <-> inhabited (MaybeEmpty.Minimal.minimal_maybe_empty_production (G := G) valid0 pat);
         Ppats valid0 pats b
         := b = true <-> inhabited (MaybeEmpty.Minimal.minimal_maybe_empty_productions (G := G) valid0 pats) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.

  Local Instance maybe_empty_cdata : @fold_grammar_correctness_data Char _ maybe_empty_fold_data G
    := { fgccd := maybe_empty_ccdata }.
  Proof.
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
  Defined.

  Lemma maybe_empty_of_correct (G : pregrammar Char)
        (predata := @rdp_list_predata _ G)
        nt
    : maybe_empty_of G nt = true <-> inhabited (MaybeEmpty.Core.maybe_empty_item G initial_nonterminals_data (NonTerminal nt)).
  Proof.
    simpl rewrite (fold_nt_correct (G := G) nt).
    simpl rewrite MaybeEmpty.MinimalOfCore.minimal_maybe_empty_item__iff__maybe_empty_item; reflexivity.
  Qed.

  Lemma maybe_empty_of_production_correct (G : pregrammar Char)
        (predata := @rdp_list_predata _ G)
        pat
    : maybe_empty_of_production G pat = true <-> inhabited (MaybeEmpty.Core.maybe_empty_production G initial_nonterminals_data pat).
  Proof.
    simpl rewrite (fold_production_correct (G := G) pat).
    simpl rewrite MaybeEmpty.MinimalOfCore.minimal_maybe_empty_production__iff__maybe_empty_production; reflexivity.
  Qed.

  Lemma maybe_empty_of_productions_correct (G : pregrammar Char)
        (predata := @rdp_list_predata _ G)
        pat
    : maybe_empty_of_productions G pat = true <-> inhabited (MaybeEmpty.Core.maybe_empty_productions G initial_nonterminals_data pat).
  Proof.
    simpl rewrite (fold_productions_correct (G := G) pat).
    simpl rewrite MaybeEmpty.MinimalOfCore.minimal_maybe_empty_productions__iff__maybe_empty_productions; reflexivity.
  Qed.

  (*Lemma maybe_empty_correct (G : pregrammar Char)
        (Hvalid : grammar_rvalid G)
        (predata := @rdp_list_predata _ G)
        nt
        (His_valid : is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt))
    : maybe_empty_of G nt = true <-> forall str, parse_of_item G str (NonTerminal nt) -> length str = 0.
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    let f := constr:(fold_nt_correct (G := G) nt) in
    simpl rewrite f.
    pose @MaybeEmpty.OfParse.parse_empty_from_maybe_empty_parse_of_item.
    pose @MaybeEmpty.OfParse.parse_empty_minimal_maybe_empty_parse_of_item.
    simpl in p.
    apply (f ch).
    pose proof (fun k => All.ReachableParse.forall_chars_reachable_from_parse_of_item p (Forall_parse_of_item_valid Hvalid' k p)) as H.
    specialize (H His_valid).
    revert H.
    setoid_rewrite (All.MinimalReachableOfReachable.minimal_reachable_from_item__iff__reachable_from_item (reflexivity _)).
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    let f := constr:(fold_nt_correct (G := G) nt) in
    apply (f ch).
  Qed.

  Lemma maybe_empty_production_correct (G : pregrammar Char)
        (Hvalid : grammar_rvalid G)
        (predata := @rdp_list_predata _ G)
        (str : String) pat
        (His_valid : production_valid pat)
        (p : parse_of_production G str pat)
  : forall_chars__char_in str (maybe_empty_production G pat).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of.
    pose proof (fun k => All.ReachableParse.forall_chars_reachable_from_parse_of_production p (Forall_parse_of_production_valid Hvalid' k p)) as H.
    specialize (H His_valid).
    revert H.
    setoid_rewrite (All.MinimalReachableOfReachable.minimal_reachable_from_production__iff__reachable_from_production (reflexivity _)).
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    let f := constr:(fold_production_correct (G := G) pat) in
    apply (f ch).
  Qed.*)
End maybe_empty_correctness.

Section all_possible_correctness.
  Context {Char : Type} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char} {HEC : Enumerable Char}.
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
      | [ |- _ /\ _ ] => split
      | [ |- inhabited _ ] => constructor
      | _ => assumption
      | _ => left; assumption
      | _ => right; assumption
      | [ H : ?A -> ?B |- ?B ] => apply H; clear H
      | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
      | [ |- context[In _ (filter _ _)] ] => rewrite filter_In
      | [ |- In _ (Enumerable.enumerate _) ] => apply enumerate_correct
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

  Lemma possible_terminals_of_correct (G : pregrammar Char)
        (Hvalid : grammar_rvalid G)
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (His_valid : is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt))
        (p : parse_of_item G str (NonTerminal nt))
  : forall_chars__char_in str (possible_terminals_of G nt).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of.
    pose proof (fun k => All.ReachableParse.forall_chars_reachable_from_parse_of_item p (Forall_parse_of_item_valid Hvalid' k p)) as H.
    specialize (H His_valid).
    revert H.
    setoid_rewrite (All.MinimalReachableOfReachable.minimal_reachable_from_item__iff__reachable_from_item (reflexivity _)).
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    let f := constr:(fold_nt_correct (G := G) nt) in
    apply (f ch).
  Qed.

  Lemma possible_terminals_of_production_correct (G : pregrammar Char)
        (Hvalid : grammar_rvalid G)
        (predata := @rdp_list_predata _ G)
        (str : String) pat
        (His_valid : production_valid pat)
        (p : parse_of_production G str pat)
  : forall_chars__char_in str (possible_terminals_of_production G pat).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of.
    pose proof (fun k => All.ReachableParse.forall_chars_reachable_from_parse_of_production p (Forall_parse_of_production_valid Hvalid' k p)) as H.
    specialize (H His_valid).
    revert H.
    setoid_rewrite (All.MinimalReachableOfReachable.minimal_reachable_from_production__iff__reachable_from_production (reflexivity _)).
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    let f := constr:(fold_production_correct (G := G) pat) in
    apply (f ch).
  Qed.
End all_possible_correctness.

Section only_first_correctness.
  Context (G : pregrammar Ascii.ascii)
          {HSLM : StringLikeMin Ascii.ascii}
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
      | [ Hvalid : is_true (grammar_rvalid _) |- grammar_valid _ ] => apply grammar_rvalid_correct; assumption
      | _ => rewrite in_app_iff
      | _ => progress simpl in *
      | [ |- context[maybe_empty_of _ _] ]
        => setoid_rewrite maybe_empty_of_correct
      | [ |- context[maybe_empty_of_production _ _] ]
        => setoid_rewrite maybe_empty_of_production_correct
      | [ |- context[maybe_empty_of_productions _ _] ]
        => setoid_rewrite maybe_empty_of_productions_correct
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
      | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
      | [ |- context[In _ (filter _ _)] ] => rewrite filter_In
      | [ |- In _ (Enumerable.enumerate _) ] => apply enumerate_correct
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
             first [ constructor; assumption | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_item _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_item__of__minimal_maybe_empty_item in H; [ | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_production _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_production__of__minimal_maybe_empty_production in H; [ | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_productions _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_productions__of__minimal_maybe_empty_productions in H; [ | reflexivity ]
      | [ m : MaybeEmpty.Core.maybe_empty_productions _ _ _ |- _ ]
        => let f := constr:(@MaybeEmpty.OfParse.parse_empty_from_maybe_empty_parse_of_productions _ _ _) in
           eapply f with (str := of_string nil) in m; [ | (assumption || (rewrite ?of_string_length; reflexivity)).. ];
           eapply parse_of_nonterminal_complete; destruct_head sigT;
           first [ assumption
                 | apply rdp_list_initial_nonterminals_correct; assumption ]
      | [ Hvalid : is_true (grammar_rvalid _) |- _ ] => apply grammar_rvalid_correct in Hvalid
      | [ Hvalid : grammar_valid _, Hnt : is_true (is_valid_nonterminal _ _), p : parse_of_item _ _ _ |- _ ]
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

  Local Opaque enumerable_ascii.

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
    setoid_rewrite (OnlyFirst.MinimalReachableOfReachable.minimal_reachable_from_production__iff__reachable_from_production (reflexivity _)).
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

Section only_last_correctness.
  Context (G : pregrammar Ascii.ascii)
          {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}
          (Hvalid : grammar_rvalid G).
  Local Open Scope string_like_scope.

  Local Existing Instance only_last_fold_data.

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
      | [ Hvalid : is_true (grammar_rvalid _) |- grammar_valid _ ] => apply grammar_rvalid_correct; assumption
      | _ => rewrite in_app_iff
      | _ => progress simpl in *
      | [ |- context[maybe_empty_of _ _] ]
        => setoid_rewrite maybe_empty_of_correct
      | [ |- context[maybe_empty_of_production _ _] ]
        => setoid_rewrite maybe_empty_of_production_correct
      | [ |- context[maybe_empty_of_productions _ _] ]
        => setoid_rewrite maybe_empty_of_productions_correct
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
      | [ H : In _ (filter _ _) |- _ ] => apply filter_In in H
      | [ |- context[In _ (filter _ _)] ] => rewrite filter_In
      | [ |- In _ (Enumerable.enumerate _) ] => apply enumerate_correct
      | [ H : is_true (BooleanRecognizer.parse_nonterminal _ _) |- _ ]
        => apply parse_nonterminal_sound in H
      | [ H : ?A -> ?B |- ?B ] => apply H; clear H
      | [ H : OnlyLast.MinimalReachable.minimal_reachable_from_item _ _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : OnlyLast.MinimalReachable.minimal_reachable_from_item _ _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : OnlyLast.MinimalReachable.minimal_reachable_from_production _ _ _ nil |- _ ] => ddestruction H
      | [ H : OnlyLast.MinimalReachable.minimal_reachable_from_production _ _ _ (_::_) |- _ ] => ddestruction H
      | [ H : OnlyLast.MinimalReachable.minimal_reachable_from_productions _ _ _ nil |- _ ] => ddestruction H
      | [ H : OnlyLast.MinimalReachable.minimal_reachable_from_productions _ _ _ (_::_) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_item _ _ (NonTerminal _) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_item _ _ (Terminal _) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_production _ _ nil |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_production _ _ (_::_) |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_productions _ _ nil |- _ ] => ddestruction H
      | [ H : MaybeEmpty.Core.maybe_empty_productions _ _ (_::_) |- _ ] => ddestruction H
      | _ => right; eauto;
             apply MaybeEmpty.MinimalOfCore.minimal_maybe_empty_item__of__maybe_empty_item;
             first [ constructor; assumption | reflexivity ]
      | _ => left;
             solve [ apply MaybeEmpty.MinimalOfCore.minimal_maybe_empty_production__of__maybe_empty_production;
                     first [ reflexivity | assumption ]
                   | constructor; eauto ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_item _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_item__of__minimal_maybe_empty_item in H; [ | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_production _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_production__of__minimal_maybe_empty_production in H; [ | reflexivity ]
      | [ H : MaybeEmpty.Minimal.minimal_maybe_empty_productions _ _ |- _ ] => eapply MaybeEmpty.MinimalOfCore.maybe_empty_productions__of__minimal_maybe_empty_productions in H; [ | reflexivity ]
      | [ m : MaybeEmpty.Core.maybe_empty_productions _ _ _ |- _ ]
        => let f := constr:(@MaybeEmpty.OfParse.parse_empty_from_maybe_empty_parse_of_productions _ _ _) in
           eapply f with (str := of_string nil) in m; [ | (assumption || (rewrite ?of_string_length; reflexivity)).. ];
           eapply parse_of_nonterminal_complete; destruct_head sigT;
           first [ assumption
                 | apply rdp_list_initial_nonterminals_correct; assumption ]
      | [ Hvalid : is_true (grammar_rvalid _) |- _ ] => apply grammar_rvalid_correct in Hvalid
      | [ Hvalid : grammar_valid _, Hnt : is_true (is_valid_nonterminal _ _), p : parse_of_item _ _ _ |- _ ]
        => idtac;
          let pf := constr:(fun k => Forall_parse_of_item_valid Hvalid k p) in
          let pf' := constr:(pf Hnt) in
          let T := (type of pf') in
          let T' := (eval simpl in T) in
          unique pose proof (pf' : T')
      | _ => eapply MaybeEmpty.OfParse.parse_empty_maybe_empty_parse_of_item; try eassumption; rewrite ?of_string_length; reflexivity
      | _ => eapply MaybeEmpty.OfParse.parse_empty_maybe_empty_parse_of_production; try eassumption; rewrite ?of_string_length; reflexivity
    end.

  Local Ltac t := repeat first [ t' | left; solve [ t ] | right; solve [ t ] ].

  Local Instance only_last_ccdata
        (predata := @rdp_list_predata _ G)
  : @fold_grammar_correctness_computational_data Ascii.ascii possible_last_terminals G
    := { Pnt valid0 nt pft
         := forall ch : Ascii.ascii,
              sub_nonterminals_listT valid0 initial_nonterminals_data
              -> (List.In ch pft <-> inhabited (OnlyLast.MinimalReachable.minimal_reachable_from_item (G := G) initial_nonterminals_data ch valid0 (NonTerminal nt)))
                 /\ (might_be_empty' pft <-> inhabited (MaybeEmpty.Core.maybe_empty_item G initial_nonterminals_data (NonTerminal nt)));
         Ppat valid0 pat pft
         := forall ch : Ascii.ascii,
              sub_nonterminals_listT valid0 initial_nonterminals_data
              -> (List.In ch pft <-> inhabited (OnlyLast.MinimalReachable.minimal_reachable_from_production (G := G) initial_nonterminals_data ch valid0 pat))
                 /\ (might_be_empty' pft <-> inhabited (MaybeEmpty.Core.maybe_empty_production G initial_nonterminals_data pat));
         Ppats valid0 pats pft
         := forall ch : Ascii.ascii,
              sub_nonterminals_listT valid0 initial_nonterminals_data
              -> (List.In ch pft <-> inhabited (OnlyLast.MinimalReachable.minimal_reachable_from_productions (G := G) initial_nonterminals_data ch valid0 pats))
                 /\ (might_be_empty' pft <-> inhabited (MaybeEmpty.Core.maybe_empty_productions G initial_nonterminals_data pats)) }.

  Local Arguments is_valid_nonterminal : simpl never.
  Local Arguments remove_nonterminal : simpl never.
  Local Arguments initial_nonterminals_data : simpl never.

  Local Opaque enumerable_ascii.

  Local Instance only_last_cdata
        (rdata := rdp_list_rdata' (G := G))
        (cdata := brute_force_cdata G)
  : @fold_grammar_correctness_data Ascii.ascii possible_last_terminals (only_last_fold_data G) G
    := { fgccd := only_last_ccdata }.
  Proof.
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
    { abstract t. }
  Defined.

  Lemma possible_last_terminals_of_correct
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (p : parse_of_item G str (NonTerminal nt))
        (His_valid : is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt))
  : last_char_in str (possible_last_terminals_of G nt).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of.
    generalize (OnlyLast.ReachableParse.for_last_char_reachable_from_parse_of_item (reflexivity _) p).
    setoid_rewrite (OnlyLast.MinimalReachableOfReachable.minimal_reachable_from_item__iff__reachable_from_item (reflexivity _)).
    intro H; specialize (H (Forall_parse_of_item_valid Hvalid' (His_valid : item_valid (NonTerminal nt)) p)); revert H.
    apply for_last_char__impl__last_char_in.
    intro ch.
    apply (fold_nt_correct (FGCD := only_last_cdata) nt); reflexivity.
  Qed.

  Lemma possible_last_terminals_of_empty_correct
        (predata := @rdp_list_predata _ G)
        (str : String) (Hlen : length str = 0) nt
        (p : parse_of_item G str (NonTerminal nt))
        (His_valid : is_valid_nonterminal initial_nonterminals_data (of_nonterminal nt))
  : might_be_empty' (possible_last_terminals_of G nt).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    unfold possible_terminals_of_production.
    apply (fold_nt_correct (FGCD := only_last_cdata) nt).
    { repeat constructor. }
    { reflexivity. }
    { constructor.
      eapply MaybeEmpty.OfParse.parse_empty_maybe_empty_parse_of_item;
        try (eassumption || (apply Forall_parse_of_item_valid; assumption) || reflexivity).
      Grab Existential Variables.
      assumption. }
  Qed.
End only_last_correctness.

Local Open Scope string_like_scope.

Local Arguments string_beq : simpl never.

Section search_forward.
  Lemma terminals_disjoint_search_for_not' {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
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

  Lemma terminals_disjoint_search_for_not {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
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

  Lemma terminals_disjoint_search_for' {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
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

  Lemma terminals_disjoint_search_for {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
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
End search_forward.

Section search_backward.
  Lemma terminals_disjoint_rev_search_for_not' {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of G nt) (possible_terminals_of_production G its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
  : forall_chars__char_in (drop n str) (possible_terminals_of_production G its)
    /\ ((n = 0 /\ might_be_empty' (possible_last_terminals_of G nt))
        \/ (for_last_char
              (take n str)
              (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production G its)))
            /\ n > 0)).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
    pose proof HinV as HinV';
      rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
    apply and_comm; split.
    { destruct (Compare_dec.zerop n); [ left | right ].
      { split; trivial; []; subst.
        eapply possible_last_terminals_of_empty_correct; try eassumption;
          find_production_valid; [].
        rewrite take_length; reflexivity. }
      { split; try omega; [].
        eapply last_char_in__impl__for_last_char;
          [
          | apply possible_last_terminals_of_correct; [ .. | eassumption | ];
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
    { apply (fun x y => possible_terminals_of_production_correct x y pits);
      try assumption;
      find_production_valid. }
  Qed.

  Lemma terminals_disjoint_rev_search_for_not {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of G nt) (possible_terminals_of_production G its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : is_after_last_char_such_that
        (*(might_be_empty' (possible_last_terminals_of G nt))*)
        str
        n
        (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production G its))).
  Proof.
    pose proof (terminals_disjoint_rev_search_for_not' Hvalid _ H_disjoint pit pits H_reachable) as H.
    split;
      [ destruct H as [H0 H1]
      | destruct H as [H0 [[H1 H2] | H1]];
        destruct_head and;
        try solve [ left; eauto
                  | right; eauto
                  | assumption
                  | apply for_last_char_nil; rewrite ?take_length; apply Min.min_case_strong; omega ] ].
    revert H0.
    apply forall_chars__char_in__impl__forall_chars.
    intros ch H' H''.
    apply Bool.negb_true_iff, Bool.not_true_iff_false in H''.
    apply H''; clear H''.
    apply list_in_lb; [ apply (@ascii_lb) | ]; assumption.
  Qed.

  Lemma terminals_disjoint_rev_search_for' {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of G nt) (possible_terminals_of_production G its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : forall_chars (drop n str)
                   (fun ch => negb (list_bin ascii_beq ch (possible_last_terminals_of G nt)))
      /\ ((n = 0 /\ might_be_empty' (possible_last_terminals_of G nt))
          \/ (last_char_in
                (take n str)
                (possible_last_terminals_of G nt)
              /\ n > 0)).
  Proof.
    pose proof Hvalid as Hvalid'; apply grammar_rvalid_correct in Hvalid'.
    destruct H_reachable as [ nt' [ prefix [ HinV HinL ] ] ].
    pose proof HinV as HinV';
      rewrite <- (@initial_nonterminals_correct _ G (@rdp_list_predata _ G) (@rdp_list_rdata' _ G)) in HinV'.
    apply and_comm; split.
    { destruct (Compare_dec.zerop n); [ left | right ].
      { split; trivial; [].
        eapply possible_last_terminals_of_empty_correct; try eassumption;
        find_production_valid; [].
        rewrite take_length; subst; reflexivity. }
      { split; try omega; try assumption; [].
        apply possible_last_terminals_of_correct; try assumption.
        find_production_valid. } }
    { eapply forall_chars__char_in__impl__forall_chars.
      { intros ch H'.
        apply Bool.negb_true_iff, Bool.not_true_iff_false.
        intro H''.
        apply list_in_bl in H''; [ | apply (@ascii_bl) ].
        eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
        apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
        apply H_disjoint.
        apply list_in_lb; [ apply (@ascii_lb) | eassumption ]. }
      { apply possible_terminals_of_production_correct; try assumption.
        find_production_valid. } }
  Qed.

  Lemma terminals_disjoint_rev_search_for {G : pregrammar Ascii.ascii}
        {HSLM : StringLikeMin Ascii.ascii}
        {HSL : StringLike Ascii.ascii}
        {HSI : StringIso Ascii.ascii}
        {HSLP : StringLikeProperties Ascii.ascii}
        {HSIP : StringIsoProperties Ascii.ascii}
        (Hvalid : grammar_rvalid G)
        (str : @String Ascii.ascii HSLM)
        {nt its}
        (H_disjoint : disjoint ascii_beq (possible_last_terminals_of G nt) (possible_terminals_of_production G its))
        {n}
        (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
        (pits : parse_of_production G (StringLike.drop n str) its)
        (H_reachable : production_is_reachable G (NonTerminal nt :: its))
    : is_after_last_char_such_that
        (*(might_be_empty' (possible_last_terminals_of G nt))*)
        str
        n
        (fun ch => list_bin ascii_beq ch (possible_last_terminals_of G nt)).
  Proof.
    pose proof (terminals_disjoint_rev_search_for' Hvalid _ H_disjoint pit pits H_reachable) as H.
    split;
      [ destruct H as [H0 H1]
      | destruct H as [H0 [[H1 H2] | [H1 ?]]];
        try solve [ right; eauto
                  | left; split; eauto
                  | assumption
                  | apply for_last_char_nil; rewrite ?take_length; apply Min.min_case_strong; omega ] ].
    { revert H0.
      apply forall_chars_Proper; [ reflexivity | ].
      intros ch H' H''.
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H'.
      apply H'.
      assumption. }
    { revert H1.
      apply last_char_in__impl__for_last_char.
      intros ch H'.
      apply list_in_lb; [ apply (@ascii_lb) | ]; assumption. }
  Qed.
End search_backward.
