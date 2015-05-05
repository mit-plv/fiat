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
Require Import Fiat.Parsers.StringLike.FirstChar.
Require Import Fiat.Parsers.StringLike.Properties.
Require Import Fiat.Parsers.MinimalParseOfParse.
Require Import Fiat.Parsers.ContextFreeGrammarProperties.
Require Import Fiat.Parsers.FoldGrammar.
Require Import Fiat.Parsers.BaseTypesLemmas.
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

Section all_possible.
  Context {Char : Type}.
  Definition possible_terminals := list Char.

  Local Instance all_possible_fold_data : fold_grammar_data Char possible_terminals
    := { on_terminal ch := [ch];
         on_redundant_nonterminal nt := nil;
         on_nil_production := nil;
         combine_production := @app _;
         on_nil_productions := nil;
         combine_productions := @app _ }.

  Definition possible_terminals_of : grammar Char -> String.string -> possible_terminals
    := @fold_nt _ _ all_possible_fold_data.
  Definition possible_terminals_of_productions : grammar Char -> productions Char -> possible_terminals
    := @fold_productions _ _ all_possible_fold_data.
  Definition possible_terminals_of_production : grammar Char -> production Char -> possible_terminals
    := @fold_production _ _ all_possible_fold_data.
End all_possible.

Section only_first.
  Context (G : grammar Ascii.ascii).

  Record possible_first_terminals :=
    { actual_possible_first_terminals :> list Ascii.ascii;
      might_be_empty : bool }.

  Local Instance only_first_fold_data : fold_grammar_data Ascii.ascii possible_first_terminals
    := { on_terminal ch := {| actual_possible_first_terminals := [ch] ; might_be_empty := false |};
         on_redundant_nonterminal nt := {| actual_possible_first_terminals := nil ; might_be_empty := brute_force_parse_nonterminal G ""%string nt |};
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
        (predata := @rdp_list_predata _ G)
        (str : String) nt
        (p : parse_of_item G str (NonTerminal nt))
        (Hp : Forall_parse_of_item (fun _ nt' => is_valid_nonterminal initial_nonterminals_data nt') p)
  : forall_chars__char_in str (possible_terminals_of G nt).
  Proof.
    unfold possible_terminals_of.
    generalize (All.ReachableParse.forall_chars_reachable_from_parse_of_item _ Hp).
    setoid_rewrite All.MinimalReachableOfReachable.minimal_reachable_from_item__iff__reachable_from_item.
    apply forall_chars__impl__forall_chars__char_in.
    intro ch.
    apply (fold_nt_correct (G := G) nt ch).
  Qed.
End all_possible_correctness.

Section only_first_correctness.
  Context (G : grammar Ascii.ascii).
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
      (*| [ |- OnlyFirst.MinimalReachable.minimal_reachable_from_item _ _ _ (NonTerminal _) ] => constructor*)
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
        => eapply MaybeEmpty.OfParse.parse_empty_from_maybe_empty_parse_of_productions with (str := ""%string) in m; [ | reflexivity.. ];
           eapply parse_nonterminal_complete; [ eassumption.. | ];
           split; [ eassumption | exact (projT2 m) ]
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
    { t.
      admit. }
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
        (Hp : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal initial_nonterminals_data nt') p)
  : first_char_in str (possible_first_terminals_of_production G pat).
  Proof.
    unfold possible_terminals_of_production.
    generalize (OnlyFirst.ReachableParse.for_first_char_reachable_from_parse_of_production _ Hp).
    setoid_rewrite OnlyFirst.MinimalReachableOfReachable.minimal_reachable_from_production__iff__reachable_from_production.
    apply for_first_char__impl__first_char_in.
    intro ch.
    apply (fold_production_correct (FGCD := only_first_cdata) pat); reflexivity.
  Qed.

  Lemma possible_first_terminals_of_production_empty_correct
        (predata := @rdp_list_predata _ G)
        (str : String) (Hlen : length str = 0) pat
        (p : parse_of_production G str pat)
        (Hp : Forall_parse_of_production (fun _ nt' => is_valid_nonterminal initial_nonterminals_data nt') p)
  : might_be_empty (possible_first_terminals_of_production G pat).
  Proof.
    unfold possible_terminals_of_production.
    apply (fold_production_correct (FGCD := only_first_cdata) pat).
    { repeat constructor. }
    { reflexivity. }
    { constructor.
      eapply MaybeEmpty.OfParse.parse_empty_maybe_empty_parse_of_production;
        eassumption. }
  Qed.
End only_first_correctness.

Local Open Scope string_like_scope.

Local Arguments string_beq : simpl never.

Definition is_first_char_such_that {Char} {HSL : StringLike Char}
           (might_be_empty : Prop)
           (str : @String Char HSL)
           (n : nat)
           P
  := forall_chars (take n str) (fun ch => ~P ch)
     /\ ((for_first_char (drop n str) P /\ n < length str)
         \/ (might_be_empty /\ length str <= n)).

Lemma is_first_char_such_that_drop {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
      (might_be_empty : Prop)
      (str : @String Char HSL)
      (n : nat)
      P
: is_first_char_such_that might_be_empty str (S n) P
  <-> (is_first_char_such_that might_be_empty (drop 1 str) n P /\ for_first_char str (fun ch => ~P ch)).
Proof.
  generalize dependent str; induction n; intros.
  { unfold is_first_char_such_that.
    repeat match goal with
             | _ => assumption
             | _ => intro
             | [ H : and _ _ |- _ ] => destruct H
             | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
             | [ H : _ |- _ ] => rewrite drop_0 in H
             | [ H : _ |- _ ] => apply forall_chars__impl__for_first_char in H
             | [ H : for_first_char (take (S _) _) _ |- _ ] => apply for_first_char__take in H
             | [ H : for_first_char ?str ?P, H' : for_first_char ?str ?P' |- _ ]
               => destruct (fun H0 => for_first_char_combine (T := False) H0 H H'); [ tauto | clear H H' | tauto ]
             | [ H : ?x = 0 |- context[?x] ] => rewrite H
             | _ => rewrite take_length
             | _ => rewrite drop_length
             | _ => rewrite drop_drop
             | _ => apply forall_chars_nil; [ (rewrite ?take_length, ?drop_length; reflexivity).. ]
             | _ => omega
             | _ => progress destruct_head and
             | _ => progress destruct_head or
             | [ |- _ /\ _ ] => split
             | [ |- _ <-> _ ] => split
             | _ => left; repeat split; trivial; omega
             | _ => right; repeat split; trivial; omega
             | _ => apply for_first_char__for_first_char__iff_short;
                   [ rewrite take_length; destruct (length str); simpl in *; omega
                   | apply -> (for_first_char__take 0); assumption ]
           end. }
  { unfold is_first_char_such_that in *.
    rewrite (forall_chars__split _ _ 1); rewrite !drop_drop, !drop_take, !take_take; simpl.
    repeat match goal with
             | _ => assumption
             | _ => intro
             | [ H : and _ _ |- _ ] => destruct H
             | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
             | [ H : _ |- _ ] => rewrite drop_0 in H
             | [ H : _ |- _ ] => apply forall_chars__impl__for_first_char in H
             | [ H : for_first_char (take (S _) _) _ |- _ ] => apply for_first_char__take in H
             | [ H : for_first_char ?str ?P, H' : for_first_char ?str ?P' |- _ ]
               => destruct (fun H0 => for_first_char_combine (T := False) H0 H H'); [ tauto | clear H H' | tauto ]
             | [ H : ?x = 0 |- context[?x] ] => rewrite H
             | _ => rewrite take_length
             | _ => rewrite drop_length
             | _ => rewrite drop_drop
             | _ => apply forall_chars_nil; [ (rewrite ?take_length, ?drop_length; reflexivity).. ]
             | _ => omega
             | _ => progress destruct_head and
             | _ => progress destruct_head or
             | [ |- _ /\ _ ] => split
             | [ |- _ <-> _ ] => split
             | _ => left; repeat split; trivial; omega
             | _ => right; repeat split; trivial; omega
             | _ => apply for_first_char__for_first_char__iff_short;
                   [ rewrite take_length; destruct (length str); simpl in *; omega
                   | apply -> (for_first_char__take 0); assumption ]
           end.
    { apply IHn.
     ].

    apply for_first_

Lemma is_first_char_such_that_eq_nat_iff {Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
      (might_be_empty : Prop)
      (str : @String Char HSL)
      (n n' : nat)
      P
      (H0 : is_first_char_such_that might_be_empty str n P)
      (H1 : is_first_char_such_that might_be_empty str n' P)
: n = n' \/ (n >= length str /\ n' >= length str /\ might_be_empty).
Proof.
  generalize dependent n'; generalize dependent str; induction n; intros.
  { destruct n'; intros.
    { left; reflexivity. }
    { right.
      unfold is_first_char_such_that in *.
      repeat match goal with
               | _ => assumption
               | [ H : and _ _ |- _ ] => destruct H
               | [ H : ?A -> ?B, H' : ?A |- _ ] => specialize (H H')
               | [ H : _ |- _ ] => rewrite drop_0 in H
               | [ H : _ |- _ ] => apply forall_chars__impl__for_first_char in H
               | [ H : for_first_char (take (S _) _) _ |- _ ] => apply for_first_char__take in H
               | [ H : for_first_char ?str ?P, H' : for_first_char ?str ?P' |- _ ]
                 => destruct (fun H0 => for_first_char_combine (T := False) H0 H H'); [ tauto | clear H H' | tauto ]
               | [ H : ?x = 0 |- context[?x] ] => rewrite H
               | _ => omega
               | _ => progress destruct_head and
               | _ => progress destruct_head or
               | [ |- _ /\ _ ] => split
             end. } }
  { destruct n'.
    { right.
      case_eq (length str).
      {
generalize dependent str.
      ; destruct_head and; try solve [ repeat split; eauto; omega ].
Focus 2.
lazymatch goal with
end.
tauto.

Lemma forall_chars__to__for_first_char str

      rewrite drop_0 in .

      destruct_head and.
      rewrite drop_0 in *.
      rewrite !drop_drop in IHn'; simpl in *.
      rewrite !take_drop in IHn'; simpl in *.
      rewrite !drop_length in IHn'; simpl in *.
      destruct_head or; repeat split; try omega; eauto.
      Focus 3.
  destruct H0 as [H0' [H0''|[H0'' H0''']]], H1 as [H1' [H1''|[H1'' H1''']]].

Lemma terminals_disjoint_search_for_not' {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: forall_chars__char_in (take n str) (possible_terminals_of G nt)
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (for_first_char
            (drop n str)
            (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of G nt))))).
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
      eapply possible_first_terminals_of_production_empty_correct; try eassumption.
      eapply expand_forall_parse_of_production;
        [
        | rewrite parse_of_production_respectful_refl; eassumption ].
      intros; simpl in *.
      apply list_in_lb; try apply @string_lb; []; eassumption. }
    { erewrite <- parse_of_production_respectful_refl in Hpits.
      eapply expand_forall_parse_of_production in Hpits;
        [ rewrite parse_of_production_respectful_refl in Hpits;
          apply possible_first_terminals_of_production_correct in Hpits
        | intros ?????; apply list_in_lb; apply @string_lb ].
      revert Hpits.
      apply first_char_in__impl__for_first_char.
      intros ch H'.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H''.
      apply list_in_bl in H''; [ | apply (@ascii_bl) ].
      eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
      apply H_disjoint.
      apply list_in_lb; [ apply (@ascii_lb) | assumption ]. } }
  { eapply possible_terminals_of_correct.
    eapply expand_forall_parse_of_item;
      [
      | reflexivity
      | reflexivity
      | rewrite parse_of_item_respectful_refl; eassumption ].
    intros ?????; apply list_in_lb; apply @string_lb.
    Grab Existential Variables.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity. }
Qed.

Lemma terminals_disjoint_search_for_not {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: is_first_char_such_that
    (might_be_empty (possible_first_terminals_of_production G its))
    str
    n
    (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of G nt))).
Proof.
  unfold is_first_char_such_that.
  pose proof (terminals_disjoint_search_for_not' _ H_disjoint _ _ H_reachable Hpit Hpits) as H.
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

Lemma terminals_disjoint_search_for' {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: forall_chars (take n str)
               (fun ch => negb (list_bin ascii_beq ch (possible_first_terminals_of_production G its)))
  /\ ((length str <= n /\ might_be_empty (possible_first_terminals_of_production G its))
      \/ (first_char_in
            (drop n str)
            (possible_first_terminals_of_production G its))).
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
      eapply possible_first_terminals_of_production_empty_correct; try eassumption.
      eapply expand_forall_parse_of_production;
        [
        | rewrite parse_of_production_respectful_refl; eassumption ].
      intros; simpl in *.
      apply list_in_lb; try apply @string_lb; []; eassumption. }
    { erewrite <- parse_of_production_respectful_refl in Hpits.
      eapply expand_forall_parse_of_production in Hpits;
        [ rewrite parse_of_production_respectful_refl in Hpits;
          apply possible_first_terminals_of_production_correct in Hpits
        | intros ?????; apply list_in_lb; apply @string_lb ].
      assumption. } }
  { erewrite <- parse_of_item_respectful_refl in Hpit.
    eapply expand_forall_parse_of_item in Hpit;
      [ rewrite parse_of_item_respectful_refl in Hpit;
        apply possible_terminals_of_correct in Hpit
      | intros ?????; apply list_in_lb; apply @string_lb
      | reflexivity
      | reflexivity ].
      revert Hpit.
      apply forall_chars__char_in__impl__forall_chars.
      intros ch H'.
      apply Bool.negb_true_iff, Bool.not_true_iff_false.
      intro H''.
      apply list_in_bl in H''; [ | apply (@ascii_bl) ].
      eapply fold_right_andb_map_in in H_disjoint; [ | eassumption ].
      apply Bool.negb_true_iff, Bool.not_true_iff_false in H_disjoint.
      apply H_disjoint.
      apply list_in_lb; [ apply (@ascii_lb) | assumption ]. }
  Grab Existential Variables.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
  reflexivity.
Qed.

Lemma terminals_disjoint_search_for {G : grammar Ascii.ascii} (str : @String Ascii.ascii string_stringlike)
      {nt its}
      (H_disjoint : disjoint ascii_beq (possible_terminals_of G nt) (possible_first_terminals_of_production G its))
      {n}
      (pit : parse_of_item G (StringLike.take n str) (NonTerminal nt))
      (pits : parse_of_production G (StringLike.drop n str) its)
      (H_reachable : production_is_reachable G (NonTerminal nt :: its))
      (Hpit : Forall_parse_of_item (fun _ nt => List.In nt (Valid_nonterminals G)) pit)
      (Hpits : Forall_parse_of_production (fun _ nt => List.In nt (Valid_nonterminals G)) pits)
: is_first_char_such_that
    (might_be_empty (possible_first_terminals_of_production G its))
    str
    n
    (fun ch => list_bin ascii_beq ch (possible_first_terminals_of_production G its)).
Proof.
  unfold is_first_char_such_that.
  pose proof (terminals_disjoint_search_for' _ H_disjoint _ _ H_reachable Hpit Hpits) as H.
  split;
    [ destruct H as [H0 H1]
    | destruct H as [H0 [[H1 H2] | H1]]; [ right | left ]; eauto ].
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
