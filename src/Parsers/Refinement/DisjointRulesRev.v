(** Refinement rules for disjoint rules *)
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.Refinement.DisjointRulesCommon.
Require Import Fiat.Parsers.ParserInterface.
Export DisjointLemmas.Exports.

Set Implicit Arguments.

Local Arguments minus !_ !_.

Lemma find_after_last_char_such_that'_short {Char HSLM HSL}
      str P len
  : @find_after_last_char_such_that' Char HSLM HSL P len str <= len.
Proof.
  revert str; induction len; simpl; intros; [ omega | ].
  destruct (get len str) eqn:H.
  { edestruct P; try omega.
    rewrite IHlen; omega. }
  { rewrite IHlen; omega. }
Qed.

Lemma find_after_last_char_such_that_short {Char HSLM HSL}
      str P
  : @find_after_last_char_such_that Char HSLM HSL str P <= length str.
Proof.
  apply find_after_last_char_such_that'_short.
Qed.

Lemma refine_find_after_last_char_such_that {Char} {HSLM : StringLikeMin Char} {HSL : StringLike Char} {HSLP : StringLikeProperties Char}
      (str : String)
      (P : Char -> bool)
  : refine { n : nat | n <= length str
                       /\ ((exists n', is_after_last_char_such_that str n' P)
                           -> is_after_last_char_such_that str n P) }
           (ret (find_after_last_char_such_that str P)).
Proof.
  intros v H.
  computes_to_inv; subst.
  apply PickComputes.
  split; [ apply find_after_last_char_such_that_short | ].
  apply is_after_last_char_such_that__find_after_last_char_such_that.
Qed.

Section with_grammar.
  Context {HSLM : StringLikeMin Ascii.ascii}
          {HSL : StringLike Ascii.ascii}
          {HSI : StringIso Ascii.ascii}
          {HSLP : StringLikeProperties Ascii.ascii}
          {HSIP : StringIsoProperties Ascii.ascii}
          {G : pregrammar' Ascii.ascii}
          (Hvalid : grammar_rvalid G)
          (search_data : disjoint_search_data G).

  Local Notation possible_terminals_of := (possible_terminals_of G compiled_productions_possible_terminals).
  Local Notation possible_first_terminals_of_production :=
    (possible_first_terminals_of_production G compiled_productions_maybe_empty_of compiled_productions_possible_first_terminals).
  Local Notation possible_terminals_of_production :=
    (possible_terminals_of_production G compiled_productions_possible_terminals).
  Local Notation possible_last_terminals_of :=
    (possible_last_terminals_of G compiled_productions_maybe_empty_of compiled_productions_possible_last_terminals).

  Definition rev_search_for_condition
             str nt (n : nat)
    := is_after_last_char_such_that
         (*(might_be_empty (possible_first_terminals_of_production G its))*)
         str
         n
         (fun ch => list_bin ascii_beq ch (possible_last_terminals_of nt)).

  Lemma refine_disjoint_rev_search_for'
        {str offset len nt its}
        (H_disjoint : disjoint ascii_beq
                               (possible_last_terminals_of nt)
                               (possible_terminals_of_production its))
    : refine {splits : list nat
             | split_list_is_complete
                 G str offset len
                 (NonTerminal nt::its) splits}
             (n <- { n : nat | n <= length (substring offset len str)
                               /\ ((exists n', rev_search_for_condition (substring offset len str) nt n')
                                   -> rev_search_for_condition (substring offset len str) nt n) };
                ret [n]).
  Proof.
    intros ls H.
    computes_to_inv; subst.
    destruct H as [H0 H1].
    apply PickComputes.
    hnf; cbv zeta.
    intros Hlen it' its' Heq n ? H_reachable pit pits.
    inversion Heq; subst it' its'; clear Heq.
    left.
    pose proof (terminals_disjoint_rev_search_for _ Hvalid _ H_disjoint pit pits H_reachable) as H'.
    specialize (H1 (ex_intro _ n H')).
    unfold rev_search_for_condition in H1.
    pose proof (is_after_last_char_such_that_eq_nat_iff H1 H') as H''.
    destruct_head or; destruct_head and; subst;
      rewrite ?Min.min_r, ?Min.min_l by assumption;
      omega.
  Qed.

  Definition rev_search_for_not_condition
             str its n
    := is_after_last_char_such_that
         (*(might_be_empty (possible_first_terminals_of_production G its))*)
         str
         n
         (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production its))).

  Lemma refine_disjoint_rev_search_for_not'
        {str offset len nt its}
        (H_disjoint : disjoint ascii_beq
                               (possible_last_terminals_of nt)
                               (possible_terminals_of_production its))
    : refine {splits : list nat
             | split_list_is_complete
                 G str offset len
                 (NonTerminal nt::its)
                 splits}
             (n <- { n : nat | n <= length (substring offset len str)
                               /\ ((exists n', rev_search_for_not_condition (substring offset len str) its n')
                                   -> rev_search_for_not_condition (substring offset len str) its n) };
                ret [n]).
  Proof.
    intros ls H.
    computes_to_inv; subst.
    destruct H as [H0 H1].
    apply PickComputes.
    hnf; cbv zeta.
    intros Hlen it' its' Heq n ? H_reachable pit pits.
    inversion Heq; subst it' its'; clear Heq.
    left.
    pose proof (terminals_disjoint_rev_search_for_not _ Hvalid _ H_disjoint pit pits H_reachable) as H'.
    specialize (H1 (ex_intro _ n H')).
    pose proof (is_after_last_char_such_that_eq_nat_iff H1 H') as H''.
    destruct_head or; destruct_head and; subst;
      rewrite ?Min.min_r by assumption;
      omega.
  Qed.

  Lemma refine_disjoint_rev_search_for
        {str offset len nt its}
        (H_disjoint : disjoint ascii_beq
                               (possible_last_terminals_of nt)
                               (possible_terminals_of_production its))
    : refine {splits : list nat
             | split_list_is_complete
                 G str offset len
                 (NonTerminal nt::its)
                 splits}
             (ret [find_after_last_char_such_that (substring offset len str) (fun ch => list_bin ascii_beq ch (possible_last_terminals_of nt))]).
  Proof.
    rewrite refine_disjoint_rev_search_for' by assumption.
    setoid_rewrite refine_find_after_last_char_such_that.
    simplify with monad laws; reflexivity.
  Qed.

  Lemma refine_disjoint_rev_search_for_not
        {str offset len nt its}
        (H_disjoint : disjoint ascii_beq
                               (possible_last_terminals_of nt)
                               (possible_terminals_of_production its))
    : refine {splits : list nat
             | split_list_is_complete
                 G str offset len
                 (NonTerminal nt::its)
                 splits}
             (ret [find_after_last_char_such_that (substring offset len str) (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production its)))]).
  Proof.
    rewrite refine_disjoint_rev_search_for_not' by assumption.
    setoid_rewrite refine_find_after_last_char_such_that.
    simplify with monad laws; reflexivity.
  Qed.

  Lemma refine_disjoint_rev_search_for_idx
        {str offset len nt its idx}
        (Heq : default_to_production (G := G) idx = NonTerminal nt :: its)
        (H_disjoint : disjoint ascii_beq
                               (possible_last_terminals_of nt)
                               (possible_terminals_of_production its))
    : refine {splits : list nat
             | split_list_is_complete_idx
                 G str offset len
                 idx
                 splits}
             (ret [find_after_last_char_such_that (substring offset len str) (fun ch => list_bin ascii_beq ch (possible_last_terminals_of nt))]).
  Proof.
    unfold split_list_is_complete_idx.
    erewrite <- refine_disjoint_rev_search_for by eassumption.
    rewrite Heq.
    apply refine_pick_pick; intro; trivial.
  Qed.

  Lemma refine_disjoint_rev_search_for_not_idx
        {str offset len nt its idx}
        (Heq : default_to_production (G := G) idx = NonTerminal nt :: its)
        (H_disjoint : disjoint ascii_beq
                               (possible_last_terminals_of nt)
                               (possible_terminals_of_production its))
    : refine {splits : list nat
             | split_list_is_complete_idx
                 G str offset len
                 idx
                 splits}
             (ret [find_after_last_char_such_that (substring offset len str) (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production its)))]).
  Proof.
    unfold split_list_is_complete_idx.
    erewrite <- refine_disjoint_rev_search_for_not by eassumption.
    rewrite Heq.
    apply refine_pick_pick; intro; trivial.
  Qed.
End with_grammar.

Ltac solve_disjoint_side_conditions :=
  idtac;
  lazymatch goal with
  | [ |- Carriers.default_to_production (G := ?G) ?k = ?e ]
    => try cbv delta [G];
       cbv beta iota zeta delta [Carriers.default_to_production Lookup_idx fst snd List.map pregrammar_productions List.length List.nth minus Operations.List.drop];
       try reflexivity
  | [ |- is_true (Operations.List.disjoint _ _ _) ]
    => vm_compute; try reflexivity
  end.

Ltac pose_disjoint_rev_search_for lem :=
  idtac;
  let G := match goal with |- context[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] => G end in
  let HSLM := match goal with |- context[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSLM end in
  let HSL := match goal with |- context[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSL end in
  let H' := get_hyp_of_shape (is_true (grammar_rvalid G)) in
  let search_data := get_hyp_of_shape (disjoint_search_data G) in
  let lem' := constr:(@refine_disjoint_rev_search_for_idx HSLM HSL _ G H' search_data) in
  let lem' := match goal with
              | [ |- context[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
                => constr:(fun idx' nt its => lem' str offset len nt its idx')
              end in
  pose proof lem' as lem.
Ltac replace_with_native_compute_in c H :=
  let c' := (eval native_compute in c) in
  (* By constrast [set ... in ...] seems faster than [change .. with ... in ...] in 8.4?! *)
  replace c with c' in H by (clear; native_cast_no_check (eq_refl c')).

Ltac rewrite_once_disjoint_rev_search_for_specialize alt_side_condition_tac lem lem' :=
  idtac;
  let G := (lazymatch goal with
             | [ |- context[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
               => G
             end) in
  match goal with
  | [ |- context[ParserInterface.split_list_is_complete_idx G ?str ?offset ?len ?idx] ]
    => pose proof (lem idx) as lem';
       do 2 (lazymatch type of lem' with
              | forall a : ?T, _ => idtac; let x := fresh in evar (x : T); specialize (lem' x); subst x
              end);
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve [ solve_disjoint_side_conditions | alt_side_condition_tac () ];
       specialize (lem' H'); clear H';
       let x := match type of lem' with
                | context[DisjointLemmas.actual_possible_last_terminals ?ls]
                  => constr:(DisjointLemmas.actual_possible_last_terminals ls)
                end in
       replace_with_vm_compute_in x lem';
       unfold Equality.list_bin in lem';
       change (orb false) with (fun bv : bool => bv) in lem';
       cbv beta in lem';
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve [ solve_disjoint_side_conditions | alt_side_condition_tac () ];
       specialize (lem' H'); clear H'
  end.
Ltac rewrite_once_disjoint_rev_search_for alt_side_condition_tac lem :=
  let lem' := fresh "lem'" in
  rewrite_once_disjoint_rev_search_for_specialize alt_side_condition_tac lem lem';
  setoid_rewrite lem'; clear lem'.
Ltac rewrite_disjoint_rev_search_for_no_clear alt_side_condition_tac lem :=
  pose_disjoint_rev_search_for lem;
  progress repeat rewrite_once_disjoint_rev_search_for alt_side_condition_tac lem.
Ltac rewrite_disjoint_rev_search_for_with_alt alt_side_condition_tac :=
  idtac;
  let lem := fresh "lem" in
  rewrite_disjoint_rev_search_for_no_clear alt_side_condition_tac lem;
  clear lem.
Ltac rewrite_disjoint_rev_search_for_leaving_side_conditions :=
  unshelve rewrite_disjoint_rev_search_for_with_alt ltac:(fun _ => shelve).
Ltac rewrite_disjoint_rev_search_for :=
  rewrite_disjoint_rev_search_for_with_alt ltac:(fun _ => fail).
Ltac refine_disjoint_rev_search_for_with_alt alt_side_condition_tac :=
  idtac;
  let lem := fresh "lem" in
  pose_disjoint_rev_search_for lem;
  let lem' := fresh "lem'" in
  rewrite_once_disjoint_rev_search_for_specialize alt_side_condition_tac lem lem';
  refine lem'; clear lem'.
Ltac refine_disjoint_rev_search_for_leaving_side_conditions :=
  unshelve refine_disjoint_rev_search_for_with_alt ltac:(fun _ => shelve).
Ltac refine_disjoint_rev_search_for :=
  refine_disjoint_rev_search_for_with_alt ltac:(fun _ => fail).
