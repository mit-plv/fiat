(** Refinement rules for disjoint rules *)
Require Import Coq.omega.Omega.
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.Refinement.DisjointRulesCommon.
Require Import Fiat.Parsers.Refinement.PossibleTerminalsSets.
Require Import Fiat.Parsers.ParserInterface.
Require Import Fiat.Common.List.DisjointFacts.
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
          (pdata : possible_data G).

  Local Notation possible_terminals_of nt
    := (@all_possible_ascii_of_nt G pdata nt).
  Local Notation possible_terminals_of_production its
    := (@all_possible_ascii_of_production G pdata its).
  Local Notation possible_first_terminals_of_production its
    := (@possible_first_ascii_of_production G pdata its).
  Local Notation possible_last_terminals_of nt
    := (@possible_last_ascii_of_nt G pdata nt).

  Definition rev_search_for_condition
             str nt (n : nat)
    := is_after_last_char_such_that
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
    pose proof (terminals_disjoint_rev_search_for _ _ H_disjoint pit pits H_reachable) as H'.
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
    pose proof (terminals_disjoint_rev_search_for_not _ _ H_disjoint pit pits H_reachable) as H'.
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
    => cbv -[Equality.ascii_beq orb andb BinNat.N.leb Reflective.opt.N_of_ascii];
       try reflexivity
  | [ |- is_true (Operations.List.disjoint _ _ _) ]
    => vm_compute; try reflexivity
  end.

Ltac pose_disjoint_rev_search_for lem :=
  idtac;
  lazymatch goal with
  | [ HSLP : @StringLikeProperties _ ?HSLM ?HSL, pdata : possible_data ?G
      |- context[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL ?str ?offset ?len ?idx] ]
    => pose proof (fun idx' nt its => @refine_disjoint_rev_search_for_idx HSLM HSL HSLP G pdata str offset len nt its idx') as lem
  end.
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
       cbv beta delta [id
                         all_possible_ascii_of_nt all_possible_ascii_of_production
                         possible_first_ascii_of_nt possible_first_ascii_of_production
                         possible_last_ascii_of_nt possible_last_ascii_of_production] in lem';
       do 2 (let x := match type of lem' with
                      | context[characters_set_to_ascii_list ?ls]
                        => constr:(characters_set_to_ascii_list ls)
                      end in
             replace_with_vm_compute_in x lem');
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
Ltac leave_side_conditions _ :=
  try rewrite disjoint_uniquize by auto using Equality.ascii_bl, Equality.ascii_lb;
  shelve.
Ltac rewrite_disjoint_rev_search_for_leaving_side_conditions :=
  unshelve rewrite_disjoint_rev_search_for_with_alt leave_side_conditions.
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
  unshelve refine_disjoint_rev_search_for_with_alt leave_side_conditions.
Ltac refine_disjoint_rev_search_for :=
  refine_disjoint_rev_search_for_with_alt ltac:(fun _ => fail).
