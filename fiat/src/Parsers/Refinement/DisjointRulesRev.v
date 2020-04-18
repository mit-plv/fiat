(** Refinement rules for disjoint rules *)
Require Import Fiat.Parsers.Refinement.PreTactics.
Require Import Fiat.Computation.Refinements.General.
Require Import Fiat.Parsers.StringLike.LastCharSuchThat.
Require Import Fiat.Common.Equality.
Require Import Fiat.Common.List.Operations.
Require Import Fiat.Parsers.ContextFreeGrammar.ValidReflective.
Require Import Fiat.Parsers.Refinement.DisjointLemmas.
Require Import Fiat.Parsers.ParserInterface.

Set Implicit Arguments.

Local Arguments minus !_ !_.

Definition rev_search_for_condition
           {HSLM : StringLikeMin Ascii.ascii}
           {HSL : StringLike Ascii.ascii}
           {HSI : StringIso Ascii.ascii}
           (G : pregrammar' Ascii.ascii)
           str nt (n : nat)
  := is_after_last_char_such_that
       (*(might_be_empty (possible_first_terminals_of_production G its))*)
       str
       n
       (fun ch => list_bin ascii_beq ch (possible_last_terminals_of G nt)).

Lemma refine_disjoint_rev_search_for'
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      (G : pregrammar' Ascii.ascii)
      (Hvalid : grammar_rvalid G)
      {str offset len nt its}
      (H_disjoint : disjoint ascii_beq
                             (possible_last_terminals_of G nt)
                             (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its) splits}
         (n <- { n : nat | n <= length (substring offset len str)
                           /\ ((exists n', rev_search_for_condition G (substring offset len str) nt n')
                               -> rev_search_for_condition G (substring offset len str) nt n) };
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
  pose proof (terminals_disjoint_rev_search_for Hvalid _ H_disjoint pit pits H_reachable) as H'.
  specialize (H1 (ex_intro _ n H')).
  unfold rev_search_for_condition in H1.
  pose proof (is_after_last_char_such_that_eq_nat_iff H1 H') as H''.
  destruct_head or; destruct_head and; subst;
  rewrite ?Min.min_r, ?Min.min_l by assumption;
  omega.
Qed.

Definition rev_search_for_not_condition
           {HSLM : StringLikeMin Ascii.ascii}
           {HSL : StringLike Ascii.ascii}
           {HSI : StringIso Ascii.ascii}
           (G : pregrammar' Ascii.ascii)
           str its n
  := is_after_last_char_such_that
       (*(might_be_empty (possible_first_terminals_of_production G its))*)
       str
       n
       (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production G its))).

Lemma refine_disjoint_rev_search_for_not'
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      (Hvalid : grammar_rvalid G)
      {str offset len nt its}
      (H_disjoint : disjoint ascii_beq
                             (possible_last_terminals_of G nt)
                             (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its)
             splits}
         (n <- { n : nat | n <= length (substring offset len str)
                           /\ ((exists n', rev_search_for_not_condition G (substring offset len str) its n')
                               -> rev_search_for_not_condition G (substring offset len str) its n) };
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
  pose proof (terminals_disjoint_rev_search_for_not Hvalid _ H_disjoint pit pits H_reachable) as H'.
  specialize (H1 (ex_intro _ n H')).
  pose proof (is_after_last_char_such_that_eq_nat_iff H1 H') as H''.
  destruct_head or; destruct_head and; subst;
  rewrite ?Min.min_r by assumption;
  omega.
Qed.

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

Lemma refine_disjoint_rev_search_for
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {str offset len nt its}
      (Hvalid : grammar_rvalid G)
      (H_disjoint : disjoint ascii_beq
                             (possible_last_terminals_of G nt)
                             (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its)
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => list_bin ascii_beq ch (possible_last_terminals_of G nt))]).
Proof.
  rewrite refine_disjoint_rev_search_for' by assumption.
  setoid_rewrite refine_find_after_last_char_such_that.
  simplify with monad laws; reflexivity.
Qed.

Lemma refine_disjoint_rev_search_for_not
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {str offset len nt its}
      (Hvalid : grammar_rvalid G)
      (H_disjoint : disjoint ascii_beq
                             (possible_last_terminals_of G nt)
                             (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete
             G str offset len
             (NonTerminal nt::its)
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production G its)))]).
Proof.
  rewrite refine_disjoint_rev_search_for_not' by assumption.
  setoid_rewrite refine_find_after_last_char_such_that.
  simplify with monad laws; reflexivity.
Qed.

Lemma refine_disjoint_rev_search_for_idx
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {str offset len nt its idx}
      (Hvalid : grammar_rvalid G)
      (Heq : default_to_production (G := G) idx = NonTerminal nt :: its)
      (H_disjoint : disjoint ascii_beq
                             (possible_last_terminals_of G nt)
                             (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete_idx
             G str offset len
             idx
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => list_bin ascii_beq ch (possible_last_terminals_of G nt))]).
Proof.
  unfold split_list_is_complete_idx.
  erewrite <- refine_disjoint_rev_search_for by eassumption.
  rewrite Heq.
  apply refine_pick_pick; intro; trivial.
Qed.

Lemma refine_disjoint_rev_search_for_not_idx
      {HSLM : StringLikeMin Ascii.ascii}
      {HSL : StringLike Ascii.ascii}
      {HSI : StringIso Ascii.ascii}
      {HSLP : StringLikeProperties Ascii.ascii}
      {HSIP : StringIsoProperties Ascii.ascii}
      {G : pregrammar' Ascii.ascii}
      {str offset len nt its idx}
      (Hvalid : grammar_rvalid G)
      (Heq : default_to_production (G := G) idx = NonTerminal nt :: its)
      (H_disjoint : disjoint ascii_beq
                             (possible_last_terminals_of G nt)
                             (possible_terminals_of_production G its))
: refine {splits : list nat
         | split_list_is_complete_idx
             G str offset len
             idx
             splits}
         (ret [find_after_last_char_such_that (substring offset len str) (fun ch => negb (list_bin ascii_beq ch (possible_terminals_of_production G its)))]).
Proof.
  unfold split_list_is_complete_idx.
  erewrite <- refine_disjoint_rev_search_for_not by eassumption.
  rewrite Heq.
  apply refine_pick_pick; intro; trivial.
Qed.

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
  let G := match goal with |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] => G end in
  let HSLM := match goal with |- appcontext[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSLM end in
  let HSL := match goal with |- appcontext[@ParserInterface.split_list_is_complete_idx ?Char ?G ?HSLM ?HSL] => HSL end in
  let lem' := constr:(@refine_disjoint_rev_search_for_idx HSLM HSL _ _ _ G) in
  let H' := fresh in
  assert (H' : ValidReflective.grammar_rvalid G) by (vm_compute; reflexivity);
  let lem' := match goal with
              | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
                => constr:(fun idx' nt its => lem' str offset len nt its idx' H')
              end in
  pose proof lem' as lem;
  clear H'.
Ltac rewrite_once_disjoint_rev_search_for_specialize lem lem' :=
  idtac;
  let G := (lazymatch goal with
             | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
               => G
             end) in
  match goal with
  | [ |- appcontext[ParserInterface.split_list_is_complete_idx ?G ?str ?offset ?len ?idx] ]
    => pose proof (lem idx) as lem';
       do 2 (lazymatch type of lem' with
              | forall a : ?T, _ => idtac; let x := fresh in evar (x : T); specialize (lem' x); subst x
              end);
       let T := match type of lem' with forall a : ?T, _ => T end in
       let H' := fresh in
       assert (H' : T) by solve_disjoint_side_conditions;
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
       assert (H' : T) by solve_disjoint_side_conditions;
       specialize (lem' H'); clear H'
  end.
Ltac rewrite_once_disjoint_rev_search_for lem :=
  let lem' := fresh "lem'" in
  rewrite_once_disjoint_rev_search_for_specialize lem lem';
  setoid_rewrite lem'; clear lem'.
Ltac rewrite_disjoint_rev_search_for_no_clear lem :=
  pose_disjoint_rev_search_for lem;
  progress repeat rewrite_once_disjoint_rev_search_for lem.
Ltac rewrite_disjoint_rev_search_for :=
  idtac;
  let lem := fresh "lem" in
  rewrite_disjoint_rev_search_for_no_clear lem;
  clear lem.
