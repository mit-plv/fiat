Require HintDbTactics.          (* plugin to pass a hint db to a tactic *)

Require Import Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.

(* Process automation *)

    Ltac invert_For_once :=
      match goal with
      | [ H : computes_to (Query_For _) _ |- _ ] =>
        let H1 := fresh in
        let H2 := fresh in
        inversion H as [H1 H2]; inversion H2; clear H2
      end.

      Ltac refine_under_bind' :=
        setoid_rewrite refine_under_bind; [ higher_order_reflexivity |
                                            let H := fresh in
                                            intros a H; try invert_For_once ].

      Ltac refine_bind' :=
        apply refine_bind; [ idtac | unfold pointwise_relation; intros; higher_order_reflexivity ].

(* ------------------------ *)
(* AddData automation *)

  Lemma eq_If_if {A}
  : forall (c : bool) (t e : Comp A),
      If c Then t Else e = if c then t else e.
  Proof. intros. reflexivity. Qed.

    (* don't rewrite inner If/Then/Else expressions *)
    (* this can be made simpler by removing context[] to only do head matches *)
    Ltac rewrite_if_head :=
      match goal with
      | [ |- context[ (refine (Bind _ (fun n => If_Then_Else _ _ _ )) _) ] ] =>
        setoid_rewrite Bind_refine_If_Then_Else
      end. 

      (* rewrite under bind the first time you can, then stop. otherwise fail *)
      Ltac tac_under_bind tac :=
        first [ tac |
                (apply refine_under_bind; intros); tac_under_bind tac ].

      (* only succeed if all subgoals can be solved with tac. 
intended for use as setoid_rewrite_by *)
      Ltac do_by tic tac :=
        tic; [ | solve [tac] | .. | solve [tac] ].

(* --------------------------- *)
(* General, unified automation *)

      (* tac is of form [first [ x1 | ... | xn]] *)
      Ltac repeat_and_simplify tac :=
        simpl in *;
        try simplify with monad laws;
        repeat (
            try tac;
            try simpl in *;
            try simplify with monad laws
          ).

      (* For a tactic [top] that generates any number of subgoals, succeed only if tac (applied to each subgoal) EVENTUALLY makes progress on at least one of them [i.e. might need to drill twice in a row, the tac will work]. Then try cont again, keeping additional drilling/applying tac if it continues to make progress, until either tac fails everywhere or top fails.

Keep progress made in any of the subgoals (i.e. don't fail the whole thing because a sub-subgoal failed, even though progress was made in a subgoal). 

Fails when top fails (fails iff tac never works on any subgoal) -- if top can loop forever, then this will loop forever 

Subgoals: even if everything fails in the other subgoal, the tactic will succeed if progress is made in the first subgoal, because the failure will be wrapped in a [try] *)

      Ltac progress_subgoal top tac cont :=
         top; (tac; try (cont ()) || (try (cont ()))).

(* Succeeds: 
tac
top tac
top* tac
tac top* tac

Fails:
top (top fail)
top top (top fail)
top top top (top fail)
top*

Other cases:
tac top (top fails): keep progress up to tac
tac top (tac fails): keep progress up to tac, try cont
top tac top (top fails): keep progress up to tac
top tac top (tac fails): keep progress up to tac, try cont

All chains must end with tac, not top (because then there'd be no progress made under it) *)

      (* ltac is call-by-value, so wrap the cont in a function *)
      Ltac cont_fn top tac'' x :=
        apply_under_subgoal top tac'' with

      (* mutually recursive with progress_subgoal *)
      (* calls top on each subgoal generated, which may generate more subgoals *)
      (* fails when top fails in progress_subgoals *)
      apply_under_subgoal top tac'' :=
        progress_subgoal top tac'' ltac:(cont_fn top tac'').

      Theorem testthm : forall n, n = n + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0.
      Proof.
        intros.
        assert (forall y, y + 0 = y) as tm. intros. omega.
        specialize (tm n).
        apply_under_subgoal ltac:(rewrite tm) ltac:(rewrite tm; try reflexivity).
      Qed.

      (* Simplify. Try all the rewrites until none work.
         If a rewrite works under a top, drill under the top and try all the rewrites until none work.
           (Do NOT drill down if no rewrite works. so: Try a drill, if failure for all rewrites, then backtrack, try a different trill. Difficult: there are multiple tops. )
         Keep doing this until none of the rewrites work at any layer of tops.
         Then, do the finishing tactics (eauto, reflexivity, various small lemmas). 
         (These should all be done on all subgoals, keeping all progress made on each one.) *)

      Ltac do_and_simplify tac :=
        tac; (* no repeat *)
        simpl in *;
        try simplify with monad laws.

Ltac srewrite_each_all :=
    first [
           (* Process *)
            setoid_rewrite (@refine_find_upperbound DNSRRecord _ _) |
            setoid_rewrite (@refine_decides_forall_In' _ _ _ _) |
            setoid_rewrite refine_check_one_longest_prefix_s |
            setoid_rewrite refine_if_If |
            setoid_rewrite refine_check_one_longest_prefix_CNAME |
            setoid_rewrite (@refine_filtered_list _ _ _ _) |
            setoid_rewrite refine_bind_unit |
            (* AddData *)
            (* Why does adding these rewrites prevent other rewrites? *)
            (* Should these be drills? *)
            (* TODO messes up Process (only this one) *)
            setoid_rewrite refine_If_Then_Else_Bind |
            setoid_rewrite refine_count_constraint_broken |
            setoid_rewrite refine_count_constraint_broken' |
            setoid_rewrite refine_Count |
            do_by
              ltac:(setoid_rewrite refine_subcheck_to_filter) ltac:(eauto with typeclass_instances) | 
            (* set_evars needed because otherwise it rewrites forever in an evar *)
            (* hacky way to revert outer If to if *)
            try (set_evars; rewrite eq_If_if);
              set_evars; rewrite clear_nested_if by apply filter_nil_is_nil
           (* set_evars; setoid_rewrite refine_if_If *) (* can be done later *)
          ].

Ltac drills_each_all :=
  first [
      subst_all; apply refine_under_bind_both; try intros |
      apply refine_If_Then_Else 
    ].

Ltac finish_each_all :=
  first [
      (eapply tuples_in_relation_satisfy_constraint_specific; eauto) |
      solve [eapply For_computes_to_In; eauto using IsPrefix_string_dec] |
      reflexivity |
      higher_order_reflexivity |
      eauto |
      invert_For_once
    ].

Ltac doAny srewrite_fn drills_fn finish_fn :=
  let repeat_srewrite_fn := repeat_and_simplify srewrite_fn in
  let anyDrill_fn := do_and_simplify drills_fn in
  let repeat_finish_fn := repeat_and_simplify finish_fn in
        try repeat_srewrite_fn; 
        apply_under_subgoal ltac:(anyDrill_fn) ltac:(repeat_srewrite_fn);
        repeat_finish_fn.

Ltac doAnyAll := doAny srewrite_each_all drills_each_all finish_each_all.

(* For debugging *)
Ltac rep_rewrite := repeat_and_simplify srewrite_each_all.
Ltac do_drill := do_and_simplify drills_each_all.
Ltac rep_finish := repeat_and_simplify finish_each_all.

(* ------------------------ *)

Create HintDb refines.
(* Hint Rewrite refine_count_constraint_broken : refines. *)
Hint Rewrite refine_count_constraint_broken' : refines.

Create HintDb refines'.
(* Hint Resolve refine_count_constraint_broken : refines'. *)
Hint Resolve refine_count_constraint_broken' : refines'.

Lemma hi : True. Admitted.
Lemma bye : True. Admitted.
Create HintDb test.
Hint Resolve hi : test.
Hint Resolve bye : test.

Ltac the_tactic :=
  let k lem := idtac lem ; fail in
  foreach [ refines ] run k.

(* this doesn't work well with the [ || ] notation *)
(* why does it need to end with fail? *)
Ltac srewrite :=
  let k lem := setoid_rewrite lem ; fail in
  foreach [ refines ] run k.

(* autorewrite with refines. *)
(* auto with refines'. *)
(* rewrite_strat topdown (hints refines). *)
