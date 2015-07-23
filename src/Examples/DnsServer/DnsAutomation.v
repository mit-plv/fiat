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
        Fiat.QueryStructure.Automation.SearchTerms.FindSuffixSearchTerms
        Fiat.QueryStructure.Automation.QSImplementation.

Require Import Fiat.Examples.DnsServer.packet
        Fiat.Examples.DnsServer.DnsSchema
        Fiat.Examples.DnsServer.DnsLemmas.


(* For Process *)

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

    Ltac srewrite_each :=
      first
             [
               setoid_rewrite (@refine_find_upperbound DNSRRecord _ _) |
                              setoid_rewrite (@refine_decides_forall_In' _ _ _ _) |
                              setoid_rewrite refine_check_one_longest_prefix_s |
                              setoid_rewrite refine_if_If |
                              setoid_rewrite refine_check_one_longest_prefix_CNAME
             ].

    Ltac srewrite_manual' :=
      repeat (
          try srewrite_each;
          try simplify with monad laws
        );
      repeat (
          try (eapply tuples_in_relation_satisfy_constraint_specific; eauto);
          try (eapply computes_to_in_specific; eauto);
          try reflexivity
        );
    try simplify with monad laws.

    (* not very automated -- TODO try to get rid of these / use setoid_rewrite *)
    Ltac drill :=
      simpl in *;
      try simplify with monad laws;
      try refine_under_bind';
      try refine_bind';
      try apply refine_If_Then_Else.

    (* drill. srewrite_manual'. reflexivity. (* nothing applies to this last goal *) *)

    Ltac automateProcess :=
      drill; srewrite_manual'.





    (* ------------------ *)
    (* For AddData *)

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
(* ---------------------------- TODO: use the database plugin above *)

(* don't rewrite inner If/Then/Else expressions *)
  Ltac rewrite_if_head :=
    match goal with
    | [ |- context[ (refine (Bind _ (fun n => If_Then_Else _ _ _ )) _) ] ] =>
      setoid_rewrite Bind_refine_If_Then_Else
    end. 

Ltac srewrite_manual :=
  repeat first [
           setoid_rewrite refine_count_constraint_broken 
                          || setoid_rewrite refine_count_constraint_broken'
                          || setoid_rewrite refine_If_Then_Else_Bind
                          || rewrite_if_head
                          || setoid_rewrite refine_Count
         ]. 

(* rewrite under bind the first time you can, then stop. otherwise fail *)
Ltac tac_under_bind tac :=
  first [ tac |
              (apply refine_under_bind; intros); tac_under_bind tac ].

(* only succeed if all subgoals can be solved with tac. 
intended for use as setoid_rewrite_by *)
Ltac do_by tic tac :=
  tic; [ | solve [tac] | .. | solve [tac] ].

Ltac finishHone H :=
  repeat (simpl in *;
          try simplify with monad laws;
          try (apply refine_If_Then_Else);
          try simplify with monad laws;
          try tac_under_bind ltac:(
 do_by ltac:(setoid_rewrite refine_subcheck_to_filter) ltac:(eauto with typeclass_instances);
 try (simplify with monad laws);
 try (rewrite clear_nested_if by apply filter_nil_is_nil));
          try simplify with monad laws;
          try eauto;
          try (clear H; reflexivity) (* TODO why clear *)
         ).

(* finishHone H. *)
(* only difference is the Count vs beq_nat *)

Ltac setoid_rewrite_by lem tac :=
  setoid_rewrite lem;
  [ | solve [tac] | .. | solve [tac] ].

(* setoid_rewrite_by refine_subcheck_to_filter ltac:(eauto with typeclass_instances). *)
(* doesn't work; can't infer heading *)

Ltac automateAddData H := srewrite_manual; finishHone H.

(* automateAddData H.              (* 13 seconds *) *)
  (* TODO why need to clear H? *)