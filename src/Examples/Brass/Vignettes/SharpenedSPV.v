Require Import Fiat.Examples.Brass.Vignettes.SPV.
Require Import Fiat.Parsers.Refinement.Tactics.
Require Import Fiat.Parsers.Refinement.DisjointRules.

Set Implicit Arguments.

Section IndexedImpl.
  Lemma ComputationalSplitter'
  : FullySharpened (string_spec spv_grammar string_stringlike).
  Proof.
    start sharpening ADT.
    start honing parser using indexed representation.

    hone method "splits".
    {
      simplify parser splitter.
      let lem := constr:(@refine_disjoint_search_for _ _ _ _) in
      setoid_rewrite lem; [ | solve [reflexivity | repeat esplit].. ].
      finish honing parser method.
    }

    finish_Sharpening_SplitterADT.
  Defined.

  Lemma ComputationalSplitter
  : FullySharpened (string_spec spv_grammar string_stringlike).
  Proof.
    make_simplified_splitter ComputationalSplitter'.
  Defined.

End IndexedImpl.

Require Export Fiat.Parsers.ParserFromParserADT.

Definition spv_parser (str : String.string) : bool.
Proof.
  Time make_parser_without_simpl_list_map ComputationalSplitter. (* 4.0s *)
Defined.

Compute parse_of_grammar "3146105 42.4630932 -76.4433789" spv_grammar.

Definition test1 := spv_parser "3146105 42.4630932 -76.4433789".

Recursive Extraction test1.

Require Import Fiat.QueryStructure.Automation.MasterPlan.

(* Require Import mathcomp.ssreflect.ssreflect. *)
(* From mathcomp Require Export ssrmatching. *)

Ltac higher_order_prod_2_reflexivity :=
  let a := match goal with |- ?R ?a (?f (?x1, ?x2)) => constr:(a) end in
  let f := match goal with |- ?R ?a (?f (?x1, ?x2)) => constr:(f) end in
  let x1 := match goal with |- ?R ?a (?f (?x1, ?x2)) => constr:(x1) end in
  let x2 := match goal with |- ?R ?a (?f (?x1, ?x2)) => constr:(x2) end in
  let a' := (eval pattern x1, x2 in a) in
  let f' := match a' with ?f' _ _ => constr:(f') end in
  unify f (fun x => f' (fst x) (snd x));
    cbv beta;
    solve [apply reflexivity].

Ltac higher_order_prod_3_reflexivity :=
  let a := match goal with |- ?R ?a (?f (?x1, ?x2, ?x3)) => constr:(a) end in
  let f := match goal with |- ?R ?a (?f (?x1, ?x2, ?x3)) => constr:(f) end in
  let x1 := match goal with |- ?R ?a (?f (?x1, ?x2, ?x3)) => constr:(x1) end in
  let x2 := match goal with |- ?R ?a (?f (?x1, ?x2, ?x3)) => constr:(x2) end in
  let x3 := match goal with |- ?R ?a (?f (?x1, ?x2, ?x3)) => constr:(x3) end in
  let a' := (eval pattern x1, x2, x3 in a) in
  let f' := match a' with ?f' _ _ _ => constr:(f') end in
  unify f (fun x => f' (fst (fst x)) (snd (fst x)) (snd x));
    cbv beta;
    solve [apply reflexivity].

Theorem SharpenedSPV : FullySharpened SPVSpec.
Proof.
  unfold SPVSpec.

  start sharpening ADT.
  simpl; pose_string_hyps; pose_heading_hyps.
  start_honing_QueryStructure'.
  - doAny drop_constraints
          master_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
  - repeat drop_constraints.
    master_rewrite_drill || (repeat subst_refine_evar; try finish honing).
    repeat drop_constraints.
    master_rewrite_drill || (repeat subst_refine_evar; try finish honing).
    repeat drop_constraints.
    master_rewrite_drill || (repeat subst_refine_evar; try finish honing).
    destruct a0 as [ [? ?] ?].
    repeat drop_constraints.
    subst_refine_evar; higher_order_prod_3_reflexivity.
    repeat drop_constraints.
    master_rewrite_drill || (repeat subst_refine_evar; try finish honing).
  - hone representation using (@FiniteTables_AbsR SPVSchema).
    + simplify with monad laws.
      refine pick val _; simpl; intuition.
      eauto using FiniteTables_AbsR_QSEmptySpec.
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + doAny simplify_queries
            Finite_AbsR_rewrite_drill ltac:(repeat subst_refine_evar; try finish honing).
    + simpl.
  - simplify with monad laws.
    rewrite refine_For_List.
    rewrite DropQSConstraintsQuery_In.
    rewrite refine_List_Query_In.
      rewrite refine_List_Query_In_Return.
      simplify with monad laws.
      rewrite refine_If_Then_Else_Bind.
      rewrite refine_if.
      + higher_order_reflexivity.
      + intro Heqe.
        rewrite Heqe; simpl.
        simplify with monad laws.
        simpl.
        rewrite freshIdx_UnConstrFreshIdx_Equiv.
        unfold GetRelation.
        simpl.
        (* rewrite refine_Pick_UnConstrFreshIdx. (* ??? *) *)
(*
Defined.

Definition SPVImpl : ComputationalADT.cADT SPVSig :=
  Eval simpl in projT1 SharpenedSPV.

Print SPVImpl.
*)
