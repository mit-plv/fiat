Require Import Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Lists.List.

Require Import Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms.

Export Coq.Vectors.Vector
        Coq.Strings.Ascii
        Coq.Bool.Bool
        Coq.Bool.Bvector
        Coq.Lists.List.

Export Fiat.QueryStructure.Automation.AutoDB
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Automation.IndexSelection
        Fiat.QueryStructure.Specification.SearchTerms.ListPrefix
        Fiat.QueryStructure.Automation.SearchTerms.FindPrefixSearchTerms.

Ltac pick := erewrite refine_pick_val by eauto.
Ltac pick_by H := erewrite refine_pick_val by (eapply H; eauto).

Hint Resolve refine_pick_val.
Hint Rewrite <- app_nil_end.

Definition testnil A B (ls : list A) (cnil ccons : B) : B :=
  match ls with
  | nil => cnil
  | _ :: _ => ccons
  end.

Lemma refine_testnil : forall A (ls : list A) B (c1 cnil ccons : Comp B),
  (ls = nil -> refine c1 cnil)
  -> (ls <> nil -> refine c1 ccons)
  -> refine c1 (testnil ls cnil ccons).
Proof.
  destruct ls; intuition congruence.
Qed.

Add Parametric Morphism A B
: (@testnil A (Comp B))
    with signature
    @eq (list A)
      ==> @refine B
      ==> @refine B
      ==> @refine B
      as refine_testnil_morphism.
Proof.
  destruct y; auto.
Qed.

Lemma refine_testnil_ret : forall A B (ls : list A) (cnil ccons : B),
  refine (testnil ls (ret cnil) (ret ccons)) (ret (testnil ls cnil ccons)).
Proof.
  destruct ls; reflexivity.
Qed.

Ltac refine_testnil ls' := etransitivity; [ apply refine_testnil with (ls := ls'); intro | ].

Definition let_ A B (v : A) (f : A -> B) := let x := v in f v.

Add Parametric Morphism A B
: (@let_ A (Comp B))
    with signature
    @eq A
      ==> pointwise_relation _ (@refine B)
      ==> @refine B
      as refine_let_morphism.
Proof.
  unfold pointwise_relation, let_; auto.
Qed.

Lemma refine_let : forall A B (v : A) c1 (c2 : A -> Comp B),
  (forall x, x = v -> refine c1 (c2 x))
  -> refine c1 (let_ v c2).
Proof.
  unfold let_; auto.
Qed.

Ltac refine_let x := apply (refine_let (v := x)); intros.

Lemma refine_let_ret : forall A B (v : A) (f : A -> B),
  let_ v (fun x => ret (f x)) =  ret (let_ v f).
Proof.
  reflexivity.
Qed.

Ltac monad_simpl := autosetoid_rewrite with refine_monad;
                   try simplify_with_applied_monad_laws; simpl.

Hint Rewrite refine_let_ret refine_testnil_ret : cleanup.

Global Opaque let_.

Ltac done := try match goal with
                 | [ |- refine ?a ?b ] => is_evar b; instantiate (1 := a)
                 end; finish honing.
Ltac cleanup := autorewrite with cleanup.
Ltac finalize := finish_SharpeningADT_WithoutDelegation.

Lemma tl_cons : forall A (x : A) ls1 ls2,
  x :: ls1 = ls2
  -> ls1 = tl ls2.
Proof.
  destruct ls2; simpl; congruence.
Qed.

Hint Resolve tl_cons.

Lemma appendone_contra : forall A (ls : list A) x, ls ++ x :: nil = nil
  -> False.
Proof.
  intros.
  apply (f_equal (@length _)) in H.
  rewrite app_length in H.
  simpl in *; omega.
Qed.

Hint Immediate appendone_contra.

Ltac begin := eexists; intro; set_evars.

Ltac arithmetic := intros;
  repeat match goal with
         | [ |- context[max ?a ?b] ] => let Heq := fresh "Heq" in
                                        destruct (Max.max_spec a b) as [ [? Heq] | [? Heq] ];
                                          rewrite Heq in *; clear Heq
         end; omega.

Ltac refines := intros; repeat computes_to_econstructor; repeat computes_to_inv; subst.

Require Import Fiat.QueryStructure.Automation.MasterPlan.
Ltac FindAttributeUses := EqExpressionAttributeCounter.
Ltac BuildEarlyIndex := LastCombineCase6 BuildEarlyEqualityIndex.
Ltac BuildLastIndex := LastCombineCase5 BuildLastEqualityIndex.
Ltac IndexUse := EqIndexUse.
Ltac createEarlyTerm := createEarlyEqualityTerm .
Ltac createLastTerm := createLastEqualityTerm.
Ltac IndexUse_dep := EqIndexUse_dep.
Ltac createEarlyTerm_dep := createEarlyEqualityTerm_dep.
Ltac createLastTerm_dep := createLastEqualityTerm_dep.
Ltac BuildEarlyBag := BuildEarlyEqualityBag.
Ltac BuildLastBag := BuildLastEqualityBag.

Ltac CreateTerm := IndexUse.
Ltac EarlyIndex := createEarlyTerm.
Ltac LastIndex := createLastTerm.
Ltac makeClause_dep := IndexUse_dep.
Ltac EarlyIndex_dep := createEarlyTerm_dep.
Ltac LastIndex_dep := createLastTerm_dep.

Ltac chooseIndexes :=
  let makeIndex attrlist :=
      make_simple_indexes attrlist
        ltac:(LastCombineCase6 BuildEarlyEqualityIndex)
        ltac:(LastCombineCase5 BuildLastEqualityIndex) in
  GenerateIndexesForAll EqExpressionAttributeCounter ltac:(fun attrlist =>
                                                             let attrlist' := eval compute in (PickIndexes _ (CountAttributes' attrlist)) in makeIndex attrlist').

Ltac implement_filters_using_find :=
  implement_filters_with_find ltac:(find_simple_search_term CreateTerm EarlyIndex LastIndex)
    ltac:(find_simple_search_term_dep makeClause_dep EarlyIndex_dep LastIndex_dep).

Ltac pick_new_database :=
  match goal with
  | [H : @DelegateToBag_AbsR ?qs_schema ?indices ?r_o ?r_n |- _ ] =>
    setoid_rewrite (refine_pick_val (@DelegateToBag_AbsR qs_schema indices r_o) H)
  end;
  monad_simpl.

Ltac planOne := plan CreateTerm EarlyIndex LastIndex
                     makeClause_dep EarlyIndex_dep LastIndex_dep.

Require Import Fiat.QueryStructure.Automation.QSImplementation.

Ltac final_optimizations := eapply FullySharpened_Finish.

Ltac determinize :=
  match goal with
  | |- appcontext[ @BuildADT (IndexedQueryStructure ?Schema ?Indexes) ] =>
    FullySharpenQueryStructure Schema Indexes
  end.

Ltac choose_data_structures :=
  simpl; BuildQSIndexedBags' BuildEarlyBag BuildLastBag.

Ltac final_simplification :=
  simpl Sharpened_Implementation;
  unfold
    Update_Build_IndexedQueryStructure_Impl_cRep,
  Join_Comp_Lists',
  GetIndexedQueryStructureRelation,
  GetAttributeRaw; simpl.

Ltac use_this_one := higher_order_reflexivityT.
