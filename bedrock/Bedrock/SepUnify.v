Require Import Bedrock.ExprUnify.
Require Import Bedrock.SepHeap.
Require Import Bedrock.Expr.
Require Import Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implicit.

Module Make (U : SynUnifier) (SH : SepHeap).
  Module SH_FACTS := SepHeapFacts SH.
  Import SH_FACTS.

  Section typed.
    Variable types : list type.
    Variable pcT stT : tvar.

    Variable s : U.Subst types.

    Definition impuresInstantiate : MM.mmap (exprs types) -> MM.mmap (exprs types) :=
      MM.mmap_map (map (@U.exprInstantiate _ s)).

    Definition sheapInstantiate (h : SH.SHeap types pcT stT) : SH.SHeap types pcT stT :=
      {| SH.impures := impuresInstantiate (SH.impures h)
       ; SH.pures   := map (@U.exprInstantiate _ s) (SH.pures h)
       ; SH.other   := SH.other h
       |}.

    Variable funcs : functions types.
    Variable preds : SH.SE.predicates types pcT stT.

    Variables U G : env types.
    Variable cs : PropX.codeSpec (tvarD types pcT) (tvarD types stT).

    Lemma impuresInstantiate_mmap_add : forall n e acc,
      SH.SE.heq funcs preds U G cs
        (SH.impuresD pcT stT (impuresInstantiate (MM.mmap_add n e acc)))
        (SH.impuresD pcT stT
          (MM.mmap_add n (map (@U.exprInstantiate _ s) e)
                         (impuresInstantiate acc))).
    Proof.
      clear. intros. eapply MM.PROPS.map_induction with (m := acc); intros.
      { unfold MM.mmap_add, impuresInstantiate, MM.mmap_map.
        repeat rewrite MF.find_Empty by auto using MF.map_Empty.
        rewrite SH.impuresD_Equiv. reflexivity.
        rewrite MF.map_add. simpl.
        reflexivity. }
      { unfold MM.mmap_add, impuresInstantiate, MM.mmap_map.
        rewrite MF.FACTS.map_o. simpl in *. unfold exprs in *. case_eq (FM.find n m'); simpl; intros.
        { rewrite SH.impuresD_Equiv. reflexivity.
          rewrite MF.map_add. reflexivity. }
        { rewrite SH.impuresD_Equiv. reflexivity.
          rewrite MF.map_add. simpl. reflexivity. } }
    Qed.

    Lemma sheapInstantiate_Equiv : forall a b,
      MM.mmap_Equiv a b ->
      MM.mmap_Equiv (impuresInstantiate a) (impuresInstantiate b).
    Proof.
      clear. unfold impuresInstantiate, MM.mmap_Equiv, MM.mmap_map, FM.Equiv; intuition;
      try solve [ repeat match goal with
                           | [ H : FM.In _ (FM.map _ _) |- _ ] => apply MF.FACTS.map_in_iff in H
                           | [ |- FM.In _ (FM.map _ _) ] => apply MF.FACTS.map_in_iff
                         end; firstorder ].
      repeat match goal with
               | [ H : FM.MapsTo _ _ (FM.map _ _) |- _ ] =>
                 apply MF.FACTS.map_mapsto_iff in H; destruct H; intuition; subst
             end.
      apply Permutation.Permutation_map. firstorder.
    Qed.

    Lemma sheapInstantiate_add : forall n e m m',
      ~FM.In n m ->
      MM.PROPS.Add n e m m' ->
      SH.SE.heq funcs preds U G cs
        (SH.impuresD pcT stT (impuresInstantiate m'))
        (SH.starred (fun v => SH.SE.Func n (map (U.exprInstantiate s) v)) e
          (SH.impuresD pcT stT (impuresInstantiate m))).
    Proof.
      clear. intros.
        unfold impuresInstantiate, MM.mmap_map.
        rewrite SH.impuresD_Add with (i := FM.map (map (map (U.exprInstantiate s))) m) (f := n) (argss := map (map (U.exprInstantiate s)) e).
        symmetry; rewrite SH.starred_base. heq_canceler.
        repeat rewrite SH.starred_def.
        match goal with
          | [ |- context [ @SH.SE.Emp ?X ?Y ?Z ] ] => generalize (@SH.SE.Emp X Y Z)
        end.
        clear. induction e; simpl; intros; try reflexivity.
        rewrite IHe. heq_canceler.

        red. intros. specialize (H0 y). repeat (rewrite MM.FACTS.add_o in * || rewrite MM.FACTS.map_o in * ).
        unfold exprs in *. rewrite H0. unfold MM.FACTS.option_map. destruct (MF.FACTS.eq_dec n y); auto.

        intro. apply H. apply MM.FACTS.map_in_iff in H1. auto.
    Qed.

    Lemma applyD_forget_exprInstantiate :
      U.Subst_equations funcs U G s ->
      forall D R F l,
        applyD (exprD funcs U G) D (map (U.exprInstantiate s) l) R F =
        applyD (exprD funcs U G) D l R F.
    Proof.
      clear. induction D; destruct l; simpl; auto.
      rewrite U.Subst_equations_exprInstantiate; eauto.
      destruct (exprD funcs U G e a); eauto.
    Qed.

    Lemma starred_forget_exprInstantiate : forall x P,
      U.Subst_equations funcs U G s ->
      forall e,
      SH.SE.heq funcs preds U G cs
        (SH.starred (fun v : list (expr types) => SH.SE.Func x (map (U.exprInstantiate s) v)) e P)
        (SH.starred (SH.SE.Func x) e P).
    Proof.
      clear. induction e; intros; repeat rewrite SH.starred_def; simpl; repeat rewrite <- SH.starred_def; SEP_FACTS.heq_canceler.
        rewrite IHe. SEP_FACTS.heq_canceler. unfold SH.SE.heq. simpl.
        match goal with
                 | [ |- context [ match ?X with _ => _ end ] ] =>
                   case_eq X; intros; try reflexivity
               end.
        erewrite applyD_forget_exprInstantiate with (D := SH.SE.SDomain p) (F := SH.SE.SDenotation p); eauto.
        reflexivity.
    Qed.

    Lemma impuresD_forget_impuresInstantiate : forall h,
      U.Subst_equations funcs U G s ->
      SH.SE.heq funcs preds U G cs
        (SH.impuresD pcT stT (impuresInstantiate h))
        (SH.impuresD pcT stT h).
    Proof.
      clear. intros. eapply MM.PROPS.map_induction with (m := h); intros.
      { unfold sheapInstantiate, MM.mmap_map. repeat rewrite SH.impuresD_Empty; eauto using MF.map_Empty. reflexivity. }
      { rewrite sheapInstantiate_add; eauto. rewrite SH.starred_base. symmetry.
        rewrite SH.impuresD_Add; eauto. rewrite <- H0. SEP_FACTS.heq_canceler.
        rewrite starred_forget_exprInstantiate; auto. reflexivity. }
    Qed.

    Lemma Func_forget_exprInstantiate : forall n e,
      U.Subst_equations funcs U G s ->
      SH.SE.heq funcs preds U G cs (SH.SE.Func n (map (U.exprInstantiate s) e)) (SH.SE.Func n e).
    Proof. clear.
      unfold SH.SE.heq. simpl. intros.
      destruct (nth_error preds n); try reflexivity.
      rewrite applyD_forget_exprInstantiate; auto. reflexivity.
    Qed.

  End typed.

End Make.
