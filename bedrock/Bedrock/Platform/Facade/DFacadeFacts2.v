Require Import SyntaxExpr.
Require Import DFacadeFacts.
Require Import DFacade.
Require Import Setoid.
Require Import StringMap.
Import StringMap.
Require Import StringMapFacts.
Import FMapNotations.
Local Open Scope fmap_scope.

Section ADTValue.

  Variable av : Type.

  Hint Extern 0 (_ == _) => reflexivity.
  
  Lemma equal_eval (st st' : State av) :
    st' == st ->
    forall e,
      eval st' e = eval st e.
  Proof.
    intros Heq.
    induction e; simpl.
    {
      rewrite Heq.
      eauto.
    }
    {
      eauto.
    }
    {
      rewrite IHe1.
      rewrite IHe2.
      eauto.
    }
    {
      rewrite IHe1.
      rewrite IHe2.
      eauto.
    }
  Qed.
    
  Global Add Morphism (@eval av)
      with signature (StringMap.Equal ==> eq ==> eq)
        as eval_Morphism.
  Proof.
    intros x y Heq e.
    eapply equal_eval; eauto.
  Qed.
    
  Lemma equal_eval_bool (st st' : State av) e :
    st' == st ->
    eval_bool st' e = eval_bool st e.
  Proof.
    intro Heq.
    unfold eval_bool.
    rewrite Heq.
    eauto.
  Qed.
  
  Global Add Morphism (@eval_bool av)
      with signature (StringMap.Equal ==> eq ==> eq)
        as eval_bool_Morphism.
  Proof.
    intros x y Heq e.
    eapply equal_eval_bool; eauto.
  Qed.
    
  Lemma equal_is_true (st st' : State av) e :
    st' == st ->
    (is_true st' e <-> is_true st e).
  Proof.
    intro Heq.
    unfold is_true.
    rewrite Heq.
    intuition.
  Qed.
  
  Global Add Morphism (@is_true av)
      with signature (StringMap.Equal ==> eq ==> iff)
        as is_true_Morphism.
  Proof.
    intros x y Heq e.
    eapply equal_is_true; eauto.
  Qed.
    
  Lemma equal_is_false (st st' : State av) e :
    st' == st ->
    (is_false st' e <-> is_false st e).
  Proof.
    intro Heq.
    unfold is_false.
    rewrite Heq.
    intuition.
  Qed.
  
  Global Add Morphism (@is_false av)
      with signature (StringMap.Equal ==> eq ==> iff)
        as is_false_Morphism.
  Proof.
    intros x y Heq e.
    eapply equal_is_false; eauto.
  Qed.

  Hint Constructors RunsTo.
  
  Lemma Equal_not_mapsto_adt (st st' : State av) k : st == st' -> not_mapsto_adt k st = not_mapsto_adt k st'.
  Proof.
    intros Heq.
    unfold not_mapsto_adt, is_mapsto_adt.
    rewrite Heq.
    eauto.
  Qed.

  Global Add Morphism (@not_mapsto_adt av) with signature eq ==> Equal ==> eq as Equal_not_mapsto_adt_m.
  Proof.
    intros; eapply Equal_not_mapsto_adt; eauto.
  Qed.

  Lemma equal_runsto (env : Env av) s st1 st2 :
    RunsTo env s st1 st2 ->
    forall st1' st2',
      st1 == st1' ->
      st2 == st2' ->
      RunsTo env s st1' st2'.
  Proof.
    induction 1; intros st1' st2' Heq1 Heq2.
    {
      econstructor.
      congruence.
    }
    {
      eauto.
    }
    {
      rename H into Hcond.
      rewrite Heq1 in Hcond.
      eauto.
    }
    {
      rename H into Hcond.
      rewrite Heq1 in Hcond.
      eauto.
    }
    {
      Require Import GeneralTactics3.
      unfold_all.
      rename H into Hcond.
      rewrite Heq1 in Hcond.
      eauto.
    }
    {
      unfold_all.
      rename H into Hcond.
      rewrite Heq1 in Hcond.
      eapply RunsToWhileFalse; eauto.
      congruence.
    }
    {
      rewrite Heq1 in *.
      rewrite Heq2 in *.
      eauto.
    }
    Import ListFacts4.

    Global Add Morphism (@sel av)
        with signature (StringMap.Equal ==> eq ==> eq)
          as sel_Morphism.
    Proof.
      intros x y Heq k.
      unfold sel.
      rewrite Heq; eauto.
    Qed.
    
    Lemma mapM_ext A B (f g : A -> option B) : (forall a, f a = g a) -> forall ls, mapM f ls = mapM g ls.
    Proof.
      intros H.
      induction ls; simpl; intuition.
      rewrite H.
      rewrite IHls.
      eauto.
    Qed.

    Require Import Coq.Classes.Morphisms.
    
    Global Add Parametric Morphism A B : (@mapM A B)
        with signature pointwise_relation A eq ==> eq ==> eq as mapM_m.
    Proof.
      intros; eapply mapM_ext; eauto.
    Qed.

    Global Add Morphism (@sel av)
        with signature (StringMap.Equal ==> pointwise_relation _ eq)
          as sel_Morphism2.
    Proof.
      intros x y Heq k.
      unfold sel.
      rewrite Heq; eauto.
    Qed.
    
    {
      unfold_all.
      rewrite Heq1 in *.
      rewrite Heq2 in *.
      eauto.
    }
    Lemma equal_no_adt_leak (st st' : State av) input args rvar :
      st' == st ->
      (no_adt_leak input args rvar st' <-> no_adt_leak input args rvar st).
    Proof.
      intro Heq.
      unfold no_adt_leak.
      intuition; eapply H; try rewrite Heq in *; eauto.
    Qed.
    
    Global Add Morphism (@no_adt_leak av)
        with signature (eq ==> eq ==> eq ==> StringMap.Equal ==> iff)
          as no_adt_leak_Morphism.
    Proof.
      intros input args rvar x y Heq.
      eapply equal_no_adt_leak; eauto.
    Qed.
    
    {
      unfold_all.
      rewrite Heq1 in *.
      rewrite Heq2 in *.
      eauto.
    }
  Qed.  

  Global Add Parametric Morphism {env} {prog} : (@RunsTo av env prog)
      with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
        as RunsTo_Morphism.
  Proof.
    intros.
    split; intros; eapply equal_runsto; eauto; congruence.
  Qed.
  
  Lemma equal_safe (env : Env av) s : forall st st', st == st' -> Safe env s st -> Safe env s st'.
  Proof.
    intros st st' Heq Hsf.
    eapply Safe_coind with (R := fun s st' => exists st, st == st' /\ Safe env s st).
    {
      clear.
      intros a b st H.
      destruct H as [st' [Heq Hsf] ].
      inversion Hsf; subst.
      rename H2 into Hsf2.
      destruct Hsf2 as [Hsf1 Hsf2].
      split.
      {
        eexists; split; eauto.
      }
      intros st'' Hrt.
      eexists.
      split.
      Focus 2.
      {
        eapply Hsf2.
        rewrite Heq.
        eauto.
      }
      Unfocus.
      eauto.
    }
    {
      intros H t f st1 Hst.
      destruct Hst as [st1' [Heq1 Hst] ].
      inversion Hst; subst.
      {
        left.
        rewrite Heq1 in *.
        split; trivial.
        eexists; split; eauto.
      }
      {
        right.
        rewrite Heq1 in *.
        split; trivial.
        eexists; split; eauto.
      }
    }
    {
      simpl.
      intros cond  body st1 H.
      destruct H as [st1' [Heq1 Hst] ].
      inversion Hst; unfold_all; subst.
      {
        left.
        rewrite Heq1 in *.
        split; trivial.
        split.
        {
          eexists; split; eauto.
        }
        intros st2 Hrt.
        exists st2.
        split; trivial.
        rename H4 into Hrtsf.
        eapply Hrtsf; eauto.
        rewrite Heq1.
        eauto.
      }
      {
        right.
        rewrite Heq1 in *.
        eauto.
      }
    }
    {
      simpl.
      intros x e st1 H.
      destruct H as [st1' [Heq1 Hst] ].
      inversion Hst; unfold_all; subst.
      rewrite Heq1 in *.
      split; trivial.
      eexists; eauto.
    }
    {
      simpl.
      intros x f args st1 H.
      destruct H as [st1' [Heq1 Hst] ].
      inversion Hst; unfold_all; subst.
      {
        rewrite Heq1 in *.
        split; trivial.
        exists input.
        split; trivial.
        left.
        eexists; split; eauto.
      }
      {
        rewrite Heq1 in *.
        split; trivial.
        exists input.
        split; trivial.
        right.
        exists spec.
        split; trivial.
        split; trivial.
        split; trivial.
        eexists; split; eauto.
      }
    }
    {
      eexists; split; eauto.
    }
  Qed.

  Global Add Parametric Morphism {env} {prog} : (@Safe av env prog)
      with signature (StringMap.Equal ==> iff)
        as Safe_Morphism.
  Proof.
    intros; split; intros; eapply equal_safe; try eassumption; congruence.
  Qed.
  
End ADTValue.