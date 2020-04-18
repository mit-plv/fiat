Require Import Coq.Lists.List.
Require Import Bedrock.SepTheoryX Bedrock.PropX.
Require Import Bedrock.PropXTac.
Require Import Coq.Classes.RelationClasses Bedrock.EqdepClass.
Require Import Bedrock.Expr.
Require Import Coq.Setoids.Setoid.
Require Import Bedrock.Folds Coq.Bool.Bool Bedrock.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Definition BadInj types (e : expr types) := False.
Definition BadPred (f : func) := False.
Definition BadPredApply types (f : func) (es : list (expr types)) (_ : env types) := False.

Module Type SepExpr.
  Declare Module ST : SepTheoryX.SepTheoryX.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record predicate := PSig {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition predicates : Type := list predicate.

    Parameter Default_predicate : predicate.

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil -> sexpr
    .

    Definition tpredicate : Type := list tvar.
    Definition tpredicates : Type := list tpredicate.

    Definition typeof_pred : predicate -> tpredicate := SDomain.
    Definition typeof_preds : predicates -> tpredicates := map typeof_pred.

    Section types.
      Variable funcs : tfunctions.
      Variable preds : tpredicates.
      Variable tU : tenv.

      Fixpoint WellTyped_sexpr (tG : tenv) (s : sexpr) : bool :=
        match s with
          | Emp => true
          | Inj e => is_well_typed funcs tU tG e tvProp
          | Star l r => WellTyped_sexpr tG l && WellTyped_sexpr tG r
          | Exists t e => WellTyped_sexpr (t :: tG) e
          | Func f args =>
            match nth_error preds f with
              | None => false
              | Some ts => all2 (is_well_typed funcs tU tG) args ts
            end
          | Const _ => true
        end.

    End types.

    (** sexprD (U ++ U') (G ++ G') e <===>
     ** sexprD (U ++ U'' ++ U') (G ++ G'' ++ G')
     **    (liftSExpr (length U) (length U'') (length G) (length G'') e)
     **)
    Fixpoint liftSExpr ua ub a b s : sexpr :=
      match s with
        | Emp => Emp
        | Const c => Const c
        | Inj p => Inj (liftExpr ua ub a b p)
        | Star l r => Star (liftSExpr ua ub a b l) (liftSExpr ua ub a b r)
        | Exists t s => Exists t (liftSExpr ua ub (S a) b s)
        | Func f args => Func f (map (liftExpr ua ub a b) args)
      end.

    Section funcs_preds.
      Variable funcs : functions types.
      Variable preds : predicates.

      Fixpoint sexprD (meta_env var_env : env types) (s : sexpr)
        : ST.hprop (tvarD types pcType) (tvarD types stateType) nil :=
        match s with
          | Emp => ST.emp _ _
          | Inj p =>
            match exprD funcs meta_env var_env p tvProp with
              | None => ST.inj (PropX.Inj (BadInj p))
              | Some p => ST.inj (PropX.Inj p)
            end
          | Star l r =>
            ST.star (sexprD meta_env var_env l) (sexprD meta_env var_env r)
          | Exists t b =>
            ST.ex (fun x : tvarD types t => sexprD meta_env (@existT _ _ t x :: var_env) b)
          | Func f b =>
            match nth_error preds f with
              | None => ST.inj (PropX.Inj (BadPred f))
              | Some f' =>
                match applyD (@exprD types funcs meta_env var_env) (SDomain f') b _ (SDenotation f') with
                  | None => ST.inj (PropX.Inj (BadPredApply f b var_env))
                  | Some p => p
                end
            end
          | Const p => p
        end.

      Definition himp (meta_env var_env : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        ST.himp cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

      Definition heq (meta_env var_env : env types)
        (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
        (gl gr : sexpr) : Prop :=
        ST.heq cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

    End funcs_preds.

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.

  End env.

  Implicit Arguments Emp [ types pcType stateType ].
  Implicit Arguments Star [ types pcType stateType ].
  Implicit Arguments Exists [ types pcType stateType ].
  Implicit Arguments Func [ types pcType stateType ].
  Implicit Arguments Const [ types pcType stateType ].
  Implicit Arguments Inj [ types pcType stateType ].

End SepExpr.

Require Import Bedrock.Reflection.

Module SepExprFacts (SE : SepExpr).
  Module SEP_FACTS := SepTheoryX_Rewrites SE.ST.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.
    Variable funcs : functions types.
    Variable preds : SE.predicates types pcType stateType.

    Variables U G : env types.
    Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

    Global Instance Trans_himp : Transitive (@SE.himp types _ _ funcs preds U G cs).
    Proof.
      red. unfold SE.himp. intros; etransitivity; eauto.
    Qed.

    Global Instance Trans_heq : Transitive (@SE.heq types _ _ funcs preds U G cs).
    Proof.
      red. unfold SE.heq. intros; etransitivity; eauto.
    Qed.

    Global Instance Refl_himp : Reflexive (@SE.himp types _ _ funcs preds U G cs).
    Proof.
      red; unfold SE.himp; intros. reflexivity.
    Qed.

    Global Instance Refl_heq : Reflexive (@SE.heq types _ _ funcs preds U G cs).
    Proof.
      red; unfold SE.heq; intros. reflexivity.
    Qed.

    Global Instance Sym_heq : Symmetric (@SE.heq types _ _ funcs preds U G cs).
    Proof.
      red; unfold SE.heq; intros. symmetry. auto.
    Qed.

    Global Instance Equiv_heq : Equivalence (SE.heq funcs preds U G cs).
    Proof.
      constructor; eauto with typeclass_instances.
    Qed.

    Lemma heq_defn : forall P Q,
      (@SE.himp types _ _ funcs preds U G cs P Q /\
       @SE.himp types _ _ funcs preds U G cs Q P) <->
      (@SE.heq types _ _ funcs preds U G cs P Q).
    Proof.
      unfold SE.heq, SE.himp. intros; apply SE.ST.heq_defn.
    Qed.

    Lemma heq_himp : forall P Q,
      @SE.heq types _ _ funcs preds U G cs P Q ->
      @SE.himp types _ _ funcs preds U G cs P Q.
    Proof.
      unfold SE.heq, SE.himp. intros; apply SE.ST.heq_himp; auto.
    Qed.

    Lemma himp_not_WellTyped : forall tfuncs tG tU f P Q l,
      WellTyped_env tU U ->
      WellTyped_env tG G ->
      WellTyped_funcs tfuncs funcs ->
      (forall p,
        nth_error preds f = Some p ->
        Folds.all2 (@is_well_typed types tfuncs tU tG) l (SE.SDomain p) = true ->
        SE.himp funcs preds U G cs (SE.Star (SE.Func f l) P) Q) ->
      SE.himp funcs preds U G cs (SE.Star (SE.Func f l) P) Q.
    Proof.
      intros. unfold SE.himp in *; simpl in *. consider (nth_error preds f); intros;
        try solve [ eapply SE.ST.himp_star_pure_c; contradiction ].
      match goal with
        | [ |- context [ match ?X with | _ => _ end ] ] =>
          case_eq X
      end; intros; try solve [ eapply SE.ST.himp_star_pure_c; contradiction ].
      specialize (H3 _ refl_equal). rewrite <- H3. rewrite H4. reflexivity.

      clear H2. clear H3. destruct p; simpl in *. generalize dependent l.
      induction SDomain; destruct l; simpl; intros; auto; try congruence.
      revert H4. consider (exprD funcs U G e a); intros.
      erewrite is_well_typed_correct_only by eauto. eapply IHSDomain; eauto. congruence.
    Qed.

    Add Parametric Relation : (@SE.sexpr types pcType stateType) (@SE.himp types _ _ funcs preds U G cs)
      reflexivity proved by  Refl_himp
      transitivity proved by Trans_himp
    as himp_rel.

    Add Parametric Relation : (@SE.sexpr types pcType stateType) (@SE.heq types _ _ funcs preds U G cs)
      reflexivity proved by  Refl_heq
      symmetry proved by Sym_heq
      transitivity proved by Trans_heq
    as heq_rel.

    Global Add Parametric Morphism : (@SE.Star types pcType stateType) with
      signature (SE.himp funcs preds U G cs ==> SE.himp funcs preds U G cs ==> SE.himp funcs preds U G cs)
      as star_himp_mor.
    Proof.
      unfold SE.himp; simpl; intros; eapply SEP_FACTS.star_himp_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (@SE.Star types pcType stateType) with
      signature (SE.heq funcs preds U G cs ==> SE.heq funcs preds U G cs ==> SE.heq funcs preds U G cs)
      as star_heq_mor.
    Proof.
      unfold SE.himp; simpl; intros; eapply SEP_FACTS.star_heq_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.himp funcs preds U G cs) with
      signature (SE.heq funcs preds U G cs ==> SE.heq funcs preds U G cs ==> Basics.impl)
      as himp_heq_mor.
    Proof.
      unfold SE.heq; simpl; intros. eapply SEP_FACTS.himp_heq_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.himp funcs preds U G cs) with
      signature (SE.himp funcs preds U G cs --> SE.himp funcs preds U G cs ==> Basics.impl)
      as himp_himp_mor.
    Proof.
      unfold SE.himp; simpl; intros. intro. etransitivity. eauto. etransitivity; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.himp funcs preds U G cs) with
      signature (SE.himp funcs preds U G cs --> SE.himp funcs preds U G cs ++> Basics.impl)
      as himp_himp_mor'.
    Proof.
      unfold SE.himp; simpl; intros. eapply SEP_FACTS.himp_himp_mor; eauto.
    Qed.

    Global Add Parametric Morphism : (SE.sexprD funcs preds U G) with
      signature (SE.heq funcs preds U G cs ==> SE.ST.heq cs)
      as heq_ST_heq_mor.
    Proof.
      unfold SE.heq; simpl; auto.
    Qed.

    Global Add Parametric Morphism : (SE.sexprD funcs preds U G) with
      signature (SE.himp funcs preds U G cs ==> SE.ST.himp cs)
      as himp_ST_himp_mor.
    Proof.
      unfold SE.himp; simpl; auto.
    Qed.

    Lemma heq_star_emp_r : forall P,
      SE.heq funcs preds U G cs (SE.Star P SE.Emp) P.
    Proof.
      unfold SE.heq; simpl; intros; autorewrite with hprop; reflexivity.
    Qed.

    Lemma heq_star_emp_l : forall P,
      SE.heq funcs preds U G cs (SE.Star SE.Emp P) P.
    Proof.
      unfold SE.heq; simpl; intros; autorewrite with hprop; reflexivity.
    Qed.

    Lemma heq_star_assoc : forall P Q R,
      SE.heq funcs preds U G cs (SE.Star (SE.Star P Q) R) (SE.Star P (SE.Star Q R)).
    Proof.
      unfold SE.heq; simpl; intros; autorewrite with hprop. rewrite SE.ST.heq_star_assoc. reflexivity.
    Qed.

    Lemma heq_star_comm : forall P Q,
      SE.heq funcs preds U G cs (SE.Star P Q) (SE.Star Q P).
    Proof.
      unfold SE.heq; simpl; intros; apply SE.ST.heq_star_comm.
    Qed.

    Lemma heq_star_frame : forall P Q R S,
      SE.heq funcs preds U G cs P R ->
      SE.heq funcs preds U G cs Q S ->
      SE.heq funcs preds U G cs (SE.Star P Q) (SE.Star R S).
    Proof.
      unfold SE.heq; simpl; intros. eapply SE.ST.heq_star_frame; auto.
    Qed.

    Lemma himp_star_frame : forall P Q R S,
      SE.himp funcs preds U G cs P R ->
      SE.himp funcs preds U G cs Q S ->
      SE.himp funcs preds U G cs (SE.Star P Q) (SE.Star R S).
    Proof.
      unfold SE.himp; simpl; intros. rewrite H; rewrite H0; reflexivity.
    Qed.

    Lemma heq_star_comm_p : forall P Q R,
      SE.heq funcs preds U G cs (SE.Star P Q) R ->
      SE.heq funcs preds U G cs (SE.Star Q P) R.
    Proof.
      intros. rewrite heq_star_comm. auto.
    Qed.

    Lemma heq_star_comm_c : forall P Q R,
      SE.heq funcs preds U G cs R (SE.Star P Q) ->
      SE.heq funcs preds U G cs R (SE.Star Q P).
    Proof.
      intros. rewrite heq_star_comm. auto.
    Qed.

    Lemma heq_star_assoc_p1 : forall P Q R S,
      SE.heq funcs preds U G cs (SE.Star P (SE.Star Q R)) S ->
      SE.heq funcs preds U G cs (SE.Star (SE.Star P Q) R) S.
    Proof.
      intros. rewrite heq_star_assoc; auto.
    Qed.

    Lemma heq_star_assoc_p2 : forall P Q R S,
      SE.heq funcs preds U G cs (SE.Star Q (SE.Star P R)) S ->
      SE.heq funcs preds U G cs (SE.Star (SE.Star P Q) R) S.
    Proof.
      intros. apply heq_star_assoc_p1 in H. rewrite <- H.
      apply heq_star_frame; try reflexivity. rewrite heq_star_comm. reflexivity.
    Qed.

    Lemma heq_star_assoc_c1 : forall P Q R S,
      SE.heq funcs preds U G cs S (SE.Star P (SE.Star Q R)) ->
      SE.heq funcs preds U G cs S (SE.Star (SE.Star P Q) R).
    Proof.
      intros. rewrite heq_star_assoc; auto.
    Qed.

    Lemma heq_star_assoc_c2 : forall P Q R S,
      SE.heq funcs preds U G cs S (SE.Star Q (SE.Star P R)) ->
      SE.heq funcs preds U G cs S (SE.Star (SE.Star P Q) R).
    Proof.
      intros. apply heq_star_assoc_c1 in H. rewrite H.
      apply heq_star_frame; try reflexivity. apply heq_star_comm; reflexivity.
    Qed.

    Lemma heq_star_emp_p : forall P S,
      SE.heq funcs preds U G cs P S ->
      SE.heq funcs preds U G cs (SE.Star SE.Emp P) S.
    Proof.
      intros. rewrite heq_star_emp_l. auto.
    Qed.

    Lemma heq_star_emp_c : forall P S,
      SE.heq funcs preds U G cs S P ->
      SE.heq funcs preds U G cs S (SE.Star SE.Emp P).
    Proof.
      intros. rewrite heq_star_emp_l. auto.
    Qed.

  End env.

  Ltac heq_canceler :=
    let cancel cp ap1 ap2 ep cc ac1 ac2 ec frm P Q :=
      let rec iter_right Q :=
        match Q with
          | SE.Emp =>
            apply ec
          | SE.Star ?L ?R =>
            (apply ac1 ; iter_right L) || (apply ac2 ; iter_right R)
          | _ =>
            apply frm; [ reflexivity | ]
        end
      in
      let rec iter_left P :=
        match P with
          | SE.Emp =>
            apply ep
          | SE.Star ?L ?R =>
            (apply ap1 ; iter_left L) || (apply ap2 ; iter_left R)
          | _ =>
            match Q with
              | SE.Star ?A ?B =>
                iter_right A || (apply cc; iter_right B)
            end
        end
      in
      match P with
        | SE.Star ?A ?B =>
          iter_left A || (apply cp; iter_left B)
      end
    in
    repeat (rewrite heq_star_emp_l || rewrite heq_star_emp_r) ;
    repeat match goal with
             | [ |- SE.heq _ _ _ _ _ ?P ?Q ] =>
               cancel heq_star_comm_p heq_star_assoc_p1 heq_star_assoc_p2 heq_star_emp_p
                      heq_star_comm_c heq_star_assoc_c1 heq_star_assoc_c2 heq_star_emp_c
                      heq_star_frame P Q
(*    | [ |- SE.himp _ _ _ _ _ ?P ?Q ] =>
   cancel himp_star_comm_p himp_star_assoc_p himp_star_comm_c himp_star_assoc_c P Q
   *)
    end; try reflexivity.

  Section other.
    Variable types : list type.
    Variables pcT stT : tvar.
    Variable funcs : functions types.
    Variable preds : SE.predicates types pcT stT.
    Variable cs : codeSpec (tvarD types pcT) (tvarD types stT).

    Theorem sexprD_weaken_wt : forall U U' G' s G,
      SE.WellTyped_sexpr (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env U) (typeof_env G) s = true ->
      SE.ST.heq cs (SE.sexprD funcs preds U G s)
                   (SE.sexprD funcs preds (U ++ U') (G ++ G') s).
    Proof.
      induction s; simpl; intros; think; try reflexivity.
      { consider (exprD funcs U G e tvProp); intros.
        erewrite exprD_weaken by eauto. reflexivity.
        rewrite <- SE.ST.heq_star_emp_r.
        eapply is_well_typed_correct in H; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
        rewrite H0 in H. exfalso; destruct H; congruence. }
      { eapply SE.ST.heq_ex. intros. rewrite IHs; eauto. reflexivity. }
      { unfold SE.typeof_preds in *. rewrite map_nth_error_full in H.
        consider (nth_error preds f); intros; try reflexivity. inversion H1; subst.
        clear H1 H. destruct p; simpl in *. generalize dependent SDomain.
        induction l; destruct SDomain; intros; simpl in *; think; try (reflexivity || congruence).
        eapply is_well_typed_correct in H; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
        destruct H. erewrite exprD_weaken; eauto. rewrite H. eauto. }
    Qed.

    Theorem sexprD_weaken : forall s U G G' U',
      SE.ST.himp cs (SE.sexprD funcs preds U G s)
                    (SE.sexprD funcs preds (U ++ U') (G ++ G') s).
    Proof.
      induction s; simpl; intros; try reflexivity.
      { consider (exprD funcs U G e tvProp); intros.
        erewrite exprD_weaken by eauto. reflexivity.
        rewrite <- SE.ST.heq_star_emp_r.
        eapply SE.ST.himp_star_pure_c. contradiction. }
      { rewrite IHs1. rewrite IHs2. reflexivity. }
      { apply SE.ST.himp_ex. intros. rewrite IHs with (U' := U') (G' := G'). reflexivity. }
      { destruct (nth_error preds f); try reflexivity.
        match goal with
          | [ |- SE.ST.himp _ match ?X with _ => _ end _ ] =>
            consider X
        end; intros.
        erewrite Expr.applyD_weaken by eauto. reflexivity.
        rewrite <- SE.ST.heq_star_emp_r.
        eapply SE.ST.himp_star_pure_c. unfold BadPredApply. contradiction. }
    Qed.

    Theorem liftSExpr_sexprD : forall cs s U U' U'' G G' G'',
      SE.ST.heq cs (SE.sexprD funcs preds (U ++ U') (G ++ G') s)
                   (SE.sexprD funcs preds (U ++ U'' ++ U') (G ++ G'' ++ G')
                     (SE.liftSExpr (length U) (length U'') (length G) (length G'') s)).
    Proof.
      do 8 intro. revert G. induction s; simpl; intros; think; try reflexivity.
      rewrite <- liftExpr_ext. reflexivity.
      apply SE.ST.heq_ex. intros. etransitivity.
      change (existT (tvarD types) t v :: G ++ G') with ((existT (tvarD types) t v :: G) ++ G'). eapply IHs. reflexivity.
      destruct (nth_error preds f); try reflexivity.
      match goal with
        | [ |- SE.ST.heq _ match ?X with _ => _ end match ?Y with _ => _ end ] =>
          cutrewrite (X = Y); try reflexivity
      end.
      destruct p; simpl. clear. revert l; induction SDomain; destruct l; simpl; auto.
      rewrite <- liftExpr_ext. destruct (exprD funcs (U ++ U') (G ++ G') e a); eauto.
    Qed.

    Theorem liftSExpr_combine : forall (s : SE.sexpr types pcT stT) ua ub uc a b c,
      SE.liftSExpr ua ub a b (SE.liftSExpr ua uc a c s) =
      SE.liftSExpr ua (uc + ub) a (c + b) s.
    Proof.
      clear. induction s; intros; simpl; think; try reflexivity.
      rewrite liftExpr_combine. reflexivity.
      f_equal. clear. induction l; simpl; intros; try rewrite liftExpr_combine; think; auto.
    Qed.

    Theorem liftSExpr_0 : forall (s : SE.sexpr types pcT stT) ua a,
      SE.liftSExpr ua 0 a 0 s = s.
    Proof.
      clear; induction s; intros; simpl; think; try reflexivity.
      rewrite liftExpr_0; auto.
      f_equal. clear. induction l; simpl; intros; try rewrite liftExpr_0; think; auto.
    Qed.
  End other.

  Theorem interp_WellTyped_sexpr : forall ts pcT stT funcs (preds : SE.predicates ts pcT stT) cs s vars uvars stn m,
    SE.ST.satisfies cs (SE.sexprD funcs preds uvars vars s) stn m ->
    SE.WellTyped_sexpr (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env uvars) (typeof_env vars) s = true.
  Proof.
    induction s; simpl; intros; auto.
    { consider (exprD funcs uvars vars e tvProp); intros.
      eapply is_well_typed_correct_only in H; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
      eapply SE.ST.satisfies_pure in H0. unfold BadInj. intuition. PropXTac.propxFo. }
    { eapply SE.ST.satisfies_star in H.
      repeat match goal with
               | [ H : exists x, _ |- _ ] => destruct H
               | [ H : _ /\ _ |- _ ] => destruct H
             end.
      erewrite IHs1; eauto.
      erewrite IHs2; eauto. }
    { eapply SE.ST.satisfies_ex in H. destruct H.
      eapply IHs in H. simpl in *. auto. }
    { unfold SE.typeof_preds. rewrite map_nth_error_full. destruct (nth_error preds f).
      { destruct p; simpl in *. generalize dependent SDomain. clear. induction l; destruct SDomain; simpl; intros; auto.
        eapply SE.ST.satisfies_pure in H. unfold BadPredApply. intuition. PropXTac.propxFo.
        eapply SE.ST.satisfies_pure in H. unfold BadPredApply. intuition. PropXTac.propxFo.
        consider (exprD funcs uvars vars a t); intros.
        erewrite is_well_typed_correct_only; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
        eapply SE.ST.satisfies_pure in H0. unfold BadPredApply. intuition. PropXTac.propxFo. }
      { eapply SE.ST.satisfies_pure in H. unfold BadPred. intuition. PropXTac.propxFo. } }
  Qed.

  Theorem himp_not_WellTyped_sexpr : forall ts pcT stT funcs (preds : SE.predicates ts pcT stT) cs s vars uvars,
    SE.WellTyped_sexpr (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env uvars) (typeof_env vars) s = false ->
    SE.ST.himp cs (SE.sexprD funcs preds uvars vars s) (SE.ST.inj [| False |]).
  Proof.
    induction s; simpl; intros; auto; try congruence.
    { consider (exprD funcs uvars vars e tvProp); intros; try reflexivity.
      eapply is_well_typed_correct_only in H0; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs. congruence. }
    { apply andb_false_iff in H. destruct H.
      rewrite IHs1 by auto. eapply SE.ST.himp_star_pure_c; contradiction.
      rewrite SE.ST.heq_star_comm.
      rewrite IHs2 by auto. eapply SE.ST.himp_star_pure_c; contradiction. }
    { eapply SE.ST.himp_ex_p. intros.
      rewrite IHs. reflexivity. auto. }
    { unfold SE.typeof_preds in H.
      rewrite map_nth_error_full in H. destruct (nth_error preds f); try reflexivity.
      destruct p; simpl in *. generalize dependent SDomain. induction l; destruct SDomain; simpl in *; intros; auto; try (congruence || reflexivity).
      consider (is_well_typed (typeof_funcs funcs) (typeof_env uvars) (typeof_env vars) a t); intros.
      eapply is_well_typed_correct in H. destruct H. rewrite H.
      rewrite IHl. reflexivity. auto.
      eauto using typeof_env_WellTyped_env.
      eauto using typeof_env_WellTyped_env.
      eauto using typeof_funcs_WellTyped_funcs.
      consider (exprD funcs uvars vars a t); intros; try reflexivity.
      eapply is_well_typed_correct_only in H1; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs. congruence. }
  Qed.

  Theorem himp_WellTyped_sexpr : forall ts pcT stT funcs (preds : SE.predicates ts pcT stT) cs s vars uvars Q,
    (SE.WellTyped_sexpr (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env uvars) (typeof_env vars) s = true ->
     SE.ST.himp cs (SE.sexprD funcs preds uvars vars s) Q) ->
    SE.ST.himp cs (SE.sexprD funcs preds uvars vars s) Q.
  Proof.
    intros. consider (SE.WellTyped_sexpr (typeof_funcs funcs) (SE.typeof_preds preds)
        (typeof_env uvars) (typeof_env vars) s); intros; auto.
    rewrite himp_not_WellTyped_sexpr; auto.
    rewrite <- SE.ST.heq_star_emp_r.
    eapply SE.ST.himp_star_pure_c; contradiction.
  Qed.

End SepExprFacts.

Module Make (ST' : SepTheoryX.SepTheoryX) <: SepExpr with Module ST := ST'.
  Module ST := ST'.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record predicate := PSig {
      SDomain : list tvar ;
      SDenotation : functionTypeD (map (@tvarD types) SDomain) (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition predicates := list predicate.

    Definition Default_predicate : predicate :=
    {| SDomain := nil
     ; SDenotation := @ST.emp _ _ _
     |} .

    Inductive sexpr : Type :=
    | Emp : sexpr
    | Inj : expr types -> sexpr
    | Star : sexpr -> sexpr -> sexpr
    | Exists : tvar -> sexpr -> sexpr
    | Func : func -> list (expr types) -> sexpr
    | Const : ST.hprop (tvarD types pcType) (tvarD types stateType) nil -> sexpr
    .

    Definition tpredicate : Type := list tvar.
    Definition tpredicates : Type := list tpredicate.

    Definition typeof_pred : predicate -> tpredicate := SDomain.
    Definition typeof_preds : predicates -> tpredicates := map typeof_pred.

    Section types.
      Variable funcs : tfunctions.
      Variable preds : tpredicates.
      Variable tU : tenv.

      Fixpoint WellTyped_sexpr (tG : tenv) (s : sexpr) : bool :=
        match s with
          | Emp => true
          | Inj e => is_well_typed funcs tU tG e tvProp
          | Star l r => WellTyped_sexpr tG l && WellTyped_sexpr tG r
          | Exists t e => WellTyped_sexpr (t :: tG) e
          | Func f args =>
            match nth_error preds f with
              | None => false
              | Some ts => all2 (is_well_typed funcs tU tG) args ts
            end
          | Const _ => true
        end.

    End types.

    Variable funcs : functions types.
    Variable sfuncs : predicates.

    Fixpoint sexprD (meta_env var_env : env types) (s : sexpr)
      : ST.hprop (tvarD types pcType) (tvarD types stateType) nil :=
      match s with
        | Emp => ST.emp _ _
        | Inj p =>
          match exprD funcs meta_env var_env p tvProp with
            | None => ST.inj (PropX.Inj (BadInj p))
            | Some p => ST.inj (PropX.Inj p)
          end
        | Star l r =>
          ST.star (sexprD meta_env var_env l) (sexprD meta_env var_env r)
        | Exists t b =>
          ST.ex (fun x : tvarD types t => sexprD meta_env (@existT _ _ t x :: var_env) b)
        | Func f b =>
          match nth_error sfuncs f with
            | None => ST.inj (PropX.Inj (BadPred f))
            | Some f' =>
              match applyD (@exprD types funcs meta_env var_env) (SDomain f') b _ (SDenotation f') with
                | None => ST.inj (PropX.Inj (BadPredApply f b var_env))
                | Some p => p
              end
          end
        | Const p => p
      end.

    Definition himp (meta_env var_env : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.himp cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

    Definition heq (meta_env var_env : env types)
      (cs : codeSpec (tvarD types pcType) (tvarD types stateType))
      (gl gr : sexpr) : Prop :=
      ST.heq cs (sexprD meta_env var_env gl) (sexprD meta_env var_env gr).

    Fixpoint existsEach (ls : list tvar) {struct ls} : sexpr -> sexpr :=
      match ls with
        | nil => fun x => x
        | t :: ts => fun y => Exists t (@existsEach ts y)
      end.

    Fixpoint liftSExpr ua ub a b s : sexpr :=
      match s with
        | Emp => Emp
        | Const c => Const c
        | Inj p => Inj (liftExpr ua ub a b p)
        | Star l r => Star (liftSExpr ua ub a b l) (liftSExpr ua ub a b r)
        | Exists t s => Exists t (liftSExpr ua ub (S a) b s)
        | Func f args => Func f (map (liftExpr ua ub a b) args)
      end.

  End env.
End Make.
