Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Syntax.
Import String Memory IL SyntaxExpr.
Require Import Bedrock.Platform.Cito.Notations3.
Require Import Bedrock.Platform.Cito.Semantics.
Require Import Bedrock.Platform.Cito.GeneralTactics.
Import SemanticsExpr.

Require Import Bedrock.StringSet.
Import StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.
Require Import Bedrock.Platform.Cito.StringSetTactics.

Definition SET := t.

Ltac openhyp' :=
  repeat match goal with
           | H : context [In_dec ?A ?B] |- _ => destruct (In_dec A B)
           | |- context [In_dec ?A ?B] => destruct (In_dec A B)
           | H : context [ { _ | _ } ] |- _ => destruct H
         end.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Ltac f_equal' :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

Section TopSection.

  Notation "m %%- k" := (remove k m) (at level 60).
  Infix "<=" := Subset : set_scope.
  Infix "+" := union.
  Infix "-" := diff.
  Notation "! x" := (singleton x) (at level 40).
  Notation "[]" := (@empty _).
  Open Scope set_scope.
  Open Scope stmt_scope.
  Infix "<-" := Syntax.Assign.

  Fixpoint used_vars e :=
    match e with
      | Const _ => empty
      | Var x => !x
      | Binop _ a b => used_vars a + used_vars b
      | TestE _ a b => used_vars a + used_vars b
    end.

  Require Import Bedrock.Platform.Cito.Union.

  Fixpoint used_vars_stmt s :=
    match s with
      | skip => empty
      | a ;; b => used_vars_stmt a + used_vars_stmt b
      | Syntax.If e t f => used_vars e + used_vars_stmt t + used_vars_stmt f
      | Syntax.While e body => used_vars e + used_vars_stmt body
      | _ <- e => used_vars e
      | Syntax.Label _ _ => empty
      | Syntax.Call _ f args => used_vars f + union_list (List.map used_vars args)
    end.

  Require Import Bedrock.Platform.Cito.Option.

  Fixpoint elim_dead s used : Stmt * SET :=
    match s with
      | skip => (s, used)
      | a ;; b =>
        let result := elim_dead b used in
        let b := fst result in
        let used := snd result in
        let result := elim_dead a used in
        let a := fst result in
        let used := snd result in
        (a ;; b, used)
      | Syntax.If e t f =>
        let result := elim_dead t used in
        let t := fst result in
        let used_t := snd result in
        let result := elim_dead f used in
        let f := fst result in
        let used_f := snd result in
        (Syntax.If e t f, used_vars e + used_t + used_f)
      | Syntax.While e body =>
        let result := elim_dead body (used + used_vars e + used_vars_stmt body) in
        let body := fst result in
        let used' := snd result in
        (Syntax.While e body, used + used' + used_vars e)
      | x <- e =>
        if In_dec x used then
          (s, used - !x + used_vars e)
        else
          (skip, used)
      | Syntax.Label x _ =>
        (s, used - !x)
      | Syntax.Call x f args =>
        (s, used - (default empty (option_map singleton x)) + used_vars f + union_list (List.map used_vars args))
    end.

  Definition opt s retvar := fst (elim_dead s (!retvar)).

  Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
  Hint Resolve union_subset_1.
  Hint Resolve union_subset_2.
  Hint Resolve diff_subset.

  Definition agree_in a b s := forall x, In x s -> Locals.sel a x = Locals.sel b x.

  Lemma agree_in_symm : forall a b s, agree_in a b s -> agree_in b a s.
    unfold agree_in; intros; symmetry; eauto.
  Qed.

  Hint Resolve agree_in_symm.

  Lemma agree_in_subset : forall a b s s', agree_in a b s -> s' <= s -> agree_in a b s'.
    unfold agree_in, Subset; intros; eauto.
  Qed.

  Hint Resolve agree_in_subset.

  Require Import Bedrock.Platform.Cito.GeneralTactics2.

  Lemma upd_same_agree_in : forall a b s x w, agree_in a b (s - !x) -> agree_in (upd a x w) (upd b x w) s.
    unfold agree_in; intros.
    destruct (string_dec x x0).
    subst.
    repeat rewrite sel_upd_eq; eauto.
    repeat rewrite sel_upd_ne.
    eapply H; eauto.
    eapply diff_iff.
    split; eauto.
    not_not.
    eapply singleton_iff in H1; eauto.
    eauto.
    eauto.
  Qed.

  Hint Resolve upd_same_agree_in.

  Lemma upd_out_agree_in : forall a b s x w, agree_in a b s -> ~ In x s -> agree_in (upd a x w) b s.
    unfold agree_in; intros.
    destruct (string_dec x x0).
    subst; intuition.
    repeat rewrite sel_upd_ne; eauto.
  Qed.

  Hint Resolve upd_out_agree_in.

  Lemma elim_dead_upper_bound :
    forall s used,
      let result := elim_dead s used in
      let used' := snd result in
      used' <= used + used_vars_stmt s.
  Proof.
    induction s; simpl; intros; openhyp'; intuition eauto using subset_trans.
    Grab Existential Variables.
    eapply empty.
  Qed.

  Hint Resolve elim_dead_upper_bound.

  Lemma eval_agree_in : forall e a b, agree_in a b (used_vars e) -> eval a e = eval b e.
    induction e; simpl; intuition.
    eapply H; eapply singleton_iff; eauto.
    f_equal; eauto.
    f_equal'; f_equal; eauto.
  Qed.

  Lemma eval_agree_in_list : forall es a b, agree_in a b (union_list (List.map used_vars es)) -> List.map (eval a) es = List.map (eval b) es.
    induction es; simpl; intuition.
    f_equal.
    eapply eval_agree_in; eauto.
    eauto.
  Qed.

End TopSection.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Require Import Bedrock.Platform.Cito.GoodOptimizer.
  Module Import GoodOptimizerMake := GoodOptimizer.Make E.
  Require Import Bedrock.Platform.Cito.Semantics.
  Import SemanticsMake.

  Section TopSection.

    Hint Unfold RunsTo.
    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe.
    Hint Constructors Semantics.Safe.

    Notation "m %%- k" := (remove k m) (at level 60).
    Infix "<=" := Subset : set_scope.
    Infix "+" := union.
    Infix "-" := diff.
    Notation "! x" := (singleton x) (at level 40).
    Notation "[]" := (@empty _).
    Open Scope set_scope.
    Open Scope stmt_scope.
    Infix "<-" := Syntax.Assign.

    Hint Extern 0 (Subset _ _) => progress (simpl; subset_solver).
    Hint Resolve union_subset_1.
    Hint Resolve union_subset_2.
    Hint Resolve diff_subset.
    Hint Resolve agree_in_symm.
    Hint Resolve agree_in_subset.
    Hint Resolve upd_same_agree_in.
    Hint Resolve upd_out_agree_in.
    Hint Resolve elim_dead_upper_bound.

    Lemma while_case :
      forall fs t v v',
        RunsTo fs t v v' ->
        forall e body used vs,
          let s := Syntax.While e body in
          let result := elim_dead s used in
          let s' := fst result in
          let used' := snd result in
          let vt := fst v in
          let heap := snd v in
          let vt' := fst v' in
          let heap' := snd v' in
          t = s' ->
          agree_in vs vt used' ->
          (
            let s := body in

            forall (used : SET) (vs vt : vals) (heap : Heap)
                   (vt' : vals) (heap' : Heap),
              let result := elim_dead s used in
              let t := fst result in
              let used' := snd result in
              RunsTo fs t (vt, heap) (vt', heap') ->
              agree_in vs vt used' ->
              exists vs' : vals,
                RunsTo fs s (vs, heap) (vs', heap') /\ agree_in vs' vt' used
          ) ->
          exists vs',
            RunsTo fs s (vs, heap) (vs', heap') /\
            agree_in vs' vt' used.
    Proof.
      induction 1; simpl; intros; unfold_all; subst; intuition.

      injection H2; intros; subst.
      destruct v; simpl in *.
      destruct v'; simpl in *.
      eapply H4 in H0; eauto; openhyp.
      destruct v''; simpl in *.
      edestruct IHRunsTo2; try reflexivity.
      2 : eauto.
      eauto using subset_trans.
      openhyp.
      descend.
      econstructor.
      simpl.
      repeat erewrite (@eval_agree_in _ vs w) by eauto.
      eauto.
      eauto.
      eauto.
      eauto.

      injection H0; intros; subst.
      descend.
      eapply RunsToWhileFalse.
      simpl.
      repeat erewrite (@eval_agree_in _ vs (fst v)) by eauto.
      eauto.
      eauto.
    Qed.

    Lemma subset_diff_empty : forall s, s <= s - empty.
      unfold Subset; intros.
      eapply diff_iff; split; eauto.
      nintro.
      eapply empty_iff in H0; intuition.
    Qed.

    Hint Resolve subset_diff_empty.

    Lemma elim_dead_is_bp :
      forall fs s used vs vt heap vt' heap',
        let result := elim_dead s used in
        let t := fst result in
        let used' := snd result in
        RunsTo fs t (vt, heap) (vt', heap') ->
        agree_in vs vt used' ->
        exists vs',
          RunsTo fs s (vs, heap) (vs', heap') /\
          agree_in vs' vt' used.
    Proof.
      induction s; simpl; intros.

      (* skip *)
      inversion H; unfold_all; subst.
      descend.
      eauto.
      eauto.

      (* seq *)
      inversion H; unfold_all; subst.
      destruct v'; simpl in *.
      eapply IHs1 in H3; eauto; openhyp.
      eapply IHs2 in H6; eauto; openhyp.
      descend.
      eauto.
      eauto.

      (* if *)
      inversion H; unfold_all; subst.
      simpl in *.
      eapply IHs1 in H7; eauto; openhyp.
      descend.
      eapply RunsToIfTrue.
      simpl.
      repeat erewrite (@eval_agree_in _ vs vt) by eauto.
      eauto.
      eauto.
      eauto.

      simpl in *.
      eapply IHs2 in H7; eauto; openhyp.
      descend.
      eapply RunsToIfFalse.
      simpl.
      repeat erewrite (@eval_agree_in _ vs vt) by eauto.
      eauto.
      eauto.
      eauto.

      (* while *)
      eapply while_case in H; eauto.

      Focus 3.
      (* assign *)
      openhyp'; simpl in *.
      inversion H; unfold_all; subst.
      descend; intuition.
      econstructor.
      erewrite eval_agree_in by eauto.
      simpl in *; eauto.

      inversion H; unfold_all; subst.
      descend; intuition.
      econstructor.
      simpl in *; eauto.

      (* call *)
      destruct o; simpl in *.
      inversion H; unfold_all; subst; simpl in *.
      descend.
      eapply RunsToCallInternal; simpl in *; eauto.
      repeat erewrite (@eval_agree_in _ vs vt) by eauto.
      eauto.
      repeat erewrite (@eval_agree_in_list _ vs vt) by eauto.
      eauto.
      simpl in *.
      eauto.

      simpl in *.
      descend.
      eapply RunsToCallForeign; simpl in *; eauto.
      repeat erewrite (@eval_agree_in _ vs vt) by eauto.
      eauto.
      repeat erewrite (@eval_agree_in_list _ vs vt) by eauto.
      eauto.
      simpl in *.
      eauto.

      inversion H; unfold_all; subst; simpl in *.
      descend.
      eapply RunsToCallInternal; simpl in *; eauto.
      repeat erewrite (@eval_agree_in _ vs vt) by eauto.
      eauto.
      repeat erewrite (@eval_agree_in_list _ vs vt) by eauto.
      eauto.
      simpl in *.
      eauto.

      simpl in *.
      descend.
      eapply RunsToCallForeign; simpl in *; eauto.
      repeat erewrite (@eval_agree_in _ vs vt) by eauto.
      eauto.
      repeat erewrite (@eval_agree_in_list _ vs vt) by eauto.
      eauto.
      simpl in *.
      eauto.

      (* label *)
      openhyp'; simpl in *.
      inversion H; unfold_all; subst.
      descend; intuition.
      econstructor; eauto.
      simpl in *; eauto.

    Qed.

    Lemma elim_dead_is_sp :
      forall fs s used vs vt heap,
        let result := elim_dead s used in
        let t := fst result in
        let used' := snd result in
        Safe fs s (vs, heap) ->
        agree_in vs vt used' ->
        Safe fs t (vt, heap).
    Proof.
      induction s.

      Focus 4.
      intros.
      unfold_all.
      eapply
        (Safe_coind
           (fun t v =>
              (exists vs c b used,
                 let s := While c b in
                 let result := elim_dead s used in
                 let s' := fst result in
                 let used' := snd result in
                 let vt := fst v in
                 let heap := snd v in
                 Safe fs s (vs, heap) /\
                 agree_in vs vt used' /\
                 (let s := b in
                  forall (used : SET) (vs vt : vals) (heap : Heap),
                    Safe fs s (vs, heap) ->
                    agree_in vs vt (snd (elim_dead s used)) ->
                    Safe fs (fst (elim_dead s used)) (vt, heap)
                 ) /\
                 t = s') \/
              Safe fs t v
        )); [ .. | left; descend; simpl in *; intuition eauto ]; clear; simpl; intros; openhyp.

      (* seq *)
      intuition.

      inversion H; unfold_all; subst; intuition eauto.

      (* if *)
      intuition.

      inversion H; subst.
      unfold_all; openhyp.
      intuition eauto.
      right; intuition eauto.

      (* while *)
      injection H2; intros; subst.
      inversion H; unfold_all; subst.
      destruct v; simpl in *.
      left.
      repeat split.
      repeat erewrite (@eval_agree_in _ v x) by eauto.
      eauto.
      eauto.

      intros.
      left.
      destruct v'; simpl in *.
      eapply elim_dead_is_bp in H3; eauto; openhyp.
      descend.
      4 : eauto.
      eauto.
      eauto using subset_trans.
      eauto.

      simpl in *.
      right.
      destruct v; simpl in *.
      repeat erewrite (@eval_agree_in _ v x) by eauto.
      eauto.

      inversion H; unfold_all; subst.
      intuition eauto.
      right.
      intuition eauto.

      (* call *)
      intuition.

      inversion H; unfold_all; subst; eauto.

      left; descend; intuition eauto.
      right; descend; intuition eauto.

      (* label *)
      intuition.

      inversion H; unfold_all; subst; intuition eauto.

      (* end of while case *)

      (* skip *)
      simpl; intros.
      eauto.

      (* seq *)
      simpl in *; intros.
      inversion H; unfold_all; subst.
      econstructor.
      eapply IHs1; eauto.
      intros.
      destruct v'; simpl in *.
      eapply elim_dead_is_bp in H1; eauto; openhyp.
      eapply IHs2; eauto.

      (* if *)
      simpl in *; intros.
      inversion H; unfold_all; subst.
      openhyp.
      econstructor.
      left.
      split.
      simpl in *.
      repeat erewrite (@eval_agree_in _ vt vs) by eauto.
      eauto.
      eapply IHs1; eauto.

      econstructor.
      right.
      split.
      simpl in *.
      repeat erewrite (@eval_agree_in _ vt vs) by eauto.
      eauto.
      eapply IHs2; eauto.

      Focus 3.
      (* assign *)
      simpl; intros; openhyp'; simpl in *; eauto.

      (* call *)
      simpl; intros.
      inversion H; unfold_all; subst.
      econstructor; simpl in *; eauto.
      repeat erewrite (@eval_agree_in _ vt vs) by eauto.
      eauto.
      repeat erewrite (@eval_agree_in_list _ vt vs) by eauto.
      eauto.

      eapply SafeCallForeign; simpl in *; eauto.
      repeat erewrite (@eval_agree_in _ vt vs) by eauto.
      eauto.
      repeat erewrite (@eval_agree_in_list _ vt vs) by eauto.
      eauto.

      (* label *)
      simpl; intros; openhyp'; simpl in *; eauto.
      inversion_clear H.
      econstructor; eauto.
    Qed.

    Require Import Bedrock.Platform.Cito.FreeVars.

    Lemma elim_dead_footprint : forall s m, free_vars (fst (elim_dead s m)) <= free_vars s.
    Proof.
      induction s; simpl; intros; openhyp'; simpl in *; subset_solver; eauto using subset_trans.
    Qed.

    Open Scope nat.

    Require Import Bedrock.Platform.Cito.Depth.
    Require Import Coq.Arith.Le.
    Require Import Bedrock.Platform.Cito.MaxFacts.

    Hint Extern 0 (le _ _) => progress (simpl; max_solver).
    Hint Resolve both_le le_n_S.

    Lemma elim_dead_depth : forall s m, depth (fst (elim_dead s m)) <= depth s.
    Proof.
      induction s; simpl; intros; openhyp'; simpl in *; max_solver; eauto using le_trans.
    Qed.

    Require Import Bedrock.Platform.Cito.GoodOptimizer.

    Lemma same_agree_in : forall a s, agree_in a a s.
      unfold agree_in; intros; eauto.
    Qed.

    Hint Resolve same_agree_in.

    Lemma agree_in_singleton : forall a b x, agree_in a b (!x) -> sel a x = sel b x.
      intros.
      eapply H.
      eapply singleton_iff; eauto.
    Qed.

    Hint Resolve agree_in_singleton.

    Lemma PreserveRunsTo_opt : PreserveRunsTo opt.
      unfold PreserveRunsTo, opt; intros.
      destruct v.
      destruct v'; simpl in *.
      eapply elim_dead_is_bp in H; openhyp; eauto.
    Qed.

    Lemma PreserveSafe_opt : PreserveSafe opt.
      unfold PreserveSafe, opt; intros.
      destruct v.
      eapply elim_dead_is_sp in H; openhyp; eauto.
    Qed.

    Require Import Bedrock.Platform.Cito.GetLocalVars.
    Require Import Bedrock.Platform.Cito.GetLocalVarsFacts.
    Import NPeano.Nat.

    Lemma PreserveGoodSize_opt : PreserveGoodSize opt.
      unfold PreserveGoodSize, opt; intros.
      eapply goodSize_weaken; eauto.
      eapply add_le_mono.
      2 : eapply elim_dead_depth.
      eapply get_local_vars_cardinal.
      eapply elim_dead_footprint; eauto.
    Qed.

    Require Import Bedrock.Platform.Cito.CompileStmtSpec.
    Require Import Bedrock.Platform.Cito.SetoidListFacts.
    Require Import Bedrock.Platform.Cito.GeneralTactics2.

    Require Import Bedrock.Platform.Cito.WellFormed.

    Hint Constructors args_not_too_long.

    Lemma opt_wellformed : forall s m, wellformed s -> wellformed (fst (elim_dead s m)).
      unfold wellformed.
      induction s; simpl; intuition; openhyp'; inversion_clear H; simpl in *; eauto.
    Qed.

    Lemma PreserveSynReq_opt : PreserveSynReq opt.
      unfold PreserveSynReq, opt; intros.
      unfold syn_req in *.
      unfold in_scope in *.
      openhyp.
      repeat split; eauto.
      eapply get_local_vars_subset; eauto.
      eapply opt_wellformed; eauto.
    Qed.

    Lemma good_optimizer : GoodOptimizer opt.
      unfold GoodOptimizer.
      split.
      eapply PreserveRunsTo_opt.
      split.
      eapply PreserveSafe_opt.
      split.
      eapply PreserveGoodSize_opt.
      eapply PreserveSynReq_opt.
    Qed.

  End TopSection.

End Make.
