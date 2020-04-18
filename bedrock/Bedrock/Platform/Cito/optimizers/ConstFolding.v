Set Implicit Arguments.

Require Import Bedrock.Platform.Cito.Syntax.
Require Import Bedrock.Platform.Cito.SyntaxExpr.
Require Import Bedrock.Platform.Cito.GeneralTactics.
Require Import Bedrock.Platform.Cito.Notations3.
Require Import Bedrock.Platform.Cito.SemanticsExpr.
Require Import Bedrock.Platform.Cito.GoodOptimizer.

Require Import Bedrock.StringSet.
Module Import SS := StringSet.
Require Import Bedrock.Platform.Cito.StringSetFacts.
Module SSF := StringSetFacts.
Require Import Bedrock.Platform.Cito.StringSetTactics.

Require Import Bedrock.Platform.Cito.StringMap.
Import StringMap.
Require Import Bedrock.Platform.Cito.StringMapFacts.

Definition const_dec : forall e, {w | e = Const w} + {~ exists w, e = Const w}.
  intros; destruct e; solve [ right; intuition; openhyp; intuition | left; eauto ].
Qed.

Definition const_zero_dec : forall e, {e = Const $0} + {e <> Const $0}.
  intros; destruct e; solve [right; intuition | destruct (weq w $0); intuition ].
Qed.

Ltac f_equal' :=
  match goal with
    | |- (if ?E1 then _ else _) = (if ?E2 then _ else _) => replace E2 with E1; try reflexivity
  end.

Require Import Bedrock.Platform.Cito.Option.

Ltac openhyp' :=
  repeat match goal with
           | H : context [const_dec ?E] |- _ => destruct (const_dec E)
           | |- context [const_dec ?E] => destruct (const_dec E)
           | H : context [const_zero_dec ?E] |- _ => destruct (const_zero_dec E)
           | |- context [const_zero_dec ?E] => destruct (const_zero_dec E)
           | H : context [option_dec ?E] |- _ => destruct (option_dec E)
           | |- context [option_dec ?E] => destruct (option_dec E)
           | H : context [ { _ | _ } ] |- _ => destruct H
         end.

Ltac descend :=
  repeat match goal with
           | [ |- exists x, _ ] => eexists
         end.

Ltac unfold_all :=
  repeat match goal with
           | H := _ |- _ => unfold H in *; clear H
         end.

Definition SET := SS.t.
Definition Map := t W.
Definition empty_set := SS.empty.
Definition empty_map := empty W.
Definition Submap elt m1 m2 := forall k v, @find elt k m1 = Some v -> find k m2 = Some v.
Definition subtract elt m s := @filter elt (fun k _ => negb (SS.mem k s)) m.

Section TopSection.

  Notation "m %%- k" := (remove k m) (at level 60).
  Infix "%<=" := Subset (at level 60).
  Infix "%%<=" := Submap (at level 60).
  Infix "+" := union.
  Infix "-" := subtract.
  Notation "! x" := (singleton x) (at level 100).
  Notation "[]" := (@empty _).
  Open Scope stmt_scope.
  Infix "<-" := Syntax.Assign.

  Fixpoint const_folding_expr (e : Expr) (env : Map) : Expr :=
    match e with
      | Var var =>
        match option_dec (find var env) with
          | inleft (exist w _) => Const w
          | _ => e
        end
      | Const w => e
      | SyntaxExpr.Binop op a b =>
        let a' := const_folding_expr a env in
        let b' := const_folding_expr b env in
        match const_dec a', const_dec b' with
          | inleft (exist wa _),  inleft (exist wb _) => Const (evalBinop op wa wb)
          | _, _ => SyntaxExpr.Binop op a' b'
        end
      | TestE op a b =>
        let a' := const_folding_expr a env in
        let b' := const_folding_expr b env in
        match const_dec a', const_dec b' with
          | inleft (exist wa _),  inleft (exist wb _) => Const (if evalTest op wa wb then $1 else $0)
          | _, _ => TestE op a' b'
        end
    end.

  Fixpoint const_folding (s : Stmt) (map : Map) : Stmt * Map * SET :=
    match s with
      | skip => (skip, map, empty_set)
      | a ;; b =>
        let result_a := const_folding a map in
        let map' := snd (fst result_a) in
        let result_b := const_folding b map' in
        let a' := fst (fst result_a) in
        let b' := fst (fst result_b) in
        let map'' := snd (fst result_b) in
        let written_a := snd result_a in
        let written_b := snd result_b in
        (a' ;; b', map'', written_a + written_b)
      | Syntax.If c t f =>
        let c' := const_folding_expr c map in
        match const_dec c' with
          | inleft (exist w _) =>
            if wneb w $0 then
              const_folding t map
            else
              const_folding f map
          | inright _ =>
            let result_t := const_folding t map in
            let result_f := const_folding f map in
            let t' := fst (fst result_t) in
            let f' := fst (fst result_f) in
            let written_t := snd result_t in
            let written_f := snd result_f in
            (* written vars in branches will no longer have known values *)
            let map' := map - written_t - written_f in
            (Syntax.If c' t' f', map', written_t + written_f)
        end
      | Syntax.While c b =>
        if const_zero_dec (const_folding_expr c map) then
          (skip, map, empty_set)
        else
          let c' := const_folding_expr c [] in
          let result_b := const_folding b [] in
          let b' := fst (fst result_b) in
          let written_b := snd result_b in
          (* written vars in loop body will no longer have known values *)
          let map' := map - written_b in
          (Syntax.While c' b', map', written_b)
      | x <- e =>
        let e' := const_folding_expr e map in
        match const_dec e' with
          | inleft (exist w _) =>
            let map' := add x w map  in
            (x <- w, map', !x)
          | inright _ =>
            let map' := map %%- x in
            (x <- e', map', !x)
        end
      | Syntax.Label x l =>
        let map := map %%- x in
        (s, map, !x)
      | Syntax.Call x f args =>
        let f' := const_folding_expr f map in
        let args' := List.map (fun e => const_folding_expr e map) args in
        match x with
          | Some s =>
            let map := map %%- s in
            (Syntax.Call x f' args', map, !s)
          | None =>
            (Syntax.Call x f' args', map, empty_set)
        end
    end.

  Definition constant_folding s := fst (fst (const_folding s empty_map)).

  Definition optimizer := constant_folding.

  Definition opt : Optimizer := fun s _ => optimizer s.

  Lemma union_same_subset : forall s, s + s %<= s.
    intros; subset_solver.
  Qed.

  Require Import Bedrock.Platform.Cito.GeneralTactics2.
  Require Import Coq.Bool.Bool.
  Require Import Coq.Classes.Morphisms.

  Lemma subtract_none : forall elt (m : t elt) s x, SS.In x s -> find x (m - s) = None.
    unfold subtract; intros.
    eapply not_find_in_iff.
    nintro.
    eapply In_MapsTo in H0; openhyp.
    eapply filter_iff in H0; openhyp.
    eapply negb_true_iff in H1.
    eapply not_mem_iff in H1; intuition.
    unfold Proper.
    unfold respectful.
    intros; subst; eauto.
  Qed.

  Lemma empty_submap : forall elt (m : t elt), [] %%<= m.
    unfold Submap; intros.
    eapply find_2 in H; eapply empty_mapsto_iff in H; intuition.
  Qed.

  Lemma subtract_submap : forall elt (m : t elt) s, m - s %%<= m.
    unfold subtract, Submap.
    intros.
    eapply find_2 in H.
    eapply filter_iff in H.
    openhyp.
    eapply find_1; eauto.
    unfold Proper.
    unfold respectful.
    intros; subst; eauto.
  Qed.

  Lemma subtract_mapsto_iff : forall elt m s k v, @MapsTo elt k v (m - s) <-> (MapsTo k v m /\ ~ SS.In k s).
    unfold subtract.
    split; intros.
    eapply filter_iff in H.
    openhyp.
    split; eauto.
    eapply negb_true_iff in H0.
    eapply not_mem_iff; eauto.
    unfold Proper.
    unfold respectful.
    intros; subst; eauto.
    openhyp.
    eapply filter_iff.
    unfold Proper.
    unfold respectful.
    intros; subst; eauto.
    split; eauto.
    eapply negb_true_iff.
    eapply not_mem_iff; eauto.
  Qed.

  Section HintsSection.

    Hint Resolve empty_iff.
    Hint Unfold Subset.
    Hint Unfold Submap.
    Hint Resolve subtract_none.
    Hint Resolve singleton_iff.
    Hint Resolve union_subset_1.
    Hint Resolve union_subset_2.
    Hint Immediate subset_refl.
    Hint Resolve union_same_subset.
    Hint Resolve empty_submap.
    Hint Resolve subtract_submap.
    Hint Resolve union_iff union_1 union_2 union_3.

    Definition agree_with (v : vals) (m : Map) :=
      forall x w,
        find x m = Some w ->
        Locals.sel v x = w.

    Lemma agree_with_remove : forall local m x e, agree_with local m -> agree_with (upd local x e) (m %%- x).
      unfold agree_with; intros; destruct (string_dec x x0).
      subst.
      eapply find_2 in H0; eapply remove_mapsto_iff in H0; intuition.
      eapply find_2 in H0; eapply remove_mapsto_iff in H0; openhyp.
      rewrite sel_upd_ne.
      eapply H; eauto.
      eapply find_1; eauto.
      eauto.
    Qed.
    Hint Resolve agree_with_remove.

    Lemma agree_with_add : forall local m x w, agree_with local m -> agree_with (upd local x w) (add x w m).
      unfold agree_with; intros; destruct (string_dec x x0).
      subst.
      rewrite sel_upd_eq in *.
      eapply find_2 in H0; eapply add_mapsto_iff in H0; openhyp; intuition.
      eauto.
      rewrite sel_upd_ne in *.
      eapply H; eauto.
      eapply find_1.
      eapply find_2 in H0; eapply add_mapsto_iff in H0; openhyp; intuition.
      eauto.
    Qed.
    Hint Resolve agree_with_add.

    Lemma everything_agree_with_empty_map : forall v, agree_with v empty_map.
      unfold agree_with.
      intros.
      eapply find_2 in H; eapply empty_mapsto_iff in H.
      intuition.
    Qed.
    Hint Resolve everything_agree_with_empty_map.

    Definition agree_except (a b : vals) (s : SET) :=
      forall x,
        Locals.sel a x <> Locals.sel b x -> SS.In x s.

    Lemma agree_except_upd : forall local x w, agree_except local (upd local x w) (!x).
      unfold agree_except.
      intros.
      destruct (string_dec x x0).
      subst.
      eapply singleton_iff; eauto.
      rewrite sel_upd_ne in H.
      intuition.
      eauto.
    Qed.
    Hint Resolve agree_except_upd.

    Lemma agree_except_same : forall local s, agree_except local local s.
      intuition.
    Qed.
    Hint Resolve agree_except_same.

    Lemma agree_except_incl : forall v1 v2 s s', agree_except v1 v2 s -> s %<= s' -> agree_except v1 v2 s'.
      unfold agree_except; eauto.
    Qed.
    Hint Resolve agree_except_incl.

    Lemma agree_except_trans : forall m1 m2 m3 s1 s2, agree_except m1 m2 s1 -> agree_except m2 m3 s2 -> agree_except m1 m3 (s1 + s2).
      unfold agree_except.
      intros.
      destruct (weq (Locals.sel m1 x) (Locals.sel m2 x)).
      destruct (weq (Locals.sel m2 x) (Locals.sel m3 x)).
      intuition.
      eauto.
      eauto.
    Qed.
    Hint Resolve agree_except_trans.

    Lemma agree_with_agree_except_subtract : forall v1 v2 m s, agree_with v1 m -> agree_except v1 v2 s -> agree_with v2 (m - s).
      unfold agree_with, agree_except.
      intros.
      destruct (weq (Locals.sel v1 x) (Locals.sel v2 x)).
      rewrite <- e.
      eapply H.
      eapply find_2 in H1.
      eapply subtract_mapsto_iff in H1.
      openhyp.
      eapply find_1; eauto.
      eapply H0 in n.
      eapply subtract_none with (m := m) in n.
      erewrite H1 in n.
      intuition.
    Qed.
    Hint Resolve agree_with_agree_except_subtract.

  End HintsSection.

  Hint Resolve union_subset_1.
  Hint Resolve union_subset_2.
  Hint Immediate subset_refl.
  Hint Resolve union_same_subset.
  Hint Resolve empty_submap.
  Hint Resolve subtract_submap.

  Hint Resolve agree_with_remove.
  Hint Resolve agree_with_add.
  Hint Resolve everything_agree_with_empty_map.
  Hint Resolve agree_except_upd.
  Hint Resolve agree_except_same.
  Hint Resolve agree_except_trans.
  Hint Resolve agree_with_agree_except_subtract.
  Hint Resolve agree_except_incl.

  Remove Hints WordKey.W_as_OT.eq_trans.
  Remove Hints WordKey.W_as_OT_new.eq_trans.

  Lemma const_folding_expr_correct :
    forall e m local,
      agree_with local m ->
      eval local (const_folding_expr e m) = eval local e.
  Proof.
    induction e; simpl; intuition; openhyp'; simpl in *; eauto.

    symmetry; eauto.

    f_equal.
    erewrite <- (IHe1 m); eauto.
    erewrite e0; eauto.
    erewrite <- (IHe2 m); eauto.
    erewrite e; eauto.

    f_equal; eauto.

    f_equal; eauto.

    f_equal'; f_equal.
    erewrite <- (IHe1 m); eauto.
    erewrite e0; eauto.
    erewrite <- (IHe2 m); eauto.
    erewrite e; eauto.

    f_equal'; f_equal; eauto.

    f_equal'; f_equal; eauto.
  Qed.

  Lemma const_folding_expr_correct' :
    forall e e' m local,
      e' = const_folding_expr e m ->
      agree_with local m ->
      eval local e' = eval local e.
  Proof.
    intros; subst; eapply const_folding_expr_correct; eauto.
  Qed.

  Lemma const_folding_expr_submap_const : forall e m w, const_folding_expr e m = Const w -> forall m', m %%<= m' -> const_folding_expr e m' = Const w.
    induction e; simpl; intuition; openhyp'; simpl in *; try discriminate.

    eapply H0 in e0.
    rewrite e0 in e.
    injection e; intros; subst.
    eauto.

    eapply H0 in e0.
    rewrite e0 in e.
    discriminate.

    eapply IHe1 in e4; eauto.
    eapply IHe2 in e3; eauto.
    rewrite e0 in e4; injection e4; intros; subst.
    rewrite e in e3; injection e3; intros; subst.
    eauto.

    contradict n.
    descend.
    eauto.

    contradict n.
    descend.
    eauto.

    eapply IHe1 in e4; eauto.
    eapply IHe2 in e3; eauto.
    rewrite e0 in e4; injection e4; intros; subst.
    rewrite e in e3; injection e3; intros; subst.
    eauto.

    contradict n.
    descend.
    eauto.

    contradict n.
    descend.
    eauto.

  Qed.
  Hint Resolve const_folding_expr_submap_const.

  Lemma not_const_zero_submap : forall e m m', const_folding_expr e m <> Const $0 -> m' %%<= m -> const_folding_expr e m' <> Const $0.
    intuition eauto.
  Qed.
  Hint Resolve not_const_zero_submap.

  Lemma not_const_zero_empty_map : forall e m, const_folding_expr e m <> Const $0 -> const_folding_expr e empty_map <> Const $0.
    intros.
    eapply not_const_zero_submap; eauto.
    eapply empty_submap.
  Qed.
  Hint Resolve not_const_zero_empty_map.

  Lemma break_pair : forall A B (p : A * B), p = (fst p, snd p).
    intros; destruct p; eauto.
  Qed.

End TopSection.

Ltac rewrite_expr := repeat erewrite const_folding_expr_correct in * by eauto.

Lemma const_folding_expr_correct_list :
  forall es m local,
    agree_with local m ->
    List.map (fun e => eval local (const_folding_expr e m)) es = List.map (eval local) es.
Proof.
  induction es; simpl; intuition; rewrite_expr; f_equal; eauto.
Qed.

Ltac rewrite_expr_list := repeat erewrite map_map in *; repeat erewrite const_folding_expr_correct_list in * by eauto.

Require Import Bedrock.Platform.Cito.ADT.

Module Make (Import E : ADT).

  Module Import GoodOptimizerMake := GoodOptimizer.Make E.
  Require Import Bedrock.Platform.Cito.Semantics.
  Import SemanticsMake.

  Section TopSection.

    Notation "m %%- k" := (remove k m) (at level 60).
    Infix "%<=" := Subset (at level 60).
    Infix "%%<=" := Submap (at level 60).
    Infix "+" := union.
    Infix "-" := subtract.
    Notation "! x" := (singleton x) (at level 100).
    Notation "[]" := empty_map.
    Open Scope stmt_scope.
    Infix "<-" := Syntax.Assign.

    Hint Resolve union_subset_1.
    Hint Resolve union_subset_2.
    Hint Immediate subset_refl.
    Hint Resolve union_same_subset.
    Hint Resolve empty_submap.
    Hint Resolve subtract_submap.

    Hint Resolve agree_with_remove.
    Hint Resolve agree_with_add.
    Hint Resolve everything_agree_with_empty_map.
    Hint Resolve agree_except_upd.
    Hint Resolve agree_except_same.
    Hint Resolve agree_except_trans.
    Hint Resolve agree_with_agree_except_subtract.
    Hint Resolve agree_except_incl.

    Hint Unfold RunsTo.
    Hint Constructors Semantics.RunsTo.
    Hint Unfold Safe.
    Hint Constructors Semantics.Safe.

    Lemma while_case :
      forall fs t v v',
        RunsTo fs t v v' ->
        forall s c b m,
          let result := const_folding s m in
          let s' := fst (fst result) in
          let m' := snd (fst result) in
          let written := snd result in
          s = Syntax.While c b ->
          t = s' ->
          agree_with (fst v) m ->
          (let s := b in
           (* the induction hypothesis from Lemma const_folding_is_backward_simulation' *)

           forall (vs : vals) (heap : Heap) (vs' : vals)
                  (heap' : Heap) (m : Map),
             let result := const_folding s m in
             let s' := fst (fst result) in
             let m' := snd (fst result) in
             let written := snd result in
             RunsTo fs s' (vs, heap) (vs', heap') ->
             agree_with vs m ->
             RunsTo fs s (vs, heap) (vs', heap') /\
             agree_with vs' m' /\
             agree_except vs vs' written

          ) ->
          RunsTo fs s v v' /\
          agree_with (fst v') m' /\
          agree_except (fst v) (fst v') written.
    Proof.
      induction 1; simpl; intros; unfold_all; subst.

      (* skip *)
      simpl in *; openhyp'; simpl in *; intuition.
      econstructor 6.
      erewrite <- const_folding_expr_correct'.
      2 : symmetry; eauto.
      simpl; eauto.
      simpl; eauto.
      econstructor.

      (* seq *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* seq *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* if *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* if *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* while *)
      simpl in *; openhyp'; simpl in *; try discriminate.
      injection H3; intros; subst.
      destruct v; simpl in *.
      destruct v'; simpl in *.
      eapply H5 in H0; eauto; openhyp.
      destruct v''; simpl in *.
      edestruct IHRunsTo2; try reflexivity.
      3 : eauto.
      replace (While (const_folding_expr c _) (fst (fst (const_folding b _)))) with (fst (fst (const_folding (While c b ) (m - snd (const_folding b []))))).
      Focus 2.
      simpl in *; openhyp'; [contradict e; eauto | simpl; eauto ].
      eapply not_const_zero_submap; eauto.
      eauto.
      eauto.
      openhyp.
      simpl in *; openhyp'; [ contradict e; eauto | ]; simpl in *.
      eapply not_const_zero_submap; eauto.
      rewrite_expr.
      intuition eauto.

      (* while *)
      simpl in *; openhyp'; simpl in *; try discriminate.
      injection H1; intros; subst.
      rewrite_expr.
      intuition eauto.

      (* call *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* call *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* label *)
      simpl in *; openhyp'; simpl in *; intuition.

      (* assign *)
      simpl in *; openhyp'; simpl in *; intuition.

    Qed.

    Lemma const_folding_is_backward_simulation :
      forall fs s vs heap vs' heap' m,
        let result := const_folding s m in
        let s' := fst (fst result) in
        let m' := snd (fst result) in
        let written := snd result in
        RunsTo fs s' (vs, heap) (vs', heap') ->
        agree_with vs m ->
        RunsTo fs s (vs, heap) (vs', heap') /\
        agree_with vs' m' /\
        agree_except vs vs' written.
    Proof.
      induction s;
      match goal with
        | |- context [Syntax.While] => solve [intros; split; intros; eapply while_case in H; eauto; openhyp; eauto]
        | |- _ => idtac
      end; simpl; intros.

      (* skip *)
      inversion H; unfold_all; subst; rewrite_expr; eauto.

      (* seq *)
      inversion H; unfold_all; subst.
      destruct v'; simpl in *.
      eapply IHs1 in H3; eauto; openhyp.
      eapply IHs2 in H6; eauto; openhyp.
      eauto 6.

      (* if *)
      openhyp'.

      destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
      eapply IHs1 in H; eauto; openhyp.
      replace x with (eval vs x) in e1 by eauto.
      rewrite <- e0 in e1.
      rewrite_expr.
      eauto.
      eapply IHs2 in H; eauto; openhyp.
      replace x with (eval vs x) in e1 by eauto.
      rewrite <- e0 in e1.
      rewrite_expr.
      eauto.

      simpl in *.
      inversion H; unfold_all; subst.
      rewrite_expr.
      eapply IHs1 in H7; eauto; openhyp.
      intuition eauto.
      rewrite_expr.
      eapply IHs2 in H7; eauto; openhyp.
      split; [econstructor 4 | ]; eauto.

      Focus 3.
      (* assign *)
      openhyp'; simpl in *; inversion H; unfold_all; subst; simpl in *.
      split.
      replace x with (eval vs x) by eauto.
      rewrite <- e0.
      rewrite_expr.
      econstructor; eauto.
      eauto.

      split.
      rewrite_expr.
      econstructor; eauto.
      eauto.

      (* call *)
      destruct o; openhyp'; simpl in *; inversion H; unfold_all; subst; simpl in *.
      split.
      rewrite_expr.
      rewrite_expr_list.
      specialize RunsToCallInternal; intros.
      simpl in *.
      specialize (H1 _ fs (Some s)).
      simpl in *.
      eapply H1; eauto.
      eauto.

      split.
      rewrite_expr.
      rewrite_expr_list.
      specialize RunsToCallForeign; intros.
      simpl in *.
      specialize (H1 _ fs (Some s)).
      simpl in *.
      eapply H1; eauto.
      eauto.

      split.
      rewrite_expr.
      rewrite_expr_list.
      specialize RunsToCallInternal; intros.
      simpl in *.
      specialize (H1 _ fs None).
      simpl in *.
      eapply H1; eauto.
      eauto.

      split.
      rewrite_expr.
      rewrite_expr_list.
      specialize RunsToCallForeign; intros.
      simpl in *.
      specialize (H1 _ fs None).
      simpl in *.
      eapply H1; eauto.
      eauto.

      (* label *)
      openhyp'; simpl in *; inversion H; unfold_all; subst; simpl in *.
      split.
      rewrite_expr.
      econstructor; eauto.
      eauto.
    Qed.

    Lemma PreserveRunsTo_opt : PreserveRunsTo opt.
      unfold PreserveRunsTo, opt, optimizer, constant_folding; intros.
      destruct v.
      destruct v'; simpl in *.
      eapply const_folding_is_backward_simulation in H; openhyp; eauto.
    Qed.

    Lemma const_folding_is_safety_preservation :
      forall fs s vs heap m,
        let result := const_folding s m in
        let s' := fst (fst result) in
        Safe fs s (vs, heap) ->
        agree_with vs m ->
        Safe fs s' (vs, heap).
    Proof.
      induction s.

      Focus 4.
      intros.
      unfold_all.
      eapply
        (Safe_coind
           (fun s' v =>
              (exists c b m,
                 let s := While c b in
                 Safe fs s v /\
                 agree_with (fst v) m /\
                 (let s := b in
                  forall (vs : vals) (heap : Heap) (m : Map),
                    Safe fs s (vs, heap) ->
                    agree_with vs m -> Safe fs (fst (fst (const_folding s m))) (vs, heap)
                 ) /\
                 s' = fst (fst (const_folding s m))) \/
              Safe fs s' v
        )); [ .. | left; descend; intuition eauto ]; clear; simpl; intros; openhyp.

      (* seq *)
      simpl in *; openhyp'; simpl in *; intuition.

      inversion_clear H.
      intuition eauto.

      (* if *)
      simpl in *; openhyp'; simpl in *; intuition.

      inversion H; subst.
      openhyp.
      intuition eauto.
      right; intuition eauto.

      (* while *)
      simpl in *; openhyp'; simpl in *; intuition.
      injection H2; intros; subst.
      rewrite_expr.
      inversion H; unfold_all; subst.
      destruct v; simpl in *.
      left.
      repeat split.
      eauto.
      right.
      eauto.

      intros.
      left.
      destruct v'; simpl in *.
      eapply const_folding_is_backward_simulation in H3; eauto; openhyp.
      descend; intuition.
      simpl in *; openhyp'; [ contradict e; eauto | ]; simpl in *.
      eapply not_const_zero_empty_map; eauto.
      eauto.

      right.
      eauto.

      inversion H; unfold_all; subst.
      intuition eauto.
      right.
      intuition eauto.

      simpl in *; openhyp'; simpl in *; intuition.

      inversion H; unfold_all; subst.
      left.
      descend.
      intuition eauto.
      right.
      descend.
      intuition eauto.

      simpl in *; openhyp'; simpl in *; intuition.
      inversion_clear H; eauto.

      (* skip *)
      eauto.

      (* seq *)
      simpl; intros; inversion H; unfold_all; subst.
      econstructor.
      simpl in *.
      eapply IHs1; eauto.
      intros.
      destruct v'; simpl in *.
      eapply const_folding_is_backward_simulation in H1.
      openhyp.
      eapply IHs2; eauto.
      eauto.

      (* if *)
      simpl; intros; openhyp'.

      destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
      inversion H; subst.
      unfold_all.
      openhyp.
      eauto.
      erewrite <- const_folding_expr_correct' in H1.
      2 : symmetry; eauto.
      simpl in *.
      intuition.
      eauto.
      inversion H; subst.
      unfold_all.
      openhyp.
      erewrite <- const_folding_expr_correct' in H1.
      2 : symmetry; eauto.
      simpl in *.
      intuition.
      eauto.
      eauto.

      simpl in *.
      inversion H; subst.
      unfold_all.
      openhyp.
      econstructor.
      left.
      rewrite_expr.
      intuition eauto.
      eapply IHs1; eauto.
      econstructor.
      right.
      rewrite_expr.
      intuition eauto.
      eapply IHs2; eauto.

      (* call *)
      destruct o; simpl; intros; inversion H; unfold_all; subst.

      econstructor; rewrite_expr; rewrite_expr_list; eauto.
      rewrite map_length; eauto.

      eapply SafeCallForeign; rewrite_expr; eauto; rewrite_expr_list; eauto.

      econstructor; rewrite_expr; rewrite_expr_list; eauto.
      rewrite map_length; eauto.

      eapply SafeCallForeign; rewrite_expr; eauto; rewrite_expr_list; eauto.

      (* assign *)
      simpl; intros; simpl in *; openhyp'; simpl in *; eauto.

      (* label *)
      simpl; intros; simpl in *; openhyp'; simpl in *; eauto.

    Qed.

    Lemma PreserveSafe_opt : PreserveSafe opt.
      unfold PreserveSafe, opt, optimizer, constant_folding; intros.
      destruct v.
      eapply const_folding_is_safety_preservation in H; openhyp; eauto.
    Qed.

    Require Import Bedrock.Platform.Cito.FreeVarsExpr.

    Lemma const_folding_expr_footprint : forall e m, SS.Subset (free_vars (const_folding_expr e m)) (free_vars e).
    Proof.
      induction e; simpl; intros; openhyp'; simpl in *; subset_solver; eauto using subset_trans.
    Qed.
    Hint Resolve const_folding_expr_footprint.

    Lemma const_folding_expr_footprint_list : forall es m, SS.Subset (Union.union_list (List.map free_vars (List.map (fun e => const_folding_expr e m) es))) (Union.union_list (List.map free_vars es)).
    Proof.
      unfold Union.union_list.
      induction es; simpl; intuition eauto.
      subset_solver; eauto using subset_trans.
    Qed.

    Hint Resolve const_folding_expr_footprint_list.

    Require Import Bedrock.Platform.Cito.FreeVars.

    Lemma const_folding_footprint : forall s m, SS.Subset (free_vars (fst (fst (const_folding s m)))) (free_vars s).
    Proof.
      induction s; simpl; intros; openhyp'; simpl in *; subset_solver.
      eauto using subset_trans.
      eauto using subset_trans.
      destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
      eauto using subset_trans.
      eauto using subset_trans.
      eauto using subset_trans.
      eauto using subset_trans.
      eauto using subset_trans.
      eauto using subset_trans.
      eauto using subset_trans.
      destruct o; simpl in *.
      subset_solver; eauto using subset_trans.
      subset_solver; eauto using subset_trans.
      eauto using subset_trans.
    Qed.

    Lemma optimizer_footprint : forall s, SS.Subset (free_vars (optimizer s)) (free_vars s).
      unfold optimizer, constant_folding; intros; eapply const_folding_footprint.
    Qed.

    Open Scope nat.

    Require Import Coq.Arith.Le.
    Require Import Coq.Arith.Max.
    Require Import Bedrock.Platform.Cito.MaxFacts.

    Hint Resolve both_le Le.le_n_S.

    Require Import Bedrock.Platform.Cito.DepthExpr.

    Lemma const_folding_expr_depth : forall e m, depth (const_folding_expr e m) <= depth e.
    Proof.
      induction e; simpl; intuition; openhyp'; simpl in *; eauto.
    Qed.
    Hint Resolve const_folding_expr_depth.

    Lemma const_folding_expr_depth_list : forall es m, le (Max.max_list 0 (List.map depth (List.map (fun e => const_folding_expr e m) es))) (Max.max_list 0 (List.map depth es)).
    Proof.
      unfold Max.max_list.
      induction es; simpl; intuition eauto.
    Qed.

    Hint Resolve const_folding_expr_depth_list.

    Require Import Bedrock.Platform.Cito.Depth.

    Hint Extern 0 (le _ _) => progress (simpl; max_solver).

    Lemma const_folding_depth : forall s m, depth (fst (fst (const_folding s m))) <= depth s.
    Proof.
      induction s; simpl; intuition; openhyp'; simpl in *; eauto.

      destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *.
      eauto using le_trans.
      eauto using le_trans.
      destruct o; simpl in *.
      max_solver; eauto using le_trans.
      max_solver; eauto using le_trans.
    Qed.

    Lemma optimizer_depth : forall s, depth (optimizer s) <= depth s.
      unfold optimizer, constant_folding; intros; eapply const_folding_depth.
    Qed.

    Import NPeano.Nat.
    Require Import Bedrock.Platform.Cito.GetLocalVars.
    Require Import Bedrock.Platform.Cito.GetLocalVarsFacts.

    Lemma PreserveGoodSize_opt : PreserveGoodSize opt.
      unfold PreserveGoodSize, opt; intros.
      eapply goodSize_weaken; eauto.
      eapply add_le_mono.
      2 : eapply optimizer_depth.
      eapply get_local_vars_cardinal.
      eapply optimizer_footprint; eauto.
    Qed.

    Require Import Bedrock.Platform.Cito.CompileStmtSpec.
    Require Import Bedrock.Platform.Cito.SetoidListFacts.
    Require Import Bedrock.Platform.Cito.GeneralTactics2.

    Require Import Bedrock.Platform.Cito.WellFormed.

    Hint Constructors args_not_too_long.

    Lemma const_folding_wellformed : forall s m, wellformed s -> wellformed (fst (fst (const_folding s m))).
      unfold wellformed.
      induction s; simpl; intuition; openhyp'; inversion_clear H; simpl in *; eauto.
      destruct (Sumbool.sumbool_of_bool (wneb x $0)); rewrite e1 in *; simpl in *; eauto.
      destruct o; simpl in *; eauto; econstructor; eauto; rewrite map_length; eauto.
    Qed.

    Lemma PreserveSynReq_opt : PreserveSynReq opt.
      unfold PreserveSynReq, opt; intros.
      unfold syn_req in *.
      unfold in_scope in *.
      openhyp.
      repeat split; eauto.
      eapply get_local_vars_subset; eauto.
      eapply const_folding_wellformed; eauto.
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
