Require Import Coq.omega.Omega.
Require Import Bedrock.Expr.
Require Import Bedrock.NatMap.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Lists.List Coq.Bool.Bool.
Require Import Bedrock.GenRec.
Require Bedrock.Folds.
Require Import Bedrock.Reflection.

Set Implicit Arguments.
Set Strict Implicit.

(** TODO: factor out [exprInstantiate] **)

Module Type SynUnifier.
  (** An environment that maintains a mapping from variables to their meaning **)
  Parameter Subst : list type -> Type.

  Section typed.
    Variable types : list type.

    (** Predicates **)
    Parameter Subst_WellTyped : tfunctions -> tenv -> tenv -> Subst types -> Prop.

    (** Relations **)
    Parameter Subst_Equal : Subst types -> Subst types -> Prop.
    Parameter Equiv_Subst_Equal : RelationClasses.Equivalence Subst_Equal.

    Parameter Subst_Extends : Subst types -> Subst types -> Prop.

    Parameter Refl_Subst_Extends : RelationClasses.Reflexive Subst_Extends.
    Parameter Antisym_Subst_Extends : @RelationClasses.Antisymmetric _ _ Equiv_Subst_Equal Subst_Extends.
    Parameter Trans_Subst_Extends : RelationClasses.Transitive Subst_Extends.

    (** Operations **)
    Parameter Subst_empty : Subst types.

    Axiom Subst_empty_WellTyped : forall funcs U G,
      Subst_WellTyped funcs U G Subst_empty.

    Parameter Subst_lookup : uvar -> Subst types -> option (expr types).

    Parameter Subst_size : Subst types -> nat.
    Parameter Subst_domain : Subst types -> list uvar.

    (** The actual unification algorithm **)
    Parameter exprUnify : nat -> expr types -> expr types -> Subst types -> option (Subst types).

    (** Substitute meta variables **)
    Parameter exprInstantiate : Subst types -> expr types -> expr types.

    Axiom exprInstantiate_WellTyped : forall funcs U G sub,
      Subst_WellTyped funcs U G sub ->
      forall e t,
        is_well_typed funcs U G e t = is_well_typed funcs U G (exprInstantiate sub e) t.

    Axiom exprInstantiate_Extends : forall x y,
      Subst_Extends x y ->
      forall t, exprInstantiate x (exprInstantiate y t) = exprInstantiate x t.

    Axiom exprInstantiate_instantiated : forall k sub e,
      Subst_lookup k sub = Some e ->
      exprInstantiate sub e = e.

    Axiom exprInstantiate_Removes : forall k sub e e' e'',
      Subst_lookup k sub = Some e ->
      exprInstantiate sub e' = e'' ->
      mentionsU k e'' = false.

    (** The meaning of size **)
    Axiom Subst_domain_iff : forall s k,
      (exists e, Subst_lookup k s = Some e) <-> In k (Subst_domain s).

    Axiom Subst_size_cardinal : forall sub,
      Subst_size sub = length (Subst_domain sub).

    (** Axiomatization of exprInstantiate **)
    Axiom exprInstantiate_Func : forall a b c,
      exprInstantiate a (Func b c) = Func b (map (exprInstantiate a) c).

    Axiom exprInstantiate_Equal : forall a b c d,
      exprInstantiate a (Equal b c d) = Equal b (exprInstantiate a c) (exprInstantiate a d).

    Axiom exprInstantiate_Not : forall a b,
      exprInstantiate a (Not b) = Not (exprInstantiate a b).

    Axiom exprInstantiate_UVar : forall a x,
      exprInstantiate a (UVar x) = match Subst_lookup x a with
                                     | None => UVar x
                                     | Some v => v
                                   end.

    Axiom exprInstantiate_Var : forall a x,
      exprInstantiate a (Var x) = Var x.

    Axiom exprInstantiate_Const : forall a t v,
      exprInstantiate a (@Const types t v) = (@Const types t v).

    (** This is the soundness statement. **)
    Axiom exprUnify_sound : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      exprInstantiate sub' l = exprInstantiate sub' r.

    Axiom exprUnify_Extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      Subst_Extends sub' sub.

    Axiom exprUnify_WellTyped : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
        is_well_typed funcs U G l t = true ->
        is_well_typed funcs U G r t = true ->
        Subst_WellTyped funcs U G sub ->
        Subst_WellTyped funcs U G sub'.

    (** Well-typedness **)
    Axiom WellTyped_lookup : forall funcs U G sub,
      Subst_WellTyped funcs U G sub ->
      forall u e,
      Subst_lookup u sub = Some e ->
      exists t, nth_error U u = Some t /\
      is_well_typed funcs U G e t = true.

    (** Semantics interpretation of substitutions **)
    Parameter Subst_equations :
      forall (funcs : functions types) (U G : env types), Subst types -> Prop.

    Axiom Subst_equations_exprInstantiate : forall funcs U G e t sub,
      Subst_equations funcs U G sub ->
      exprD funcs U G (exprInstantiate sub e) t = exprD funcs U G e t.

    Axiom Subst_equations_Extends : forall funcs G sub sub' U,
      Subst_Extends sub' sub ->
      Subst_equations funcs U G sub' ->
      Subst_equations funcs U G sub.

    Axiom Subst_equations_WellTyped : forall funcs G U sub,
      Subst_equations funcs U G sub ->
      Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub.

    (** An incremental version of Subst_equations **)
    Section Subst_equations_to.
      Variable funcs : functions types.
      Variables uenv venv : env types.
      Variable subst : Subst types.

      Fixpoint Subst_equations_to (from : nat) (ls : Expr.env types) : Prop :=
        match ls with
          | nil => True
          | l :: ls =>
            match Subst_lookup from subst with
              | None => True
              | Some e => match exprD funcs uenv venv e (projT1 l) with
                            | None => False
                            | Some v => projT2 l = v
                          end
            end /\ Subst_equations_to (S from) ls
        end.

      Axiom Subst_equations_to_Subst_equations :
        Subst_WellTyped (typeof_funcs funcs) (typeof_env uenv) (typeof_env venv) subst ->
        Subst_equations_to 0 uenv ->
        Subst_equations funcs uenv venv subst.

    End Subst_equations_to.

  End typed.
End SynUnifier.

Inductive R_expr (ts : list type) : expr ts -> expr ts -> Prop :=
| R_EqualL : forall t l r, R_expr l (Equal t l r)
| R_EqualR : forall t l r, R_expr r (Equal t l r)
| R_Not    : forall e, R_expr e (Not e)
| R_Func   : forall f args arg,
  In arg args -> R_expr arg (Func f args).

Lemma wf_R_expr' ts : well_founded (@R_expr ts).
Proof.
  red; induction a; constructor; inversion 1; try assumption.

  subst. clear H0. generalize dependent y. generalize dependent l. clear.
  induction l; intros; simpl. inversion H3.
  inversion H3. inversion H. rewrite H0 in H4; assumption.
  inversion H; apply IHl; auto.
Defined.

Lemma wf_R_expr ts : well_founded (@R_expr ts).
Proof.
  let v := eval cbv beta iota zeta delta [ wf_R_expr' list_ind list_rec list_rect eq_ind eq_ind_r eq_rect eq_sym expr_ind ] in (@wf_R_expr' ts) in
  exact  v.
Defined.

(** TODO: Really what I want to do is abstract over the functor that creates the map, but I don't know how to do that **)
Module Unifier (E : OrderedType.OrderedType with Definition t := uvar with Definition eq := @eq uvar) <: SynUnifier.
  Module FM := FMapAVL.Make E.

  Remove Hints FM.E.eq_sym FM.E.eq_refl FM.E.eq_trans FM.E.lt_not_eq FM.E.lt_trans
    FM.Raw.Proofs.L.PX.eqk_refl FM.Raw.Proofs.L.PX.eqk_sym
    FM.Raw.Proofs.L.PX.eqk_trans
    FM.Raw.Proofs.PX.eqk_refl FM.Raw.Proofs.PX.eqk_sym FM.Raw.Proofs.PX.eqk_trans
    FM.Raw.Proofs.L.PX.eqke_refl FM.Raw.Proofs.L.PX.eqke_sym FM.Raw.Proofs.L.PX.eqke_trans
    FM.Raw.Proofs.PX.eqke_refl FM.Raw.Proofs.PX.eqke_sym FM.Raw.Proofs.PX.eqke_trans
    FM.Raw.Proofs.L.PX.MO.lt_eq FM.Raw.Proofs.L.PX.MO.eq_lt FM.Raw.Proofs.L.MX.lt_eq
    FM.Raw.Proofs.L.MX.eq_lt FM.Raw.Proofs.PX.MO.lt_eq FM.Raw.Proofs.PX.MO.eq_lt
    FM.Raw.Proofs.MX.lt_eq FM.Raw.Proofs.MX.eq_lt
    FM.Raw.Proofs.L.PX.eqk_ltk FM.Raw.Proofs.L.PX.ltk_eqk FM.Raw.Proofs.L.PX.ltk_trans
    FM.Raw.Proofs.PX.eqk_ltk FM.Raw.Proofs.PX.ltk_eqk FM.Raw.Proofs.PX.ltk_trans
    FM.Raw.Proofs.L.PX.MO.lt_antirefl
    FM.Raw.Proofs.L.MX.lt_antirefl FM.Raw.Proofs.PX.MO.lt_antirefl FM.Raw.Proofs.MX.lt_antirefl
    FM.Raw.Proofs.L.PX.eqk_not_ltk FM.Raw.Proofs.L.PX.ltk_not_eqke
    FM.Raw.Proofs.L.PX.ltk_not_eqk FM.Raw.Proofs.L.PX.MO.lt_not_gt
    FM.Raw.Proofs.L.PX.MO.eq_not_gt FM.Raw.Proofs.L.PX.MO.eq_neq
    FM.Raw.Proofs.L.PX.MO.neq_eq FM.Raw.Proofs.L.PX.MO.eq_le
    FM.Raw.Proofs.L.PX.MO.le_eq FM.Raw.Proofs.L.PX.MO.eq_not_lt
    FM.Raw.Proofs.L.PX.MO.gt_not_eq FM.Raw.Proofs.L.MX.lt_not_gt
    FM.Raw.Proofs.L.MX.eq_not_gt FM.Raw.Proofs.L.MX.eq_neq
    FM.Raw.Proofs.L.MX.neq_eq FM.Raw.Proofs.L.MX.eq_le
    FM.Raw.Proofs.L.MX.le_eq FM.Raw.Proofs.L.MX.eq_not_lt
    FM.Raw.Proofs.L.MX.gt_not_eq FM.Raw.Proofs.PX.eqk_not_ltk
    FM.Raw.Proofs.PX.ltk_not_eqke FM.Raw.Proofs.PX.ltk_not_eqk
    FM.Raw.Proofs.PX.MO.lt_not_gt FM.Raw.Proofs.PX.MO.eq_not_gt
    FM.Raw.Proofs.PX.MO.eq_neq FM.Raw.Proofs.PX.MO.neq_eq
    FM.Raw.Proofs.PX.MO.eq_le FM.Raw.Proofs.PX.MO.le_eq
    FM.Raw.Proofs.PX.MO.eq_not_lt FM.Raw.Proofs.PX.MO.gt_not_eq
    FM.Raw.Proofs.MX.lt_not_gt FM.Raw.Proofs.MX.eq_not_gt
    FM.Raw.Proofs.MX.eq_neq FM.Raw.Proofs.MX.neq_eq
    FM.Raw.Proofs.MX.eq_le FM.Raw.Proofs.MX.le_eq
    FM.Raw.Proofs.MX.eq_not_lt FM.Raw.Proofs.MX.gt_not_eq
    FM.Raw.Proofs.L.PX.Sort_Inf_NotIn FM.Raw.Proofs.PX.Sort_Inf_NotIn
    FM.Raw.Proofs.L.PX.Inf_eq FM.Raw.Proofs.L.PX.MO.Inf_lt
    FM.Raw.Proofs.L.MX.Inf_lt FM.Raw.Proofs.PX.Inf_eq
    FM.Raw.Proofs.PX.MO.Inf_lt FM.Raw.Proofs.MX.Inf_lt
    FM.Raw.Proofs.L.PX.Inf_lt FM.Raw.Proofs.L.PX.MO.Inf_lt
    FM.Raw.Proofs.L.MX.Inf_lt FM.Raw.Proofs.PX.Inf_lt
    FM.Raw.Proofs.PX.MO.Inf_lt FM.Raw.Proofs.MX.Inf_lt
    FM.Raw.InRight FM.Raw.InLeft FM.Raw.InRoot
    FM.Raw.Proofs.L.PX.InA_eqke_eqk FM.Raw.Proofs.L.PX.MO.In_eq
    FM.Raw.Proofs.L.PX.MO.ListIn_In FM.Raw.Proofs.L.MX.In_eq
    FM.Raw.Proofs.L.MX.ListIn_In FM.Raw.Proofs.PX.InA_eqke_eqk
    FM.Raw.Proofs.PX.MO.In_eq FM.Raw.Proofs.PX.MO.ListIn_In
    FM.Raw.Proofs.MX.In_eq FM.Raw.Proofs.MX.ListIn_In
    FM.Raw.Proofs.L.PX.In_inv_3 FM.Raw.Proofs.PX.In_inv_3
    FM.Raw.Proofs.L.PX.In_inv_2 FM.Raw.Proofs.PX.In_inv_2
    FM.Raw.MapsRight FM.Raw.MapsLeft
    FM.Raw.MapsRoot FM.Raw.Proofs.L.PX.MO.Sort_NoDup
    FM.Raw.Proofs.L.MX.Sort_NoDup FM.Raw.Proofs.PX.MO.Sort_NoDup
    FM.Raw.Proofs.MX.Sort_NoDup
    FM.Raw.BSLeaf FM.Raw.BSNode FM.Raw.Leaf FM.Raw.Node.

  Module FACTS := FMapFacts.Facts FM.
  Module MFACTS := NatMap.MoreFMapFacts FM.
  Module PROPS := FMapFacts.Properties FM.

  Section typed.
    Variable types : list type.

    Section Normalization.
      Variable ctx : FM.t (expr types).

      Fixpoint normalized (e : expr types) : bool :=
        match e with
          | Var _
          | Const _ _ => true
          | UVar x => match FM.find x ctx with
                        | None => true
                        | Some _ => false
                      end
          | Not e => normalized e
          | Equal _ e1 e2 => (normalized e1) && (normalized e2)
          | Func _ l =>
            fold_right (fun x acc => acc && (normalized x)) true l
        end.
    End Normalization.

    Definition WellFormed (this : FM.t (expr types)) : Prop :=
      forall k v,
        FM.MapsTo k v this -> normalized this v = true.

    Definition Subst : Type :=
      { this : FM.t (expr types) & WellFormed this }.

    Definition Subst_WellTyped (funcs : tfunctions) (U G : tenv) (s : Subst) : Prop :=
      forall k v, FM.MapsTo k v (projT1 s) ->
        exists t, nth_error U k = Some t /\ is_well_typed funcs U G v t = true.

    Definition subst_empty : FM.t (expr types) := FM.empty _.

    Theorem WF_subst_empty : WellFormed subst_empty.
      red; unfold subst_empty; intros. apply FACTS.empty_mapsto_iff in H. exfalso; auto.
    Defined.

    Definition Subst_empty : Subst :=
      @existT _ _ subst_empty WF_subst_empty.

    Theorem Subst_empty_WellTyped : forall funcs U G,
      Subst_WellTyped funcs U G Subst_empty.
    Proof.
      unfold Subst_WellTyped, Subst_empty, subst_empty; simpl; intros.
      exfalso. apply FACTS.empty_mapsto_iff in H; auto.
    Qed.

    Definition subst_lookup (k : nat) (s : FM.t (expr types)) : option (expr types) :=
      FM.find k s.

    Definition Subst_lookup k (s : Subst) : option (expr types) :=
      subst_lookup k (projT1 s).

    Definition Subst_size (s : Subst) : nat := FM.cardinal (projT1 s).

    Definition Subst_domain (s : Subst) : list uvar :=
      map fst (FM.elements (projT1 s)).

    Theorem Subst_domain_iff : forall s k,
      (exists e, Subst_lookup k s = Some e) <-> In k (Subst_domain s).
    Proof.
      unfold Subst_domain, Subst_lookup, subst_lookup. intros.
      split. intro.
      { destruct H.
        generalize (FACTS.find_mapsto_iff (projT1 s) k x). intros.
        generalize (FACTS.elements_mapsto_iff (projT1 s) k x). intros. intuition.
        change k with (fst (k,x)). eapply in_map. eapply SetoidList.InA_alt in H2. destruct H2.
        destruct H2. destruct x0. inversion H2. simpl in *; subst. auto. }
      { intros. apply in_map_iff in H. destruct H. destruct x; intuition; subst. exists e.
        apply FACTS.find_mapsto_iff. apply FACTS.elements_mapsto_iff.
        eapply SetoidList.InA_alt. exists (k0,e). simpl. intuition auto. reflexivity. }
    Qed.

    Theorem Subst_size_cardinal : forall sub,
      Subst_size sub = length (Subst_domain sub).
    Proof.
      intros. unfold Subst_domain. rewrite map_length. eapply FM.cardinal_1.
    Qed.

    Section Instantiate.
      Variable sub : FM.t (expr types).

      Fixpoint subst_exprInstantiate (e : expr types) : expr types :=
        match e with
          | Const _ _
          | Var _ => e
          | UVar n => match subst_lookup n sub with
                        | None => e
                        | Some v => v
                      end
          | Func f args => Func f (map subst_exprInstantiate args)
          | Equal t l r => Equal t (subst_exprInstantiate l) (subst_exprInstantiate r)
          | Not e => Not (subst_exprInstantiate e)
        end.
    End Instantiate.

    Definition exprInstantiate (sub : Subst) := subst_exprInstantiate (projT1 sub).

    Section Subst_equations.
      Variable funcs : functions types.
      Variables U G : env types.

      Definition Subst_equations (sub : Subst) : Prop :=
        FM.fold (fun k v P =>
          match nth_error U k with
            | None => False
            | Some (existT T val) => match exprD funcs U G v T with
                                       | Some val' => val = val' /\ P
                                       | None => False
                                     end
          end) (projT1 sub) True.

    End Subst_equations.

    Definition Subst_Equal (l r : Subst) : Prop :=
      FM.Equal (projT1 l) (projT1 r).

    Local Ltac think :=
      unfold subst_lookup in *; simpl in *; intros;
      repeat (match goal with
                | [ H : _ && _ = true |- _ ] =>
                  apply andb_true_iff in H; destruct H
                | [ H : _ || _ = false |- _ ] =>
                  apply orb_false_iff in H; destruct H
                | [ H : _ |- _ ] =>
                  rewrite H in * by auto
                | [ H : Some _ = Some _ |- _ ] =>
                  inversion H; clear H; subst
                | [ H : context [ if ?X then _ else _ ] |- _ ] =>
                  consider X; intros; (solve [ try congruence ] || (try congruence; [ ]))
                | [ |- context [ if ?X then _ else _ ] ] =>
                  consider X; intros; (solve [ try congruence ] || (try congruence; [ ]))
                | [ H : ?X = ?X |- _ ] => clear H
                | [ |- _ ] => progress ( simpl in * )
              end
              || rewrite FACTS.add_o in *
              || rewrite FACTS.map_o in *
              || rewrite FACTS.remove_o in *); try congruence.

    Lemma Subst_Equal_extensional : forall l r,
      Subst_Equal l r <->
      forall e, exprInstantiate l e = exprInstantiate r e.
    Proof.
      intros; split.
      { induction e; simpl; think; auto.
          f_equal; induction H0; simpl; think; auto.
      }
      { intros. unfold Subst_Equal.
        red. intros. generalize (H (UVar y)). simpl in *; auto. unfold subst_lookup in *.
        case_eq (FM.find y (projT1 l)); case_eq (FM.find y (projT1 r)); intros; think; auto; exfalso.
        destruct l; simpl in *.
          apply FACTS.find_mapsto_iff in H1.
          generalize (w _ _ H1). simpl.
          apply FACTS.find_mapsto_iff in H1. rewrite H1. congruence.
        destruct r; simpl in *. subst.
          apply FACTS.find_mapsto_iff in H0.
          generalize (w _ _ H0). simpl.
          apply FACTS.find_mapsto_iff in H0. rewrite H0. congruence.
      }
    Qed.

    Definition subst_set (k : nat) (v : expr types) (s : FM.t (expr types))
      : option (FM.t (expr types)) :=
      let v' := subst_exprInstantiate s v in
      if mentionsU k v'
      then None
      else let s := FM.add k v' s in
           let s := FM.map (subst_exprInstantiate s) s in
           Some s.


    Lemma wf_instantiate_normalized : forall s e,
      WellFormed s ->
      normalized s (subst_exprInstantiate s e) = true.
    Proof.
      unfold exprInstantiate. intros. induction e; simpl in *; intros; auto.
        { unfold subst_lookup. case_eq (FM.find x s); intros.
          apply MFACTS.PROPS.F.find_mapsto_iff in H0. eapply H in H0. auto.
          simpl. rewrite H0. auto.
        }
        { induction H0; simpl; auto.
          rewrite IHForall. eauto.
        }
        { rewrite IHe1. rewrite IHe2. auto. }
    Qed.

    Lemma subst_exprInstantiate_add_not_mentions : forall k e e' s,
      mentionsU k e = false ->
      subst_exprInstantiate (FM.add k e' s) e = subst_exprInstantiate s e.
    Proof.
      induction e; simpl; intros; think; auto.
      { f_equal. revert H0. induction H; simpl; intros; think; auto. }
    Qed.

    Lemma normalized_map : forall F s e,
      normalized (FM.map F s) e = normalized s e.
    Proof.
      induction e; simpl; intros; think; auto.
        generalize true. induction H; simpl; intros; think; auto.
    Qed.

    Lemma normalized_add : forall k v s e,
      mentionsU k e = false ->
      normalized (FM.add k v s) e = normalized s e.
    Proof.
      induction e; simpl; intros; think; auto.
        revert H0. induction H; simpl; intros; think;  auto.
    Qed.

    Lemma WellFormed_Canonical : forall s v,
      normalized s v = true ->
        subst_exprInstantiate s v = v.
    Proof.
      induction v; simpl; auto.
        { unfold subst_lookup. destruct (FM.find x s); auto; congruence. }
        { generalize true at 1. intros. f_equal. generalize dependent l.
          induction 1; simpl; intros; auto.
          apply andb_true_iff in H1. intuition. f_equal; eauto. }
        { intros. apply andb_true_iff in H; f_equal; firstorder. }
        { intros; f_equal; auto. }
    Qed.

    Lemma subst_exprInstantiate_idem : forall s e,
      WellFormed s ->
      subst_exprInstantiate s (subst_exprInstantiate s e) = subst_exprInstantiate s e.
    Proof.
      intros. change (subst_exprInstantiate s) with (exprInstantiate (@existT _ _ _ H)).
      induction e; simpl; think; intros; auto.
        case_eq (FM.find x s); intros.
        apply FACTS.find_mapsto_iff in H0. apply H in H0. apply WellFormed_Canonical; auto.
        simpl. unfold subst_lookup. rewrite H0. auto.
        f_equal. induction H0; simpl; intros; think; auto.
    Qed.

    Lemma subst_set_wf : forall k v s s',
      WellFormed s ->
      subst_set k v s = Some s' ->
      WellFormed s'.
    Proof.
      unfold subst_set; intros.
      revert H0; case_eq (mentionsU k (subst_exprInstantiate s v)); try congruence.
      intros; think.

      red. intros. eapply MFACTS.FACTS.map_mapsto_iff in H1. destruct H1. intuition. subst.
      apply MFACTS.PROPS.F.add_mapsto_iff in H3; destruct H3; intuition; subst.
      { rewrite subst_exprInstantiate_add_not_mentions by auto.
        rewrite subst_exprInstantiate_idem by auto.
        rewrite normalized_map. rewrite normalized_add; eauto. eapply wf_instantiate_normalized; auto.
      }
      { rewrite normalized_map.
        apply H in H3. revert H3. induction x; simpl in *; intros; think; auto.
        { subst. rewrite normalized_add; eauto. eapply wf_instantiate_normalized; auto. }
        { revert H3. generalize true at 1 3. induction H1; simpl; intros; think; auto. } }
    Qed.


    Definition Subst_set (k : nat) (v : expr types) (s : Subst) : option Subst :=
      match subst_set k v (projT1 s) as t return subst_set k v (projT1 s) = t -> _ with
        | None => fun _ => None
        | Some s' => fun pf => Some (@existT _ _ s' (@subst_set_wf _ _ _ _ (projT2 s) pf))
      end refl_equal.

    Lemma Subst_set_unroll : forall u E sub sub',
      Subst_set u E sub = Some sub' ->
      mentionsU u (exprInstantiate sub E) = false /\
      projT1 sub' =
        (FM.map
          (subst_exprInstantiate
            (FM.add u (exprInstantiate sub E) (projT1 sub)))
          (FM.add u (exprInstantiate sub E) (projT1 sub))).
    Proof.
      unfold Subst_set. do 4 intro.
      match goal with
        | [ |- context [ eq_refl ?X ] ] => generalize (eq_refl X)
      end.
      simpl in *.
      generalize (subst_set u E (projT1 sub)) at 2 3. destruct o; intros; try congruence.
      unfold subst_set in *.
      inversion H; clear H; subst. simpl in *.
      unfold exprInstantiate.
      destruct (mentionsU u (subst_exprInstantiate (projT1 sub) E)); try congruence.
      inversion e; auto.
    Qed.

(*
    (** s has more mappings **)
    Inductive Subst_Le (s : Subst) : Subst -> Prop :=
    | SE_Refl : Subst_Le s s
    | SE_Add : forall s' s'' k v,
      Subst_set k v s'' = Some s'
      Subst_Le s s' ->
      Subst_Le s s''.
*)

    Definition Subst_Extends (l r : Subst) : Prop :=
      forall k v, FM.MapsTo k v (projT1 r) ->
        FM.MapsTo k (exprInstantiate l v) (projT1 l).

    Theorem Equiv_Subst_Equal : RelationClasses.Equivalence Subst_Equal.
    Proof.
      constructor; unfold Subst_Equal, FM.Equiv; red; intros; subst; eauto.
        reflexivity.
        symmetry; auto.
        etransitivity; eauto.
    Qed.

    Lemma normalized_Lt' : forall s s' v,
      normalized (projT1 s) v = true ->
      Subst_Extends s s' ->
      normalized (projT1 s') v = true.
    Proof.
      induction v; simpl; intros; auto.
      { revert H. case_eq (FM.find x (projT1 s)); intros; try congruence.
        apply FACTS.not_find_in_iff in H.
        cutrewrite (FM.find x (projT1 s') = None); auto.
        apply FACTS.not_find_in_iff. intro. apply H.
        destruct H2. eapply H0 in H2. eexists; eauto. }
      { revert H0; revert H1; generalize true at 1 3; induction H; auto; simpl; intros.
        apply andb_true_iff in H2. apply andb_true_iff. intuition. }
      { apply andb_true_iff. apply andb_true_iff in H. intuition. }
    Qed.

    Lemma exprInstantiate_Extends : forall x y,
      Subst_Extends x y ->
      forall t, exprInstantiate x (exprInstantiate y t) = exprInstantiate x t.
    Proof.
      induction t; simpl; intros; try solve [ auto | f_equal; intuition ].
      { unfold subst_lookup.
        case_eq (FM.find x0 (projT1 y)); intros.
          cutrewrite (FM.find x0 (projT1 x) = Some (exprInstantiate x e)); auto.
          eapply FACTS.find_mapsto_iff. unfold Subst_Extends in *. eapply H.
          eapply FACTS.find_mapsto_iff. auto.

          case_eq (FM.find x0 (projT1 x)); intros; simpl; unfold subst_lookup; rewrite H1; auto. }
      { f_equal. induction H0; simpl; auto.
        f_equal; auto. }
    Qed.

    Lemma normalized_Lt : forall s s' w w' v,
      normalized s' v = true ->
      Subst_Extends (@existT _ _ s' w') (@existT _ _ s w) ->
      normalized s v = true.
    Proof.
      intros. change s with (projT1 (@existT _ _ s w)). eapply normalized_Lt'; eauto.
      simpl. auto.
    Qed.

    Global Instance Refl_Subst_Extends : RelationClasses.Reflexive Subst_Extends.
    Proof.
      red; unfold Subst_Extends; intros. destruct x; simpl in *.
      unfold exprInstantiate in *; simpl in *.
      rewrite WellFormed_Canonical; auto. eapply w; eauto.
    Qed.

    Global Instance Antisym_Subst_Extends : @RelationClasses.Antisymmetric _ _ Equiv_Subst_Equal Subst_Extends.
    Proof.
      red. intros. apply Subst_Equal_extensional. unfold Subst_Extends, Subst_Equal, FM.Equal in *.
      destruct x; destruct y; unfold exprInstantiate in *; simpl in *.
      induction e; simpl;
        repeat match goal with
                 | [ H : _ |- _ ] => rewrite H
               end; auto.
      { unfold subst_lookup.
        case_eq (FM.find x1 x0); intros.
          eapply FACTS.find_mapsto_iff in H1. generalize H1. eapply w0 in H1. eapply normalized_Lt in H1.
            2: instantiate (1 := w). 2: instantiate (1 := w0). 2: unfold Subst_Extends; simpl; auto.
            intros.
            apply H in H2. rewrite WellFormed_Canonical in H2; eauto.
            eapply FACTS.find_mapsto_iff in H2. rewrite H2; reflexivity.

          eapply FACTS.not_find_in_iff in H1.
          assert (~FM.In x1 x).
          intro. apply H1. apply MFACTS.MapsTo_def.
          destruct H2. eapply H0 in H2. eauto.
          apply FACTS.not_find_in_iff in H2. rewrite H2. auto. }
      { f_equal. induction H1; simpl; f_equal; auto. }
    Qed.

    Global Instance Trans_Subst_Extends : RelationClasses.Transitive Subst_Extends.
    Proof.
      red; unfold Subst_Extends; intros.
        eapply H0 in H1. eapply H in H1.
        erewrite exprInstantiate_Extends in H1; auto.
    Qed.



    (** Unification **)
    Section fold_in.
      Variable LS : list (expr types).
      Variable F : forall (l r : expr types), Subst -> In l LS -> option Subst.

      Fixpoint dep_in (ls rs : list (expr types)) (sub : Subst) : (forall l, In l ls -> In l LS) -> option Subst.
      refine (
        match ls as ls , rs as rs return (forall l, In l ls -> In l LS) -> option Subst with
          | nil , nil => fun _ => Some sub
          | l :: ls , r :: rs => fun pf_trans =>
            match F l r sub _ with
              | None => None
              | Some sub => dep_in ls rs sub (fun ls pf => pf_trans _ _)
            end
          | _ , _ => fun _ => None
        end).
        Focus 2.
        refine (or_intror _ pf).
        refine (pf_trans _ (or_introl _ (refl_equal _))).
      Defined.

    End fold_in.

    Definition exprUnify_recursor bound_l
      (recur : forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b bound_l -> expr types -> Subst -> option Subst)
      (r : expr types) (sub : Subst) : option Subst.
    refine (
      match bound_l as bound_l
        return (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b bound_l -> expr types -> Subst -> option Subst)
        -> option Subst
        with
        | (bound,l) =>
          match l as l , r as r
            return (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound, l) -> expr types -> Subst -> option Subst)
            -> option Subst
            with
            | Const t v , Const t' v' => fun _ =>
              match equiv_dec t t' with
                | left pf => match pf in _ = k return tvarD _ k -> _ with
                               | refl_equal => fun v' =>
                                 if get_Eq types t v v'
                                   then Some sub
                                   else None
                             end v'
                | right _ => None
              end
            | Var v , Var v' => fun _ =>
              if Peano_dec.eq_nat_dec v v'
                then Some sub
                else None
            | Func f1 args1 , Func f2 args2 => fun recur =>
              if EqNat.beq_nat f1 f2 then
                @dep_in args1 (fun l r s pf => recur (bound, l) _ r s) args1 args2 sub (fun _ pf => pf)
              else None
            | Equal t1 e1 f1 , Equal t2 e2 f2 => fun recur =>
              if equiv_dec t1 t2 then
                match recur (bound, e1) _ e2 sub with
                  | None => None
                  | Some sub => recur (bound, f1) _ f2 sub
                end
                else
                  None
            | Not e1 , Not e2 => fun recur =>
              recur (bound,e1) _ e2 sub
            | UVar l , UVar r =>
              if EqNat.beq_nat l r then fun _ => Some sub
              else
                match Subst_lookup l sub with
                  | None => fun _ => Subst_set l (UVar r) sub
                  | Some l' =>
                    match Subst_lookup r sub with
                      | None => fun _ => Subst_set r l' sub
                      | Some r' =>
                        match bound as bound return
                          (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,UVar l) -> expr types -> Subst -> option Subst)
                          -> option Subst with
                          | 0 => fun _ => None
                          | S bound => fun recur => recur (bound, l') _ r' sub
                        end
                    end
                end
            | UVar u , _ =>
              match Subst_lookup u sub with
                | None => fun recur =>
                  Subst_set u r sub
                | Some l' =>
                  match bound as bound return
                    (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,UVar u) -> expr types -> Subst -> option Subst)
                    -> option Subst with
                    | 0 => fun _ => None
                    | S bound => fun recur => recur (bound, l') _ r sub
                  end
              end
            | l , UVar u =>
              match Subst_lookup u sub with
                | None => fun recur =>
                  Subst_set u l sub
                | Some r' =>
                  match bound as bound return
                    (forall a_b, R_pair GenRec.R_nat (@R_expr types) a_b (bound,l) -> expr types -> Subst -> option Subst)
                    -> option Subst with
                    | 0 => fun _ => None
                    | S bound => fun recur => recur (bound, l) _ r' sub
                  end
              end
            | _ , _ => fun _ => None
          end
      end recur
    ); try solve [ apply GenRec.L ; constructor | apply GenRec.R ; constructor; assumption ].
    Defined.

    (** index by a bound, since the termination argument is not trivial
     ** it is guaranteed to not make more recursions than the number of
     ** uvars.
     **)
    Definition exprUnify (bound : nat) (l : expr types) : expr types -> Subst -> option Subst :=
      (@Fix _ _ (guard 4 (GenRec.wf_R_pair GenRec.wf_R_nat (@wf_R_expr types)))
        (fun _ => expr types -> Subst -> option Subst) exprUnify_recursor) (bound,l).

    (** Proofs **)
    Section equiv.
      Variable A : Type.
      Variable R : A -> A -> Prop.
      Hypothesis Rwf : well_founded R.
      Variable P : A -> Type.

      Variable equ : forall x, P x -> P x -> Prop.
      Hypothesis equ_Equiv : forall x, RelationClasses.Equivalence (@equ x).

      Variable F : forall x : A, (forall y : A, R y x -> P y) -> P x.

      Lemma Fix_F_equ : forall (x : A) (r : Acc R x),
        equ (@F x (fun (y : A) (p : R y x) => Fix_F P F (Acc_inv r p)))
        (Fix_F P F r).
      Proof.
        eapply Acc_inv_dep; intros.
        simpl in *. reflexivity.
      Qed.

      Lemma Fix_F_inv_equ :
        (forall (x : A) (f g : forall y : A, R y x -> P y),
          (forall (y : A) (p : R y x), equ (@f y p) (g y p)) -> equ (@F x f) (@F x g)) ->
        forall (x : A) (r s : Acc R x), equ (Fix_F P F r) (Fix_F P F s).
      Proof.
        intro. intro. induction (Rwf x). intros.
        erewrite <- Fix_F_equ. symmetry. erewrite <- Fix_F_equ. symmetry.
        eapply H. intros. eauto.
      Qed.

    End equiv.

    Lemma Equiv_equiv : Equivalence
      (fun f g : expr types -> Subst -> option Subst =>
        forall (a : expr types) (b : Subst), f a b = g a b).
    Proof.
      constructor; eauto.
      red. intros. rewrite H; eauto.
    Qed.

    Lemma exprUnify_recursor_inv : forall (bound : nat)
      e1 e2 (sub : Subst) (A B : Acc _ (bound,e1))
      (w : well_founded (R_pair R_nat (R_expr (ts:=types)))),
      Fix_F (fun _ : nat * expr types => expr types -> Subst -> option Subst)
      exprUnify_recursor A e2 sub =
      Fix_F (fun _ : nat * expr types => expr types -> Subst -> option Subst)
      exprUnify_recursor B e2 sub.
    Proof.
      intros.
      eapply (@Fix_F_inv_equ (nat * expr types) (R_pair R_nat (R_expr (ts:=types)))
        w
        (fun _ : nat * expr types => expr types -> Subst -> option Subst)
        (fun x f g => forall a b, f a b = g a b)
        (fun _ => Equiv_equiv)
        exprUnify_recursor).
      clear. intros.
      unfold exprUnify_recursor. destruct x. destruct e; destruct a; auto;
      repeat match goal with
               | _ => reflexivity
               | [ H : _ |- _ ] => rewrite H
               | [ |- context [ match ?X with
                                  | _ => _
                                end ] ] => destruct X
             end.
      generalize (fun (l1 : expr types) (pf : In l1 l) => pf).
      assert (
        forall l' l0 b, forall i : forall l1 : expr types, In l1 l' -> In l1 l,
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            f (n, l1)
            (R R_nat (R_expr (ts:=types)) n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i =
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            g (n, l1)
            (R R_nat (R_expr (ts:=types)) n l1 (Func f0 l) (R_Func f0 l l1 pf))
            r0 s) l' l0 b i).
      induction l'; simpl in *; intros; auto.
      destruct l1; auto.
      rewrite H. destruct (g (n, a)); auto.
      eapply H0.
    Qed.

    Theorem exprUnify_unroll : forall bound l r sub,
      exprUnify bound l r sub =
      match l , r with
        | Const t v , Const t' v' =>
          match equiv_dec t t' with
            | left pf => match pf in _ = k return tvarD _ k -> _ with
                           | refl_equal => fun v' =>
                             if get_Eq types t v v'
                               then Some sub
                               else None
                         end v'
            | right _ => None
          end
        | Var v , Var v' =>
          if Peano_dec.eq_nat_dec v v'
            then Some sub
            else None
        | Func f1 args1 , Func f2 args2 =>
          if EqNat.beq_nat f1 f2 then
            Folds.fold_left_2_opt (@exprUnify bound) args1 args2 sub
          else None
        | Equal t1 e1 f1 , Equal t2 e2 f2 =>
          if equiv_dec t1 t2 then
            match exprUnify bound e1 e2 sub with
              | None => None
              | Some sub => exprUnify bound f1 f2 sub
            end
            else
              None
        | Not e1, Not e2 =>
          exprUnify bound e1 e2 sub
        | UVar l , UVar r =>
          if EqNat.beq_nat l r then Some sub
            else
              match Subst_lookup l sub with
                | None => Subst_set l (UVar r) sub
                | Some l' =>
                  match Subst_lookup r sub with
                    | None => Subst_set r l' sub
                    | Some r' =>
                      match bound with
                        | 0 => None
                        | S bound => exprUnify bound l' r' sub
                      end
                  end
              end
        | UVar u , _ =>
          match Subst_lookup u sub with
            | None => Subst_set u r sub
            | Some l' =>
              match bound with
                | 0 => None
                | S bound => exprUnify bound l' r sub
              end
          end
        | l , UVar u =>
          match Subst_lookup u sub with
            | None => Subst_set u l sub
            | Some r' =>
              match bound with
                | 0 => None
                | S bound => exprUnify bound l r' sub
              end
          end
        | _ , _ => None
      end.
    Proof.
      intros. unfold exprUnify at 1.
      match goal with
        | [ |- context [ guard ?X ?Y ] ] =>
          generalize (guard X Y)
      end.
      intros. unfold Fix.
      rewrite <- (@Fix_F_equ (nat * expr types) (R_pair R_nat (R_expr (ts:=types)))
        (fun _ : nat * expr types => expr types -> Subst -> option Subst)
        (fun x f g => forall a b, f a b = g a b)
        (fun _ => Equiv_equiv)
        exprUnify_recursor
        (bound,l)
        (w (bound,l))
        r sub).
      destruct l; destruct r; simpl; intros; auto;
        try solve [
          repeat match goal with
                   | [ |- context [ match ?X with
                                      | _ => _
                                    end ] ] => destruct X
                 end; try solve [ auto |
                   unfold exprUnify, Fix ;
                     eapply exprUnify_recursor_inv; eauto ] ].
      Focus 2.
      destruct (equiv_dec t t0); auto.
      unfold exprUnify, Fix.
      erewrite exprUnify_recursor_inv; eauto.
      instantiate (1 := (guard 4 (wf_R_pair wf_R_nat (wf_R_expr (ts:=types))) (bound, l1))).
      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X
      end; auto.
      erewrite exprUnify_recursor_inv; eauto.

      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X; auto
      end.
      generalize (fun (l1 : expr types) (pf : In l1 l) => pf).
      assert (forall l' l0 sub,
        forall i : (forall l1 : expr types, In l1 l' -> In l1 l),
          dep_in l
          (fun (l1 r0 : expr types) (s : Subst) (pf : In l1 l) =>
            @Fix_F _ _ (fun _ : nat * expr types => expr types -> Subst -> option Subst)
            exprUnify_recursor (bound, l1) (@Acc_inv (nat * expr types)
              (@R_pair nat (expr types) R_nat (@R_expr types))
              (bound, @Func types f l) (w (bound, @Func types f l))
              (bound, l1)
              (@R nat (expr types) R_nat (@R_expr types) bound l1
                (@Func types f l) (@R_Func types f l l1 pf))) r0 s) l' l0 sub i =
          Folds.fold_left_2_opt (exprUnify bound) l' l0 sub).
      induction l'; simpl; intros; destruct l1; auto.
      erewrite exprUnify_recursor_inv; eauto.
      instantiate (1 := (guard 4 (wf_R_pair wf_R_nat (wf_R_expr (ts:=types))) (bound, a))).
      unfold exprUnify, Fix.
      match goal with
        | [ |- match ?X with
                 | _ => _
               end = _ ] => destruct X; auto
      end.
      eapply H.
    Qed.

    Lemma Subst_set_Subst_lookup : forall k v sub sub',
      Subst_set k v sub = Some sub' ->
      Subst_lookup k sub' = Some (exprInstantiate sub v).
    Proof.
      intros. unfold Subst_lookup; apply Subst_set_unroll in H; intuition; think.
      destruct (FM.E.eq_dec k k); try congruence. simpl.
      f_equal. clear e. rewrite subst_exprInstantiate_add_not_mentions; auto.
      unfold exprInstantiate. rewrite subst_exprInstantiate_idem; auto. destruct sub; auto.
    Qed.

    Lemma adf : forall (k : nat) (v : expr types) (x : FM.t (expr types))
     (k0 : FM.key) (v0 : expr types),
     mentionsU k (subst_exprInstantiate x v) = false ->
     ~ FM.E.eq k k0 ->
     normalized x v0 = true ->
     WellFormed x ->
     subst_exprInstantiate
     (FM.map (subst_exprInstantiate (FM.add k (subst_exprInstantiate x v) x))
       (FM.add k (subst_exprInstantiate x v) x)) v0 =
     subst_exprInstantiate (FM.add k (subst_exprInstantiate x v) x) v0.
    Proof.
      induction v0; simpl; intros; think; auto.
      { repeat rewrite FACTS.map_o. repeat rewrite FACTS.add_o.
        rewrite subst_exprInstantiate_add_not_mentions; eauto.
        rewrite subst_exprInstantiate_idem; auto. }
      { f_equal. induction H; simpl; intros; think; auto. }
    Qed.


    Lemma Subst_set_Extends : forall k v sub sub',
      Subst_set k v sub = Some sub' ->
      Subst_lookup k sub = None ->
      Subst_Extends sub' sub.
    Proof.
      intros. generalize (Subst_set_Subst_lookup _ _ _ H).
      unfold Subst_set in *; simpl; intros.
      revert H.
      match goal with
        | [ |- context [ eq_refl ?X ] ] => generalize (eq_refl X)
      end.
      generalize (subst_set k v (projT1 sub)) at 2 3. intro.
      destruct o; intros; try congruence.
        inversion H; clear H; subst.
        destruct sub. unfold Subst_Extends, Subst_lookup, subst_set, exprInstantiate in *; simpl in *.
        revert e. case_eq (mentionsU k (subst_exprInstantiate x v)); intros; try congruence.
        think. apply FACTS.map_mapsto_iff. case_eq (FM.E.eq_dec k k0); intros.
          rewrite e in H0. exfalso. eapply FACTS.not_find_in_iff in H0. eapply H0. eexists. eapply H2.

          exists v0. split.
          2: eapply FACTS.add_mapsto_iff; right; split; eauto.

          eapply adf; eauto.
    Qed.

    Lemma fold_left_2_opt_exprUnify_Extends' : forall b l l0 sub sub',
      Folds.fold_left_2_opt (exprUnify b) l l0 sub = Some sub' ->
      Forall
      (fun l : expr types =>
        forall (r : expr types) (sub sub' : Subst),
          exprUnify b l r sub = Some sub' -> Subst_Extends sub' sub) l ->
      Subst_Extends sub' sub.
    Proof.
      intros.
      generalize dependent l0. generalize dependent sub.
      induction H0; destruct l0; simpl in *; try congruence; intros.
        inversion H; eapply Refl_Subst_Extends.

      revert H1; case_eq (exprUnify b x e sub); try congruence; intros.
      eapply Trans_Subst_Extends; eauto.
    Qed.

    Theorem exprUnify_Extends : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      Subst_Extends sub' sub.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; destruct r; simpl in *;
        try solve [
          repeat (congruence || eauto ||
              solve [ eapply Subst_set_Extends; eauto |
                      eapply Trans_Subst_Extends; eauto |
                      apply Refl_Subst_Extends |
                  eapply fold_left_2_opt_exprUnify_Extends'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] =>
                  unfold Equivalence.equiv in H; subst
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] => revert H; case_eq X; intros
              end) ].
    Qed.

    Lemma fold_left_2_opt_exprUnify_Extends : forall b l l0 sub sub',
      Folds.fold_left_2_opt (exprUnify b) l l0 sub = Some sub' ->
      Subst_Extends sub' sub.
    Proof.
      induction l; destruct l0; simpl in *; try congruence; intros.
        inversion H; subst; apply Refl_Subst_Extends.
      revert H; case_eq (exprUnify b a e sub); try congruence; intros.
      eapply Trans_Subst_Extends; eauto using exprUnify_Extends.
    Qed.

    Lemma Subst_lookup_Extends : forall sub sub' k v,
      Subst_lookup k sub = Some v ->
      Subst_Extends sub' sub ->
      Subst_lookup k sub' = Some (exprInstantiate sub' v).
    Proof.
      intros. unfold Subst_lookup, Subst_Extends, Subst_lookup, exprInstantiate in *.
      destruct sub; destruct sub'; simpl in *.
      unfold subst_lookup in *.
      eapply FACTS.find_mapsto_iff in H. eapply H0 in H. eapply FACTS.find_mapsto_iff in H. auto.
    Qed.

    Lemma exprInstantiate_extends : forall sub sub' l r,
      exprInstantiate sub l = exprInstantiate sub r ->
      Subst_Extends sub' sub ->
      exprInstantiate sub' l = exprInstantiate sub' r.
    Proof.
      intros.
      cut (exprInstantiate sub' (exprInstantiate sub l) = exprInstantiate sub' (exprInstantiate sub r)); intros.
      repeat (rewrite exprInstantiate_Extends in H1; eauto). rewrite H; reflexivity.
    Qed.

    Lemma fold_left_2_opt_map_sound' : forall (n : nat) (l l0 : list (expr types)) (sub sub' : Subst),
      Folds.fold_left_2_opt (exprUnify n) l l0 sub = Some sub' ->
      Forall
      (fun l1 : expr types =>
        forall (r : expr types) (sub0 sub'0 : Subst),
          exprUnify n l1 r sub0 = Some sub'0 ->
          exprInstantiate sub'0 l1 = exprInstantiate sub'0 r) l ->
      map (exprInstantiate sub') l = map (exprInstantiate sub') l0.
    Proof.
      intros.
      generalize dependent l0. revert sub; revert sub'.
      induction H0; simpl in *; intros; destruct l0; simpl in *; try congruence; auto.
      revert H1. case_eq (exprUnify n x e sub); intros; try congruence.
      f_equal; eauto using exprInstantiate_extends, exprUnify_Extends, fold_left_2_opt_exprUnify_Extends.
    Qed.

    Lemma Subst_set_exprInstantiate : forall x e sub sub',
      Subst_set x e sub = Some sub' ->
      Subst_lookup x sub = None ->
      exprInstantiate sub' (UVar x) = exprInstantiate sub' e.
    Proof.
      unfold Subst_set, Subst_lookup, exprInstantiate; simpl; intros;
        destruct sub; destruct sub'; simpl in *; auto.
      revert H.
      match goal with
        | [ |- context [ @eq_refl _ ?X ] ] =>
          generalize (@eq_refl _ X)
      end.
      generalize (subst_set x e x0) at 2 3.
      intro. destruct o; intros; try congruence.
      think. unfold subst_lookup, subst_set in *.
      revert e0. case_eq (mentionsU x (subst_exprInstantiate x0 e)); intros; try congruence.
      think.
      destruct (FM.E.eq_dec x x); try solve [ exfalso; eauto ].
      clear e0. simpl.

      revert H; revert w0.
      generalize (subst_exprInstantiate x0 e) at 1 2 4 6 7.
      induction e; simpl; intros; think; auto.
      { consider (FM.find x1 x0); simpl; intros; auto.
        consider (EqNat.beq_nat x x1); try congruence; intros.
        unfold subst_lookup. rewrite FACTS.add_o.
        destruct (FM.E.eq_dec x x1); [ exfalso; auto | ].
        rewrite H. auto. }
      { f_equal.
        induction H; simpl; intros; think; auto. }
    Qed.

    Lemma exprInstantiate_Func : forall a b c,
      exprInstantiate a (Func b c) = Func b (map (exprInstantiate a) c).
    Proof. reflexivity. Qed.
    Lemma exprInstantiate_Equal : forall a b c d,
      exprInstantiate a (Equal b c d) = Equal b (exprInstantiate a c) (exprInstantiate a d).
    Proof. reflexivity. Qed.
    Lemma exprInstantiate_Not : forall a b,
      exprInstantiate a (Not b) = Not (exprInstantiate a b).
    Proof. reflexivity. Qed.
    Lemma exprInstantiate_UVar : forall a x,
      exprInstantiate a (UVar x) = match Subst_lookup x a with
                                     | None => UVar x
                                     | Some v => v
                                   end.
    Proof. reflexivity. Qed.
    Lemma exprInstantiate_Var : forall a x,
      exprInstantiate a (Var x) = Var x.
    Proof. reflexivity. Qed.
    Lemma exprInstantiate_Const : forall a t v,
      exprInstantiate a (@Const types t v) = (@Const types t v).
    Proof. reflexivity. Qed.

    Hint Rewrite exprInstantiate_Func exprInstantiate_Equal exprInstantiate_Not
      exprInstantiate_UVar exprInstantiate_Var exprInstantiate_Const : subst_simpl.

    Theorem exprInstantiate_WellTyped : forall funcs U G sub,
      Subst_WellTyped funcs U G sub ->
      forall e t,
        is_well_typed funcs U G e t = is_well_typed funcs U G (exprInstantiate sub e) t.
    Proof.
      unfold exprInstantiate, Subst_WellTyped; induction e; simpl; intros; eauto;
      repeat (match goal with
                | [ |- context [ FM.find ?X ?Y ] ] =>
                  case_eq (FM.find X Y); intros
                | [ |- context [ nth_error ?X ?Y ] ] =>
                  case_eq (nth_error X Y); intros
                | [ |- context [ equiv_dec ?X ?Y ] ] =>
                  destruct (equiv_dec X Y); intros; unfold equiv in *; try subst
                | [ |- _ ] => progress (unfold subst_lookup || simpl in *)
                | [ H : FM.find _ _ = _ |- _ ] =>
                  eapply FACTS.find_mapsto_iff in H
                | [ H : ?X = _ , H' : ?X = _ |- _ ] =>
                  rewrite H in H'
                | [ H : exists x, _ |- _ ] => destruct H
                | [ H : _ /\ _ |- _ ] => destruct H
                | [ |- context [ match ?X with | _ => _ end ] ] =>
                  solve [ consider X; try congruence ] || ((consider X; try congruence; auto); [ ])
                | [ H : forall k v, FM.MapsTo k v _ -> _ , H' : FM.MapsTo _ _ _ |- _ ] => apply H in H'
                | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
              end); try solve [ auto | congruence | symmetry; eapply H; eauto using FACTS.find_mapsto_iff ].
      symmetry. eapply is_well_typed_only; eauto.

      intros. generalize dependent (TDomain t0). clear H1. clear - H0.
      induction H0; simpl. reflexivity.
      destruct l0; auto; simpl in *.
      rewrite <- IHForall. rewrite <- H. reflexivity.
    Qed.

    Opaque Subst_lookup Subst_set exprInstantiate.

    Theorem exprUnify_sound : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      exprInstantiate sub' l = exprInstantiate sub' r.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; destruct r; simpl in *;
        try solve [
          repeat (congruence ||
                  solve [ eauto |
                          eapply exprInstantiate_extends; eauto using exprUnify_Extends |
                          eapply fold_left_2_opt_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] =>
                  unfold Equivalence.equiv in H; subst
                | [ |- _ ] => erewrite Subst_set_exprInstantiate by eauto
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite Subst_set_Subst_lookup by eauto
                | [ H : forall (l r : expr types) (sub sub' : Subst), exprUnify _ l r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ _ H')
                | [ H : Subst_lookup _ _ = _ |- _ ] =>
                  eapply Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_Extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] =>
                  revert H; Reflection.consider X; intros
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
                | [ |- _ ] =>
                  rewrite exprInstantiate_Func || rewrite exprInstantiate_Equal ||
                  rewrite exprInstantiate_Not || rewrite exprInstantiate_UVar ||
                  rewrite exprInstantiate_Var || rewrite exprInstantiate_Const
              end) ].
      { repeat (congruence ||
                  solve [ eauto |
                          eapply exprInstantiate_extends; eauto using exprUnify_Extends |
                          eapply fold_left_2_opt_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] =>
                  unfold Equivalence.equiv in H; subst
                | [ |- _ ] => erewrite Subst_set_exprInstantiate by eauto
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite Subst_set_Subst_lookup by eauto
                | [ H : forall (l r : expr types) (sub sub' : Subst), exprUnify _ l r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ _ H')
                | [ H : Subst_lookup _ _ = _ |- _ ] =>
                  eapply Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_Extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] =>
                  revert H; Reflection.consider X; intros
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
                | [ |- _ ] =>
                  rewrite exprInstantiate_Func || rewrite exprInstantiate_Equal ||
                  rewrite exprInstantiate_Not || rewrite exprInstantiate_UVar ||
                  rewrite exprInstantiate_Var || rewrite exprInstantiate_Const
              end).
        eapply Subst_set_Extends in H2; try eassumption.
        erewrite Subst_lookup_Extends; try eassumption.
        reflexivity. }
      { repeat (congruence ||
                  solve [ eauto |
                          eapply exprInstantiate_extends; eauto using exprUnify_Extends |
                          eapply fold_left_2_opt_map_sound'; eauto ] ||
              match goal with
                | [ H : Equivalence.equiv _ _ |- _ ] =>
                  unfold Equivalence.equiv in H; subst
                | [ |- _ ] => erewrite Subst_set_exprInstantiate by eauto
                | [ H : _ |- _ ] => erewrite H by eauto
                | [ |- _ ] => erewrite Subst_set_Subst_lookup by eauto
                | [ H : forall (l r : expr types) (sub sub' : Subst), exprUnify _ l r sub = Some sub' -> _ , H' : _ |- _ ] =>
                  specialize (@H _ _ _ _ H')
                | [ H : Subst_lookup _ _ = _ |- _ ] =>
                  eapply Subst_lookup_Extends in H; [ | solve [ eauto using exprUnify_Extends ] ]
                | [ H : match exprUnify ?A ?B ?C ?D with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (exprUnify A B C D); intros
                | [ H : match Subst_lookup ?X ?Y with _ => _ end = _ |- _ ] =>
                  revert H; case_eq (Subst_lookup X Y); intros
                | [ H : match ?X with _ => _ end = _ |- _ ] =>
                  revert H; Reflection.consider X; intros
                | [ |- Equal _ _ _ = Equal _ _ _ ] => f_equal
                | [ |- Func _ _ = Func _ _ ] => f_equal
                | [ |- _ ] =>
                  rewrite exprInstantiate_Func || rewrite exprInstantiate_Equal ||
                  rewrite exprInstantiate_Not || rewrite exprInstantiate_UVar ||
                  rewrite exprInstantiate_Var || rewrite exprInstantiate_Const
              end).
        eapply Subst_set_Extends in H2; try eassumption.
        erewrite Subst_lookup_Extends; try eassumption.
        reflexivity. }
    Qed.

    Transparent Subst_set.

    Lemma Subst_set_WellTyped : forall funcs U G u E t sub sub',
      Subst_set u E sub = Some sub' ->
      nth_error U u = Some t ->
      is_well_typed funcs U G E t = true ->
      Subst_WellTyped funcs U G sub ->
      Subst_WellTyped funcs U G sub'.
    Proof.
      intros. apply Subst_set_unroll in H; intuition.
      unfold Subst_WellTyped in *. rewrite H4. clear H4. clear sub'.
      destruct sub; simpl in *. intros. eapply FACTS.map_mapsto_iff in H. destruct H. intuition; subst.
      eapply FACTS.add_mapsto_iff in H5. destruct H5.
      { intuition. subst. eexists; split; eauto.
        rewrite subst_exprInstantiate_add_not_mentions; eauto.
        Transparent exprInstantiate. unfold exprInstantiate. rewrite subst_exprInstantiate_idem; eauto.
        simpl. change (subst_exprInstantiate x E) with (exprInstantiate (@existT _ _ _ w) E).
        rewrite <- exprInstantiate_WellTyped; eauto. }
      { intuition. eapply H2 in H5. destruct H5; intuition. eexists. split; eauto.
        revert H6. clear H5. clear H4. clear H3. revert x1.
        induction x0; simpl; intros; think;
        repeat (progress simpl ||
          match goal with
            | [ H : _ = _ |- _ ] => rewrite H in *
            | [ H : equiv _ _ |- _ ] => unfold equiv in H; subst; try congruence
            | [ H : context [ match ?X with
                                | _ => _
                              end ] |- _ ] =>
            revert H; consider X; intros
            | [ |- context [ FM.E.eq_dec ?X ?Y ] ] => destruct (FM.E.eq_dec X Y); subst
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
            | [ |- _ ] => rewrite <- exprInstantiate_WellTyped by assumption
            | [ |- context [ FM.find ?X ?Y ] ] =>
              case_eq (FM.find X Y); intros; try congruence
            | [ H : FM.find _ _ = Some _ |- _ ] =>
              apply FACTS.find_mapsto_iff in H
            | [ H : forall x y, FM.MapsTo x y ?X -> _ , H' : FM.MapsTo _ _ ?X |- _ ] =>
              apply H in H'
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ ] => apply andb_true_iff; split
          end); auto; try congruence.
        consider (tvar_seqb t0 t0); eauto.
        destruct t0; simpl in *. revert H5; clear -H. revert TDomain. induction H; simpl; destruct TDomain; auto.
        case_eq (is_well_typed funcs U G x0 t); intros; try congruence.
        rewrite H; eauto. }
    Qed.

    Lemma Subst_lookup_WellTyped : forall funcs U G e u sub t,
      Subst_lookup u sub = Some e ->
      Subst_WellTyped funcs U G sub ->
      nth_error U u = Some t ->
      is_well_typed funcs U G e t = true.
    Proof.
      Transparent Subst_lookup.
      unfold Subst_WellTyped, Subst_lookup, subst_lookup. intros.
      apply FACTS.find_mapsto_iff in H. eapply H0 in H. destruct H. rewrite H1 in *. intuition.
      inversion H2; auto.
    Qed.
    Opaque Subst_lookup.

(*    SearchAbout is_well_typed.

    Lemma is_well_typed_const : forall funcs U G t (v : tvarD types t),
      is_well_typed funcs U G (Const v) t = true.
    Proof.
      simpl. intros. consider (tvar_seqb t t); auto.
    Qed.
    Lemma is_well_typed_var : forall funcs U G t v,
      nth_error G v = Some t ->
      is_well_typed funcs U G (@Var types v) t = true.
    Proof.
      simpl. intros; rewrite H. consider (tvar_seqb t t); auto.
    Qed.
    Lemma is_well_typed_uvar : forall funcs U G t v,
      nth_error U v = Some t ->
      is_well_typed funcs U G (@UVar types v) t = true.
    Proof.
      simpl. intros; rewrite H. consider (tvar_seqb t t); auto.
    Qed.
*)

    Hint Extern 1 (is_well_typed _ _ _ _ _ = _) =>
      simpl;
        repeat match goal with
                 | [ H : _ = _ |- _ ] => rewrite H
                 | [ |- _ ] => rewrite EquivDec_refl_left
                 | [ |- _ ] => rewrite tvar_seqb_refl
               end; reflexivity : exprs.
(*
    Hint Resolve is_well_typed_const is_well_typed_var is_well_typed_uvar : exprs.
        Hint Extern 1 (is_well_typed _ _ _ _ _ = true) => simpl; think : exprs.
*)

    Lemma exprUnify_WellTyped_Forall : forall n (l : list (expr types)),
      Forall
      (fun l0 : expr types =>
        forall (r : expr types) (sub sub' : Subst),
          exprUnify n l0 r sub = Some sub' ->
          forall (funcs : tfunctions) (U G : tenv) (t : tvar),
            is_well_typed funcs U G l0 t = true ->
            is_well_typed funcs U G r t = true ->
            Subst_WellTyped funcs U G sub -> Subst_WellTyped funcs U G sub') l ->
      forall (funcs : tfunctions) (U G : tenv) (sub' : Subst)
        (l0 : list tvar) (sub : Subst),
        Subst_WellTyped funcs U G sub ->
        forall l1 : list (expr types),
          Folds.fold_left_2_opt (exprUnify n) l l1 sub = Some sub' ->
          Folds.all2 (is_well_typed funcs U G) l1 l0 = true ->
          Folds.all2 (is_well_typed funcs U G) l l0 = true ->
          Subst_WellTyped funcs U G sub'.
    Proof.
      induction 1; simpl; intros.
      { destruct l0; destruct l1; simpl in *; auto; try congruence. inversion H0; subst; auto. }
      { destruct l1; destruct l0; try congruence. simpl in *.
        repeat match goal with
                 | [ H : context [ match ?X with
                                     | _ => _
                                   end ] |- _ ] =>
                 revert H; case_eq X; try congruence; intros
               end. eauto. }
    Qed.

    Theorem exprUnify_WellTyped : forall n l r sub sub',
      exprUnify n l r sub = Some sub' ->
      forall funcs U G t,
        is_well_typed funcs U G l t = true ->
        is_well_typed funcs U G r t = true ->
        Subst_WellTyped funcs U G sub ->
        Subst_WellTyped funcs U G sub'.
    Proof.
      induction n; induction l; intros; rewrite exprUnify_unroll in *; unfold get_Eq in *; destruct r; simpl in *;
        try congruence;
        repeat (match goal with
                 | [ H : (if ?X then _ else _) = _ |- _ ] =>
                   (revert H; Reflection.consider X; intros; try congruence); [ try subst ]
                 | [ H : context [ @equiv_dec ?A ?B ?C ?E ?X ?Y ] |- _ ] =>
                   destruct (@equiv_dec A B C E X Y); unfold equiv in *; subst; try congruence
                 | [ H : context [ match ?T with
                                     | tvProp => _
                                     | tvType _ => _
                                   end ] |- _ ] => (destruct T; try congruence); [ ]
                 | [ H : context [ match nth_error ?X ?Y with
                                     | _ => _
                                   end ] |- _ ] =>
                 revert H; case_eq (nth_error X Y); intros; try congruence
                 | [ H : context [ match Subst_lookup ?X ?Y with
                                     | _ => _
                                   end ] |- _ ] =>
                 revert H; case_eq (Subst_lookup X Y); intros; try congruence
                 | [ H : (if ?X then _ else _) = _ |- _ ] =>
                   (revert H; Reflection.consider X; intros; try congruence); [ ]
                 | [ H : ?X = _ , H' : ?X = _ |- _ ] => rewrite H in H'
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ H : context [ match exprUnify ?A ?B ?C ?D with _ => _ end ] |- _ ] =>
                   revert H; case_eq (exprUnify A B C D); intros; try congruence
                 | [ H : _ && _ = true |- _ ] => eapply andb_true_iff in H; destruct H
                 | [ H : forall a b c d, exprUnify ?n a b c = Some d -> _ , H' : exprUnify ?n _ _ _ = Some _ |- _ ] =>
                   (eapply H in H'; (eauto using Subst_lookup_WellTyped, Subst_set_WellTyped with exprs));
                   instantiate; eauto with exprs
                 | [ H : ?X = ?X , H' : context [ match ?H with _ => _ end ] |- _ ] =>
                   rewrite (EqdepClass.UIP_refl H) in H'
                 | [ |- _ ] => try unfold equiv in *; progress subst
               end);
        try solve [ eauto using Subst_lookup_WellTyped, Subst_set_WellTyped with exprs
              | (eapply Subst_set_WellTyped; eauto); simpl;
                repeat match goal with
                         | [ H : _ = _ |- _ ] => rewrite H
                         | [ |- _ ] => rewrite EquivDec_refl_left
                         | [ |- _ ] => rewrite tvar_seqb_refl
                       end; auto
          | eauto using exprUnify_WellTyped_Forall].
      { consider (EqNat.beq_nat x u); intros; subst.
        inversion H4; clear H4; subst; auto.
        eapply Subst_set_WellTyped; try eassumption.
        simpl. rewrite H1. consider (tvar_seqb t t); auto. }
      { consider (EqNat.beq_nat x u); intros; subst.
        inversion H5; clear H5; subst; auto.
        eapply IHn. eassumption. 3: eassumption.
        eapply Subst_lookup_WellTyped; eassumption.
        eapply Subst_lookup_WellTyped; eassumption. }
      { consider (EqNat.beq_nat x u); intros; subst.
        inversion H4; clear H4; subst; auto.
        eapply Subst_set_WellTyped; try eassumption.
        simpl. rewrite H1. consider (tvar_seqb t t); auto. }
    Qed.

    Lemma Subst_lookup_Subst_equations : forall funcs U G x sub e t,
      Subst_lookup x sub = Some e ->
      Subst_equations funcs U G sub ->
      exprD funcs U G e t = lookupAs U t x.
    Proof.
      intros. unfold Subst_equations in *.
      rewrite PROPS.fold_Add with (m1 := FM.remove x (projT1 sub)) (m2 := projT1 sub) (k := x) (e := e) in H0;
        eauto with typeclass_instances.
      repeat match goal with
               | [ H : match ?X with
                         | _ => _
                       end |- _ ] =>
               revert H; case_eq X; intros; try contradiction
             end.
      intuition. subst.
      unfold lookupAs. rewrite H0. simpl in *.
      destruct (equiv_dec x0 t).
      unfold equiv in *. subst. auto.
      case_eq (exprD funcs U G e t); intros; auto.
      exfalso. apply c. unfold equiv; eapply exprD_det with (e := e) (funcs := funcs) (meta_env := U) (var_env := G); congruence.


      { clear. repeat (red; intros; subst).
        destruct (nth_error U y); intros.
        destruct s. destruct (exprD funcs U G y0 x0); firstorder. firstorder. }
      { clear. repeat (red; intros; subst).
        repeat match goal with
                 | [ |- context [ match ?X with
                                    | _ => _
                                  end ] ] => destruct X
               end; firstorder. }
        { intro. rewrite FACTS.remove_in_iff in H1. intuition; congruence. }
        { unfold PROPS.Add. intros; rewrite FACTS.add_o; rewrite FACTS.remove_o. destruct (FM.E.eq_dec x y); auto.
          Transparent Subst_lookup.
          unfold Subst_lookup, subst_lookup in *. subst; auto. }
    Qed.

    Theorem Subst_equations_exprInstantiate : forall funcs U G e t sub,
      Subst_equations funcs U G sub ->
      exprD funcs U G (exprInstantiate sub e) t = exprD funcs U G e t.
    Proof.
      induction e; simpl; intros; think; autorewrite with subst_simpl in *; symmetry;
        repeat (simpl in *;
          match goal with
            | [ H : context [ match ?X with
                                | _ => _
                              end ] |- _ ] =>
            revert H; case_eq X; intros; try congruence
            | [ H : equiv _ _ |- _ ] => unfold equiv in H; subst
                 | [ H : _ |- _ ] => erewrite H by eauto
            | [ |- context [ match ?X with
                               | tvProp => _
                               | tvType _ => _
                             end ] ] => destruct X

          end); auto; try congruence.
      { change (FM.find x (projT1 sub)) with (Subst_lookup x sub).
        case_eq (Subst_lookup x sub); intros; simpl; auto.
        erewrite Subst_lookup_Subst_equations; eauto. }
      { destruct (nth_error funcs f); auto.
        destruct (equiv_dec (Range s) t); auto. unfold equiv in *. subst.
        destruct s; simpl in *.
        generalize dependent Domain. induction H; destruct Domain; simpl; auto.
        erewrite H by eauto. intros. destruct (exprD funcs U G x t); auto. }
    Qed.

    Theorem WellTyped_lookup : forall funcs U G sub,
      Subst_WellTyped funcs U G sub ->
      forall u e,
      Subst_lookup u sub = Some e ->
      exists t, nth_error U u = Some t /\
      is_well_typed funcs U G e t = true.
    Proof.
      unfold Subst_WellTyped, Subst_lookup, subst_lookup. intros.
      apply FACTS.find_mapsto_iff in H0. eauto.
    Qed.

    Theorem exprInstantiate_instantiated : forall k sub e,
      Subst_lookup k sub = Some e ->
      exprInstantiate sub e = e.
    Proof.
      intros. generalize H; eapply Subst_lookup_Extends in H. 2: reflexivity. intros.
      rewrite H in H0. inversion H0; auto. repeat rewrite H2. auto.
    Qed.

    Lemma normalized_not_mentions : forall k e' s e,
      subst_lookup k s = Some e' ->
      normalized s e = true ->
      mentionsU k e = false.
    Proof.
      induction e; simpl in *; intros; think; subst; think; auto.
      revert H1. induction H; think.
    Qed.

    Theorem exprInstantiate_Removes : forall k sub e e' e'',
      Subst_lookup k sub = Some e ->
      exprInstantiate sub e' = e'' ->
      mentionsU k e'' = false.
    Proof.
      induction e'; simpl in *; intros; think; subst; think; auto.
      { destruct sub. unfold Subst_lookup, subst_lookup in *; simpl in *.
        consider (FM.find x x0); intros; simpl.
        2: consider (EqNat.beq_nat k x); try congruence.
        eapply normalized_not_mentions. eapply H. eapply w. eapply FACTS.find_mapsto_iff. eauto. }
      { induction H; simpl; auto. rewrite H; auto. }
    Qed.

    Lemma Subst_set_unroll_None: forall (u : nat) (E : expr types) (sub : Subst),
      Subst_set u E sub = None ->
      mentionsU u (exprInstantiate sub E) = true.
    Proof.
      unfold Subst_set. do 3 intro.
      match goal with
        | [ |- context [ eq_refl ?X ] ] => generalize (eq_refl X)
      end.
      generalize (subst_set u E (projT1 sub)) at 2 3. destruct o; intros; try congruence.
      unfold subst_set in *.
      unfold exprInstantiate.
      destruct (mentionsU u (subst_exprInstantiate (projT1 sub) E)); congruence.
    Qed.

    Lemma Subst_Extends_fin_instantiate : forall x sub sub' v k,
      Subst_Extends sub' sub ->
      mentionsU k (subst_exprInstantiate (projT1 sub) v) = false ->
      FM.MapsTo k v (projT1 sub') ->
      normalized (projT1 sub) x = true ->
      subst_exprInstantiate (projT1 sub')
      (subst_exprInstantiate
        (FM.add k (subst_exprInstantiate (projT1 sub) v) (projT1 sub)) x) =
      exprInstantiate sub' x.
    Proof.
      induction x; simpl; intros; auto.
      { unfold subst_lookup.
        consider (FM.find (elt:=expr types) x (projT1 sub)); try congruence; intros.
        rewrite MFACTS.PROPS.F.add_o. destruct (FM.E.eq_dec k x); subst.
        generalize (exprInstantiate_Extends H); unfold exprInstantiate.
        intro. rewrite H3.
        apply MFACTS.PROPS.F.find_mapsto_iff in H1. rewrite H1.
        change (exprInstantiate sub' v = v).
        eapply exprInstantiate_instantiated. unfold Subst_lookup, subst_lookup.
        eassumption.
        rewrite H2. reflexivity. }
      { f_equal. rewrite map_map.
        revert H3; induction H; simpl; intros; think; auto. }
      { f_equal; think; auto. }
      { think. }
    Qed.

    Lemma exprInstantiate_Extends' : forall x y,
      Subst_Extends x y ->
      forall t, exprInstantiate y (exprInstantiate x t) = exprInstantiate x t.
    Proof.
      induction t; simpl; intros; think; auto.
      { consider (FM.find (elt:=expr types) x0 (projT1 x)); intros.
        apply MFACTS.PROPS.F.find_mapsto_iff in H0.
        eapply (projT2 x) in H0.
        eapply WellFormed_Canonical.
        destruct y; destruct x. eapply normalized_Lt. eassumption. eassumption.
        simpl. unfold subst_lookup.
        consider (FM.find (elt:=expr types) x0 (projT1 y)); intros.
        apply MFACTS.PROPS.F.find_mapsto_iff in H1.
        apply H in H1.
        apply MFACTS.PROPS.F.find_mapsto_iff in H1. congruence. auto. }
      { f_equal. rewrite map_map. induction H0; intros; think; auto. }
    Qed.

    Lemma extends_add_from : forall sub sub' k v,
      Subst_Extends sub' sub ->
      Subst_lookup k sub' = Some v ->
      Subst_lookup k sub = None ->
      match Subst_set k v sub with
        | None => False
        | Some sub => Subst_Extends sub' sub
      end.
    Proof.
      intros.
      consider (Subst_set k v sub); intros.
      { generalize (Subst_set_Extends _ _ _ H2 H1); intros.
        generalize (exprInstantiate_Extends H).
        generalize (exprInstantiate_Extends H3); intros.
        eapply Subst_set_unroll in H2; intuition.
        unfold Subst_Extends. generalize H.
        unfold Subst_Extends in * |-; intros. unfold exprInstantiate in *. rewrite H7 in *. clear H7 s.
        unfold Subst_lookup, subst_lookup in *.
        apply MFACTS.PROPS.F.find_mapsto_iff in H0.
        apply MFACTS.PROPS.F.map_mapsto_iff in H8. destruct H8. intuition. subst.
        apply MFACTS.PROPS.F.add_mapsto_iff in H9. destruct H9; intuition; subst.
        { match goal with
          | H : FM.MapsTo ?A ?Y ?B |- FM.MapsTo ?A ?X ?B => cutrewrite (X = Y); auto
          end.
          rewrite subst_exprInstantiate_add_not_mentions by auto.
          rewrite subst_exprInstantiate_idem.
          2: destruct sub; auto. rewrite H5.
          apply WellFormed_Canonical.
          destruct sub' as [ sub' ? ]; simpl in *. eapply w. eauto. }
        { match goal with
            | |- FM.MapsTo _ ?X _ => cutrewrite (X = exprInstantiate sub' x); auto
          end.
          eapply Subst_Extends_fin_instantiate; eauto.
          eapply (projT2 sub). eauto. } }
      { apply Subst_set_unroll_None in H2.
        rewrite <- (exprInstantiate_instantiated _ _ H0) in H2.
        rewrite exprInstantiate_Extends' in H2; eauto.
        erewrite normalized_not_mentions in H2; eauto.
        congruence. apply wf_instantiate_normalized. apply (projT2 sub'). }
    Qed.

    Lemma diff_add : forall T k (v : T) m m',
      FM.Equal (FM.remove k (PROPS.diff m m'))
      (PROPS.diff m (FM.add k v m')).
    Proof.
      intros. red. intros.
      rewrite FACTS.remove_o. destruct (FM.E.eq_dec k y). subst.
      { consider (FM.find (elt:=T) y (PROPS.diff m (FM.add y v m'))); intros; auto.
        exfalso. apply FACTS.find_mapsto_iff in H.
        eapply PROPS.diff_mapsto_iff in H. intuition. apply H1.
        exists v. apply FACTS.add_mapsto_iff. intuition. }
      { consider (FM.find (elt:=T) y (PROPS.diff m m')); intros.
        { apply FACTS.find_mapsto_iff in H. eapply PROPS.diff_mapsto_iff in H. destruct H.
          consider (FM.find (elt:=T) y (PROPS.diff m (FM.add k v m'))); intros.
          apply FACTS.find_mapsto_iff in H1. eapply PROPS.diff_mapsto_iff in H1. destruct H1.
          apply FACTS.find_mapsto_iff in H1. apply FACTS.find_mapsto_iff in H. congruence.
          exfalso. apply FACTS.not_find_in_iff in H1. apply H1.
          apply PROPS.diff_in_iff. split. exists t. auto.
          rewrite FACTS.add_neq_in_iff; auto. }
        { consider (FM.find (elt:=T) y (PROPS.diff m (FM.add k v m'))); auto; intros; exfalso.
          apply FACTS.find_mapsto_iff in H0. eapply PROPS.diff_mapsto_iff in H0.
          destruct H0. apply FACTS.not_find_in_iff in H. apply H; clear H.
          rewrite FACTS.add_neq_in_iff in H1; auto. eapply PROPS.diff_in_iff; intuition.
          exists t. auto. } }
    Qed.

    Lemma diff_map_2 : forall T (F : T -> T) m m',
      FM.Equal (PROPS.diff m m') (PROPS.diff m (FM.map F m')).
    Proof. clear.
      intros; red; intros.
      consider (FM.find (elt:=T) y (PROPS.diff m m'));
      consider (FM.find (elt:=T) y (PROPS.diff m (FM.map F m'))); intros; auto;
        repeat match goal with
                 | |- Some _ = None => exfalso
                 | |- None = Some _ => exfalso
                 | H : FM.find _ (PROPS.diff _ _) = Some _ |- _ =>
                   apply FACTS.find_mapsto_iff in H; apply PROPS.diff_mapsto_iff in H
                 | H : FM.find ?A (PROPS.diff ?B ?C) = None |- _ =>
                   apply FACTS.not_find_in_iff in H
                 | H : ~ FM.In _ (PROPS.diff _ _) |- _ => rewrite PROPS.diff_in_iff in H; apply H; clear H; split
                 | H : FM.MapsTo _ _ _ |- _ => apply FACTS.find_mapsto_iff in H
                 | H : _ /\ _ |- _ => destruct H
                 | H : FM.find ?K ?M = Some ?V |- FM.In ?K ?M => exists V; apply FACTS.find_mapsto_iff in H; eapply H
                 | |- _ => rewrite FACTS.map_in_iff in *
               end; try congruence; auto.
    Qed.

    Inductive Subst_Extends' : Subst -> Subst -> Prop :=
    | SE_Refl : forall a b, Subst_Equal a b -> Subst_Extends' a b
    | SE_Add : forall k v a b c,
      Subst_set k v a = Some b -> ~FM.In k (projT1 a) -> Subst_Extends' c b ->
      Subst_Extends' c a.

    Lemma decidable_In : forall T k s, Decidable.decidable (FM.In (elt:=T) k s).
    Proof. clear; intros.
      consider (FM.find k s); intros. left. exists t. apply FACTS.find_mapsto_iff; auto.
      right. intro. destruct H0. apply FACTS.find_mapsto_iff in H0. congruence.
    Qed.

    Lemma extends_as_extension : forall sub sub',
      Subst_Extends sub' sub ->
      Subst_Extends' sub' sub.
    Proof.
      intros.
      remember (PROPS.diff (projT1 sub') (projT1 sub)).
      assert (FM.Equal t (PROPS.diff (projT1 sub') (projT1 sub))). subst; reflexivity. clear Heqt. rename H0 into Heqt.
      generalize dependent sub.
      eapply PROPS.map_induction with (m := t); intros.
      { eapply SE_Refl. red. red; intros.
        consider (FM.find (elt:=expr types) y (projT1 sub'));
        consider (FM.find (elt:=expr types) y (projT1 sub)); intros; auto.
        { f_equal.
          assert (normalized (projT1 sub') e = true).
          cut (forall k, FM.In k (projT1 sub') -> FM.In k (projT1 sub)).
          cut (normalized (projT1 sub) e = true). clear.
          { induction e; simpl; intros; think; auto.
            { apply FACTS.not_find_in_iff in H. exfalso. apply H. apply H0.
              exists e. apply FACTS.find_mapsto_iff; auto. }
            { revert H0. induction H; simpl; intros; think; auto. } }
          eapply (projT2 sub). apply FACTS.find_mapsto_iff. eassumption.
          { clear - H Heqt. intros. destruct H0.
            assert (~FM.In k m). intro. destruct H1. apply FACTS.find_mapsto_iff in H1.
            rewrite MFACTS.find_Empty in H1; auto. congruence.
            rewrite Heqt in H1. rewrite PROPS.diff_in_iff in H1.
            apply Decidable.not_and in H1; auto using decidable_In.
            destruct H1. exfalso. apply H1. exists x. auto.
            apply Decidable.not_not in H1; auto using decidable_In. }
          apply FACTS.find_mapsto_iff in H1. apply H0 in H1. apply FACTS.find_mapsto_iff in H1. rewrite H1 in H2.
          inversion H2. unfold exprInstantiate. apply WellFormed_Canonical. auto. }
        { cut (FM.MapsTo y e m); intros. exfalso.
          rewrite MFACTS.find_empty_iff in H. specialize (H y). apply FACTS.find_mapsto_iff in H3. congruence.
          rewrite Heqt in *. eapply PROPS.diff_mapsto_iff. apply FACTS.find_mapsto_iff in H2. intuition.
          destruct H3. apply FACTS.find_mapsto_iff in H3. congruence. }
        { exfalso. clear Heqt. apply FACTS.find_mapsto_iff in H1. eapply H0 in H1.
          apply FACTS.find_mapsto_iff in H1. congruence. } }
      { generalize (H1 x); intro.
        rewrite FACTS.add_o in H3. destruct (FM.E.eq_dec x x); try congruence. clear e0.
        apply FACTS.find_mapsto_iff in H3. rewrite Heqt in *.
        eapply PROPS.diff_mapsto_iff in H3. destruct H3.
        eapply extends_add_from with (k := x) (v := e) in H2.
        remember (Subst_set x e sub). destruct o; try contradiction.
        eapply SE_Add with (k := x) (v := e).
        symmetry; eauto. eauto.
        apply H; eauto.

        symmetry in Heqo. eapply Subst_set_unroll in Heqo. destruct Heqo.

        rewrite H6. rewrite <- diff_map_2. rewrite <- diff_add. rewrite <- Heqt.
        red. intro. specialize (H1 y). rewrite FACTS.remove_o.
        rewrite H1. rewrite FACTS.add_o.
        destruct (FM.E.eq_dec x y); subst; auto. apply FACTS.not_find_in_iff; auto.

        unfold Subst_lookup, subst_lookup; apply FACTS.find_mapsto_iff. assumption.
        unfold Subst_lookup, subst_lookup; apply FACTS.not_find_in_iff; assumption. }
    Qed.

    Lemma Subst_equations_sem : forall funcs U G s,
      Subst_equations funcs U G s <->
      (forall k e,
        Subst_lookup k s = Some e ->
        match nth_error U k with
          | None => False
          | Some v => match exprD funcs U G e (projT1 v) with
                        | None => False
                        | Some v' => v' = projT2 v
                      end
        end).
    Proof.
      unfold Subst_equations, Subst_lookup, subst_lookup. destruct s. simpl in *. clear w.
      cut True; auto. generalize True. intro.
      eapply PROPS.map_induction with (m := x); intros.
      { split; intros.
        { rewrite MFACTS.find_Empty in H2; auto. congruence. }
        { rewrite PROPS.fold_Empty; eauto with typeclass_instances. } }
      { split; intros.
        { rewrite PROPS.fold_Add in H3; eauto with typeclass_instances.
          repeat match goal with
                   | H : match ?X with _ => _ end |- _ => consider X; intros; try contradiction
                   | H : _ /\ _ |- _ => destruct H
                 end; subst.
          rewrite H1 in H4. rewrite FACTS.add_o in H4. destruct (FM.E.eq_dec x0 k); subst.
          { rewrite H5. simpl. inversion H4. subst; rewrite H6. reflexivity. }
          { eapply H; eauto. }
          { repeat (red; intros; subst);
            repeat match goal with
                     | |- context [ match ?X with _ => _ end ] => destruct X
                   end; intuition. }
          { repeat (red; intros; subst);
            repeat match goal with
                     | |- context [ match ?X with _ => _ end ] => destruct X
                   end; intuition. } }
          { specialize (H H2).
            rewrite PROPS.fold_Add; eauto with typeclass_instances.
            generalize (H3 x0 e); intros. rewrite H1 in H4. rewrite FACTS.add_o in H4.
            destruct (FM.E.eq_dec x0 x0); try congruence. specialize (H4 refl_equal).
            destruct (nth_error U x0); try contradiction.
            destruct s; simpl in *. destruct (exprD funcs U G e x1); auto; subst. split; auto.
            eapply H. intros. eapply H3. rewrite H1.
            rewrite FACTS.add_o. destruct (FM.E.eq_dec x0 k); auto. subst. exfalso. apply H0.
            exists e1. apply FACTS.find_mapsto_iff; auto.
            { repeat (red; intros; subst);
              repeat match goal with
                       | |- context [ match ?X with _ => _ end ] => destruct X
                     end; intuition. }
            { repeat (red; intros; subst);
              repeat match goal with
                       | |- context [ match ?X with _ => _ end ] => destruct X
                     end; intuition. } } }
    Qed.

(*
    Lemma Subst_set_Subst_equations : forall funcs U G k v a b,
      Subst_lookup k a = None ->
      Subst_set k v a = Some b ->
      match nth_error U k with
        | None => False
        | Some e => match exprD funcs U G v (projT1 e) with
                      | None => False
                      | Some v => v = projT2 e
                    end
      end ->
      Subst_equations funcs U G b ->
      Subst_equations funcs U G a.
    Proof.
      intros. eapply Subst_set_unroll in H0. intuition.
      consider (nth_error U k); intros; try contradiction.
      consider (exprD funcs U G v (projT1 s)); try contradiction; intros. subst.
      eapply Subst_equations_sem; intros.
      generalize H2.
      eapply Subst_equations_sem with (k := k0)
        (e := exprInstantiate b e) in H2.
      destruct (nth_error U k0); auto. intro.
      rewrite Subst_equations_exprInstantiate in H2. auto. auto.
      { unfold Subst_lookup, subst_lookup in *. rewrite H4. rewrite FACTS.map_o. rewrite FACTS.add_o.
        destruct (FM.E.eq_dec k k0); subst; simpl. congruence.
        rewrite H5. simpl. unfold exprInstantiate. rewrite H4. f_equal.
        unfold exprInstantiate in *. erewrite adf; eauto using (projT2 a).
        2: apply (projT2 a).
        generalize exprInstantiate_instantiated. unfold Subst_lookup, subst_lookup. intro XX.
        apply XX in H5. rewrite <- H5.
        eapply wf_instantiate_normalized. apply (projT2 a). }
    Qed.
*)

    Lemma Subst_set_Subst_equations' : forall funcs U G k v a b,
      Subst_lookup k a = None ->
      Subst_set k v a = Some b ->
      match nth_error U k with
        | None => False
        | Some e => match exprD funcs U G (exprInstantiate a v) (projT1 e) with
                      | None => False
                      | Some v => v = projT2 e
                    end
      end ->
      Subst_equations funcs U G b ->
      Subst_equations funcs U G a.
    Proof.
      intros. eapply Subst_set_unroll in H0. intuition.
      consider (nth_error U k); intros; try contradiction.
      consider (exprD funcs U G (exprInstantiate a v) (projT1 s)); try contradiction; intros. subst.
      eapply Subst_equations_sem; intros.
      generalize H2.
      eapply Subst_equations_sem with (k := k0)
        (e := exprInstantiate b e) in H2.
      destruct (nth_error U k0); auto. intro.
      rewrite Subst_equations_exprInstantiate in H2. auto. auto.
      { unfold Subst_lookup, subst_lookup in *. rewrite H4. rewrite FACTS.map_o. rewrite FACTS.add_o.
        destruct (FM.E.eq_dec k k0); subst; simpl. congruence.
        rewrite H5. simpl. unfold exprInstantiate. rewrite H4. f_equal.
        unfold exprInstantiate in *. erewrite adf; eauto using (projT2 a).
        2: apply (projT2 a).
        generalize exprInstantiate_instantiated. unfold Subst_lookup, subst_lookup. intro XX.
        apply XX in H5. rewrite <- H5.
        eapply wf_instantiate_normalized. apply (projT2 a). }
    Qed.


    Theorem Subst_equations_Extends : forall funcs G sub sub' U,
      Subst_Extends sub' sub ->
      Subst_equations funcs U G sub' ->
      Subst_equations funcs U G sub.
    Proof.
      intros. apply extends_as_extension in H.
      induction H.
      { unfold Subst_equations in *. unfold Subst_Equal in *.
        rewrite PROPS.fold_Equal in H0. eassumption. eauto with typeclass_instances.
        { repeat (red; intros; subst). destruct (nth_error U y); auto. destruct s. destruct (exprD funcs U G y0 x0); intuition. }
        { repeat (red; intros; subst);
            repeat match goal with
                     | |- context [ match ?X with _ => _ end ] => destruct X
                   end; intuition. }
        auto. }
      { specialize (IHSubst_Extends' H0).
        eapply Subst_set_Subst_equations' with (k := k); eauto.
        unfold Subst_lookup, subst_lookup. apply FACTS.not_find_in_iff; auto.
        apply Subst_set_Subst_lookup in H.
        eapply Subst_equations_sem in IHSubst_Extends'. 2: eassumption.
        destruct (nth_error U k); auto. }
    Qed.


    Theorem Subst_equations_WellTyped : forall funcs G U sub,
      Subst_equations funcs U G sub ->
      Subst_WellTyped (typeof_funcs funcs) (typeof_env U) (typeof_env G) sub.
    Proof.
      intros. intro; intros.
      eapply Subst_equations_sem with (k := k) (e := v) in H.
      consider (nth_error U k); intros; try contradiction.
      consider (exprD funcs U G v (projT1 s)); intros; try contradiction. subst.
      unfold typeof_env at 1. erewrite map_nth_error by eassumption. eexists; split. reflexivity.
      eapply is_well_typed_correct_only in H1; eauto using typeof_env_WellTyped_env, typeof_funcs_WellTyped_funcs.
      unfold Subst_lookup, subst_lookup. apply FACTS.find_mapsto_iff; auto.
    Qed.

    (** An incremental version of Subst_equations **)
    Section Subst_equations_to.
      Variable funcs : functions types.
      Variables uenv venv : env types.
      Variable subst : Subst.

      Fixpoint Subst_equations_to (from : nat) (ls : Expr.env types) : Prop :=
        match ls with
          | nil => True
          | l :: ls =>
            match Subst_lookup from subst with
              | None => True
              | Some e => match exprD funcs uenv venv e (projT1 l) with
                            | None => False
                            | Some v => projT2 l = v
                          end
            end /\ Subst_equations_to (S from) ls
        end.

      Lemma Subst_equations_to_sem : forall ls from,
        Subst_equations_to from ls ->
        forall n,
          match nth_error ls n with
            | None => True
            | Some v' =>
              match Subst_lookup (from + n) subst with
                | None => True
                | Some e => match exprD funcs uenv venv e (projT1 v') with
                              | None => False
                              | Some v => projT2 v' = v
                            end
              end
          end.
      Proof.
        induction ls; destruct n; simpl in *; intros; auto.
        { rewrite Plus.plus_0_r. intuition. }
        { intuition. eapply IHls with (n := n) in H1.
          cutrewrite (from + S n = S from + n); [ assumption | omega ]. }
      Qed.


      Theorem Subst_equations_to_Subst_equations :
        Subst_WellTyped (typeof_funcs funcs) (typeof_env uenv) (typeof_env venv) subst ->
        Subst_equations_to 0 uenv ->
        Subst_equations funcs uenv venv subst.
      Proof.
        intros.
        eapply Subst_equations_sem. intros.
        assert (FM.MapsTo k e (projT1 subst)). apply FACTS.find_mapsto_iff. eapply H1.
        eapply H in H2. destruct H2.
        apply Subst_equations_to_sem with (n := k) in H0. destruct H2.
        unfold typeof_env in H2.
        rewrite Tactics.map_nth_error_full in H2.
        destruct (nth_error uenv k); try congruence.
        simpl in *. rewrite H1 in H0.
        destruct (exprD funcs uenv venv e (projT1 s)); auto.
      Qed.

    End Subst_equations_to.

  End typed.
End Unifier.

Module UNIFIER := Unifier NatMap.Ordered_nat.
