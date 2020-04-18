Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Bedrock.SepTheoryX Bedrock.PropX.
Require Import Bedrock.PropXTac.
Require Import Coq.Classes.RelationClasses Bedrock.EqdepClass.
Require Import Bedrock.Expr Bedrock.SepExpr.
Require Import Bedrock.DepList.
Require Import Coq.Setoids.Setoid.
Require Import Bedrock.Tactics.
Require Import Coq.Bool.Bool Bedrock.Folds.
Require Import Bedrock.Reflection.

Set Implicit Arguments.
Set Strict Implicit.

Require Bedrock.NatMap Bedrock.Multimap.

Module FM := NatMap.IntMap.

Remove Hints FM.Raw.Proofs.L.PX.eqk_refl FM.Raw.Proofs.L.PX.eqk_sym
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
  FM.Raw.BSLeaf FM.Raw.BSNode FM.Raw.Leaf FM.Raw.Node
  FM.E.lt_trans FM.E.lt_not_eq FM.E.eq_refl
  FM.E.eq_sym FM.E.eq_trans.

Module MM := Multimap.Make FM.
Module MF := NatMap.MoreFMapFacts FM.

Module Type SepHeap.
  Declare Module SE : SepExpr.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Record SHeap : Type :=
    { impures : MM.mmap (exprs types)
    ; pures   : list (expr types)
    ; other   : list (SE.ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Parameter WellTyped_sheap : forall (tf : tfunctions) (tp : SE.tpredicates) (tU tG : tenv) (h : SHeap), bool.

    Parameter WellTyped_impures : forall (tf : tfunctions) (tp : SE.tpredicates) (tU tG : tenv) (imps : MM.mmap (exprs types)), bool.

    (** TODO: What happens if I denote this directly to hprop?
     ** - fewer lemmas about concrete syntax!
     ** - can't re-hash (probably don't want to do this anyways...)
     ** * I think this is Ok for now
     **)
    Parameter sheapD : SHeap -> SE.sexpr types pcType stateType.

    (** Operations on [SHeap]s **)
    Definition SHeap_empty : SHeap :=
      {| impures := MM.empty _
       ; pures := nil
       ; other := nil
       |}.

    Parameter star_SHeap : SHeap -> SHeap -> SHeap.

    Parameter liftSHeap : nat -> nat -> nat -> nat -> SHeap -> SHeap.

    Parameter applySHeap : forall (F : expr types -> expr types) (sh : SHeap), SHeap.

    Axiom applySHeap_defn : forall F sh,
      applySHeap F sh =
      {| impures := MM.mmap_map (map F) (impures sh)
       ; pures := map F (pures sh)
       ; other := other sh
       |}.

    (** Convert an [sexpr] to an [SHeap] **)
    Parameter hash : SE.sexpr types pcType stateType -> variables * SHeap.

    Parameter impuresD : MM.mmap (exprs types) -> SE.sexpr types pcType stateType.

    Parameter starred : forall (T : Type) (F : T -> SE.sexpr types pcType stateType),
      list T -> SE.sexpr types pcType stateType -> SE.sexpr types pcType stateType.

    Section facts.
      Variable funcs : functions types.
      Variable preds : SE.predicates types pcType stateType.
      Variables U G : env types.
      Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

      (** Theorems **)
      Axiom hash_denote : forall (s : SE.sexpr types pcType stateType),
        SE.heq funcs preds U G cs s (SE.existsEach (fst (hash s)) (sheapD (snd (hash s)))).

      Axiom star_SHeap_denote : forall s s',
        SE.heq funcs preds U G cs (SE.Star (sheapD s) (sheapD s')) (sheapD (star_SHeap s s')).

      (** Well-typedness **)
      Axiom WellTyped_sheap_eq : forall (tf : tfunctions) (tp : SE.tpredicates) (tU tG : tenv) (h : SHeap),
        WellTyped_sheap tf tp tU tG h =
        WellTyped_impures tf tp tU tG (impures h) && allb (fun e => is_well_typed tf tU tG e tvProp) (pures h).

      Axiom WellTyped_impures_spec_eq : forall tf tp tU tG impures,
        WellTyped_impures tf tp tU tG impures =
        FM.fold (fun p argss acc =>
        acc && match argss , nth_error tp p with
                 | nil , _ => true
                 | _ , None => false
                 | argss , Some ts =>
                   allb (fun args => all2 (is_well_typed tf tU tG) args ts) argss
               end) impures true.

      Axiom WellTyped_impures_eq : forall tf tp tU tG impures,
        WellTyped_impures tf tp tU tG impures = true <->
        (forall k v, FM.find k impures = Some v ->
          match v with
            | nil => True
            | _ => match nth_error tp k with
                     | None => False
                     | Some ts =>
                       allb (fun argss => all2 (is_well_typed tf tU tG) argss ts) v = true
                   end
          end).

      Axiom WellTyped_sheap_star : forall tf tp tU tG h0 h1,
        WellTyped_sheap tf tp tU tG h0 && WellTyped_sheap tf tp tU tG h1 =
        WellTyped_sheap tf tp tU tG (star_SHeap h0 h1).

      Axiom WellTyped_sheap_WellTyped_sexpr : forall tf tp tU tG h,
        WellTyped_sheap tf tp tU tG h = SE.WellTyped_sexpr tf tp tU tG (sheapD h).

      Axiom WellTyped_hash : forall tf tp tU tG (s : SE.sexpr types pcType stateType),
        SE.WellTyped_sexpr tf tp tU tG s =
        WellTyped_sheap tf tp tU (rev (fst (hash s)) ++ tG) (snd (hash s)).

      (** Hash Equations **)
      Axiom hash_Func : forall p args,
        hash (SE.Func p args) = (nil, {| impures := MM.mmap_add p args (MM.empty _)
                                       ; pures   := nil
                                       ; other   := nil
                                       |}).

      (** Definitions **)
      Axiom starred_def : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls : list T) (base : SE.sexpr _ _ _),
        SE.heq funcs preds U G cs
            (starred F ls base)
            (fold_right (fun x a => SE.Star (F x) a) base ls).

      Axiom starred_base : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls : list T) (base : SE.sexpr _ _ _),
        SE.heq funcs preds U G cs
            (starred F ls base)
            (SE.Star base (starred F ls SE.Emp)).

      Axiom starred_app : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls ls' : list T) (base : SE.sexpr _ _ _),
        SE.heq funcs preds U G cs
            (starred F (ls ++ ls') base)
            (starred F ls (starred F ls' base)).

      Axiom starred_perm : forall T L R,
        Permutation.Permutation L R ->
        forall (F : T -> _) base,
          SE.heq funcs preds U G cs (starred F L base) (starred F R base).

      Axiom impuresD_Add : forall f argss i i',
        MM.PROPS.Add f argss i i' ->
        ~FM.In f i ->
        SE.heq funcs preds U G cs
            (impuresD i')
            (SE.Star (starred (SE.Func f) argss SE.Emp) (impuresD i)).

      Axiom impuresD_Empty : forall i,
        FM.Empty i ->
        SE.heq funcs preds U G cs
            (impuresD i) SE.Emp.

      Axiom impuresD_Equiv : forall a b,
        MM.mmap_Equiv a b ->
        SE.heq funcs preds U G cs (impuresD a) (impuresD b).

      Axiom sheapD_def : forall s,
        SE.heq funcs preds U G cs
            (sheapD s)
            (SE.Star (impuresD (impures s))
                     (SE.Star (starred (@SE.Inj _ _ _) (pures s) SE.Emp)
                              (starred (@SE.Const _ _ _) (other s) SE.Emp))).

      (** applySHeap **)
      Axiom applySHeap_wt_spec : forall cs U G U' G' s F,
        (forall e t,
          is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G) e t = true ->
          exprD funcs U G e t = exprD funcs U' G' (F e) t) ->
        WellTyped_sheap (typeof_funcs funcs) (SE.typeof_preds preds) (typeof_env U) (typeof_env G) s = true ->
        SE.ST.heq cs (SE.sexprD funcs preds U G (sheapD s))
                     (SE.sexprD funcs preds U' G' (sheapD (applySHeap F s))).

      Axiom applySHeap_spec : forall cs U G U' G' s F,
        (forall e t,
          exprD funcs U G e t = exprD funcs U' G' (F e) t) ->
        SE.ST.heq cs (SE.sexprD funcs preds U G (sheapD s))
                     (SE.sexprD funcs preds U' G' (sheapD (applySHeap F s))).

      Axiom applySHeap_typed_eq : forall tf tp U G U' G' s F,
        (forall e t,
          is_well_typed tf U G e t = is_well_typed tf U' G' (F e) t) ->
        WellTyped_sheap tf tp U G s = WellTyped_sheap tf tp U' G' (applySHeap F s).

      Axiom applySHeap_typed_impl : forall tf tp U G U' G' s F,
        (forall e t,
          is_well_typed tf U G e t = true ->
          is_well_typed tf U' G' (F e) t = true) ->
        WellTyped_sheap tf tp U G s = true ->
        WellTyped_sheap tf tp U' G' (applySHeap F s) = true.

    End facts.
  End env.
End SepHeap.

Module Make (SE : SepExpr) <: SepHeap with Module SE := SE.
  Module Import SE := SE.
  Module ST := SE.ST.

  Module Import SE_FACTS := SepExpr.SepExprFacts SE.

  Section env.
    Variable types : list type.
    Variable pcType : tvar.
    Variable stateType : tvar.

    Variable funcs : functions types.
    Variable preds : predicates types pcType stateType.

    (** A more efficient representation for sexprs. **)
    Record SHeap : Type :=
    { impures : MM.mmap (exprs types)
    ; pures   : list (expr types)
    ; other   : list (ST.hprop (tvarD types pcType) (tvarD types stateType) nil)
    }.

    Definition SHeap_empty : SHeap :=
      {| impures := @MM.empty _
       ; pures   := nil
       ; other   := nil
       |}.

    Existing Instance himp_rel_relation.
    Existing Instance heq_rel_relation.
    Hint Rewrite heq_star_emp_l heq_star_emp_r : hprop.

    Theorem ST_himp_himp : forall (U G : env types) cs L R,
      SE.himp funcs preds U G cs L R ->
      ST.himp cs (sexprD funcs preds U G L) (sexprD funcs preds U G R).
    Proof.
      clear. auto.
    Qed.

    Theorem ST_heq_heq : forall (U G : env types) cs L R,
      heq funcs preds U G cs L R ->
      ST.heq cs (sexprD funcs preds U G L) (sexprD funcs preds U G R).
    Proof.
      clear. auto.
    Qed.


    (** sexprD (U ++ U') (G ++ G') s =
     ** sexprD (U ++ U'' ++ U') (G ++ G'' ++ G') (liftSHeap (length U) (length U'') (length G) (length G'') s)
     **)
    Definition liftSHeap (ua ub : nat) (a b : nat) (s : SHeap) : SHeap :=
      {| impures := MM.mmap_map (map (liftExpr ua ub a b)) (impures s)
       ; pures   := map (liftExpr ua ub a b) (pures s)
       ; other   := other s
       |}.

    Fixpoint star_SHeap (l r : SHeap) : SHeap :=
      {| impures := MM.mmap_join (impures l) (impures r)
       ; pures := pures l ++ pures r
       ; other := other l ++ other r
       |}.

    Fixpoint hash (s : sexpr types pcType stateType) : ( variables * SHeap ) :=
      match s with
        | Emp => (nil, SHeap_empty)
        | Inj p => (nil,
          {| impures := MM.empty _
           ; pures := p :: nil
           ; other := nil
           |})
        | Star l r =>
          let (vl, hl) := hash l in
          let (vr, hr) := hash r in
          let nr := length vr in
          (vl ++ vr,
            star_SHeap (liftSHeap 0 0 0 nr hl) (liftSHeap 0 0 nr (length vl) hr))
        | Exists t b =>
          let (v, b) := hash b in
          (t :: v, b)
        | Func f a =>
          (nil,
           {| impures := MM.mmap_add f a (MM.empty _)
            ; pures := nil
            ; other := nil
           |})
        | Const c =>
          (@nil tvar,
           {| impures := MM.empty _
            ; pures := @nil (expr types)
            ; other := c :: nil
            |})
      end.

    Definition starred (T : Type) (F : T -> sexpr types pcType stateType) (ls : list T) (base : sexpr _ _ _)
      : sexpr _ _ _ :=
      fold_right (fun x a => match a with
                               | Emp => F x
                               | _ => Star (F x) a
                             end) base ls.

    Definition sheapD (h : SHeap) : sexpr types pcType stateType :=
      let a := starred (@Const _ _ _) (other h) Emp in
      let a := starred (@Inj _ _ _) (pures h) a in
      let a := FM.fold (fun k => starred (Func k)) (impures h) a in
      a.

    Definition WellTyped_impures (tf : tfunctions) (tp : tpredicates) (tU tG : tenv) (imps : MM.mmap (exprs types)) : bool :=
      FM.fold (fun p argss acc =>
        acc && match argss , nth_error tp p with
                 | nil , _ => true
                 | _ , None => false
                 | argss , Some ts =>
                   allb (fun args => all2 (is_well_typed tf tU tG) args ts) argss
               end) imps true.

    Theorem WellTyped_impures_spec_eq : forall tf tp tU tG impures,
        WellTyped_impures tf tp tU tG impures =
        FM.fold (fun p argss acc =>
        acc && match argss , nth_error tp p with
                 | nil , _ => true
                 | _ , None => false
                 | argss , Some ts =>
                   allb (fun args => all2 (is_well_typed tf tU tG) args ts) argss
               end) impures true.
    Proof. reflexivity. Qed.

    Definition WellTyped_sheap (tf : tfunctions) (tp : tpredicates) (tU tG : tenv) (h : SHeap) : bool :=
      WellTyped_impures tf tp tU tG (impures h) && allb (fun e => is_well_typed tf tU tG e tvProp) (pures h).

    Theorem WellTyped_sheap_eq : forall (tf : tfunctions) (tp : SE.tpredicates) (tU tG : tenv) (h : SHeap),
      WellTyped_sheap tf tp tU tG h =
      WellTyped_impures tf tp tU tG (impures h) &&
      allb (fun e => is_well_typed tf tU tG e tvProp) (pures h).
    Proof.
      clear. reflexivity.
    Qed.

    Lemma starred_const_well_typed : forall tf tp tU tG e x,
      WellTyped_sexpr tf tp tU tG (starred (@Const _ _ _) x e) = WellTyped_sexpr tf tp tU tG e.
    Proof.
      clear. induction x; simpl; intros; auto.
      destruct (starred (Const (stateType:=stateType)) x e); auto.
    Qed.

    Lemma starred_pures_well_typed : forall tf tp tU tG e x,
      WellTyped_sexpr tf tp tU tG (starred (@Inj _ _ _) x e) =
      allb (fun e => is_well_typed tf tU tG e tvProp) x && WellTyped_sexpr tf tp tU tG e.
    Proof.
      clear. induction x; simpl; intros; auto.
      consider (is_well_typed tf tU tG a tvProp); intros;
      destruct (starred (Inj (stateType:=stateType)) x e); simpl in *; think; auto.
      rewrite <- IHx. auto.
    Qed.

    Lemma starred_funcs_well_typed : forall tf tp tU tG p,
      forall e x,
      WellTyped_sexpr tf tp tU tG (starred (@Func _ _ _ p) x e) =
      match x , nth_error tp p with
        | nil , _ => true
        | _ , None => false
        | x , Some ts =>
          allb (fun args => all2 (is_well_typed tf tU tG) args ts) x
      end && WellTyped_sexpr tf tp tU tG e.
    Proof.
      clear. induction x; simpl; intros; auto.
      destruct x; simpl in *.
      { destruct e; simpl;
          repeat match goal with
                   | [ |- context [ nth_error ?a ?b ] ] => destruct (nth_error a b)
                   | [ |- context [ all2 ?a ?b ?c ] ] => destruct (all2 a b c)
                 end; auto. }
      { repeat (simpl in *;
        match goal with
          | [ |- context [ match ?X with _ => _ end ] ] => destruct X
        end); auto. }
    Qed.

    Theorem WellTyped_sheap_WellTyped_sexpr : forall tf tp tU tG h,
      WellTyped_sheap tf tp tU tG h = SE.WellTyped_sexpr tf tp tU tG (sheapD h).
    Proof.
      clear. intros. destruct h. unfold WellTyped_sheap, WellTyped_impures, sheapD; simpl.
      eapply MF.PROPS.fold_rec with (m := impures0); intros; simpl.
      { rewrite NatMap.IntMapProperties.fold_Empty; eauto with typeclass_instances.
        rewrite starred_pures_well_typed. rewrite starred_const_well_typed. simpl.
        symmetry; apply andb_true_r. }
      { rewrite NatMap.IntMapProperties.fold_Add with (eqA := fun x y => WellTyped_sexpr tf tp tU tG x = WellTyped_sexpr tf tp tU tG y). 5: eauto. 5: eauto.
        destruct e. simpl. rewrite andb_true_r. eauto.
        rewrite starred_funcs_well_typed. rewrite <- H2.
        rewrite andb_comm. rewrite andb_assoc. rewrite andb_assoc. rewrite andb_comm.
        repeat rewrite <- andb_assoc. f_equal. apply andb_comm.

        { clear; econstructor; auto. red. intros; think. auto. }
        { clear. repeat red; intros; subst. induction y0; simpl; intros; auto.
          consider (starred (Func y) y0 x1);
          consider (starred (Func y) y0 y1); intros; simpl in *; think;
            repeat match goal with
                     | [ |- context [ nth_error ?X ?Y ] ] => destruct (nth_error X Y)
                     | [ H : true = _ |- _ ] => rewrite <- H
                     | [ H : false = _ |- _ ] => rewrite <- H
                   end; auto using andb_true_r. }
        { clear. repeat (red; intros; subst).
          repeat rewrite starred_funcs_well_typed. destruct e; destruct e'; auto.
          generalize (l :: e); generalize (l0 :: e'). intros.
          destruct (nth_error tp k); destruct (nth_error tp k'); auto.
          rewrite andb_comm. rewrite <- andb_assoc. f_equal. apply andb_comm.
          rewrite andb_false_r. auto.
          rewrite andb_false_r; auto. } }
    Qed.

    Definition sheapD' (h : SHeap) : sexpr types pcType stateType :=
      Star (FM.fold (fun k => starred (Func k)) (impures h) Emp)
           (Star (starred (@Inj _ _ _) (pures h) Emp)
                 (starred (@Const _ _ _) (other h) Emp)).

    Definition impuresD (imp : MM.mmap (exprs types)) : sexpr types pcType stateType :=
      FM.fold (fun k ls acc =>
        Star (starred (Func k) ls Emp) acc) imp Emp.

    Section with_envs.
      Variables U G : env types.
      Variable cs : codeSpec (tvarD types pcType) (tvarD types stateType).

      Local Notation "a '<===>' b" := (heq funcs preds U G cs a b) (at level 60, only parsing).

      Theorem starred_def : forall (T : Type) (F : T -> SE.sexpr _ _ _) (ls : list T) (base : SE.sexpr _ _ _),
        (starred F ls base) <===>
        (fold_right (fun x a => SE.Star (F x) a) base ls).
      Proof.
        induction ls; simpl; intros.
          reflexivity.
          specialize (IHls base). revert IHls.
          case_eq (starred F ls base); intros;
            rewrite <- IHls; heq_canceler.
      Qed.

      Theorem starred_base : forall T F ls base,
        (@starred T F ls base) <===> (SE.Star base (@starred T F ls Emp)).
      Proof.
        intros. repeat rewrite starred_def.
        revert base. induction ls; simpl in *; intros.
          heq_canceler.
          rewrite IHls. heq_canceler.
      Qed.

      Ltac heq_canceler :=
        repeat match goal with
                 | [ H : SE.heq _ _ _ _ _ _ _ |- _ ] => rewrite H
                 | [ |- context [ starred ?F ?L ?B ] ] =>
                   match B with
                     | SE.Emp => fail 1
                     | _ => rewrite (@starred_base _ F L B)
                   end
               end;
        SE_FACTS.heq_canceler.

      Global Add Parametric Morphism : (fun k0 : nat => starred (Func k0)) with
        signature (eq ==> eq ==> heq funcs preds U G cs ==> heq funcs preds U G cs)
        as star_himp_mor'.
      Proof.
        intros. repeat rewrite starred_def.
        revert H. revert x; revert y1.
        induction y0; unfold heq in *; simpl in *; intros; try eauto.
        rewrite IHy0; eauto. heq_canceler.
      Qed.

      Lemma transpose_neqkey_starred : NatMap.IntMapProperties.transpose_neqkey (SE.heq funcs preds U G cs)
        (fun k0 : nat => starred (Func k0)).
      Proof.
        red. intros. rewrite starred_base. symmetry.
        rewrite starred_base. repeat rewrite starred_base with (base := a).
        heq_canceler.
      Qed.
      Lemma transpose_neqkey_Star (X : Type) F : NatMap.IntMapProperties.transpose_neqkey (heq funcs preds U G cs)
        (fun (k0 : nat) (ls : X) (a1 : sexpr types _ _) => Star (F k0 ls) a1).
      Proof.
        red. intros. heq_canceler.
      Qed.

      Hint Resolve transpose_neqkey_starred transpose_neqkey_Star : hprop.
      Hint Extern 1 (Morphisms.Proper _ _) =>
        (unfold Morphisms.Proper, Morphisms.respectful; intros; subst;
          repeat match goal with
                   | [ H : heq _ _ _ _ _ _ _ |- _ ] => rewrite H
                 end; reflexivity) : hprop.
      Hint Extern 1 (MM.PROPS.transpose_neqkey _ _) =>
        (clear; red; intros; subst; repeat rewrite MM.FACTS.add_o;
          repeat match goal with
                   | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                     destruct (FM.E.eq_dec X Y)
                   | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
                 end; solve [ auto | exfalso; auto | heq_canceler ]) : hprop.


      Theorem impuresD_Add : forall f argss i i',
        MM.PROPS.Add f argss i i' ->
        ~FM.In f i ->
        SE.heq funcs preds U G cs
          (impuresD i')
          (SE.Star (starred (SE.Func f) argss SE.Emp) (impuresD i)).
      Proof.
        unfold impuresD; intros.
        rewrite MM.PROPS.fold_Add; eauto with typeclass_instances hprop.
          heq_canceler.
      Qed.

      Theorem impuresD_Empty : forall i,
        FM.Empty i ->
        SE.heq funcs preds U G cs (impuresD i) SE.Emp.
      Proof.
        unfold impuresD; intros.
        rewrite MM.PROPS.fold_Empty; eauto with typeclass_instances. heq_canceler.
      Qed.

      Theorem sheapD_def : forall s,
        SE.heq funcs preds U G cs
          (sheapD s)
          (SE.Star (impuresD (impures s))
                   (SE.Star (starred (@SE.Inj _ _ _) (pures s) SE.Emp)
                            (starred (@SE.Const _ _ _) (other s) SE.Emp))).
      Proof.
        intros; unfold sheapD.
        eapply MM.PROPS.fold_rec; intros.
          rewrite impuresD_Empty; eauto. heq_canceler.
          rewrite impuresD_Add; eauto. heq_canceler.
      Qed.

      Lemma sheapD_sheapD' : forall h,
        sheapD h <===> sheapD' h.
      Proof.
        destruct h. rewrite sheapD_def; unfold sheapD', impuresD; simpl.
        repeat eapply heq_star_frame; try reflexivity.
        generalize (@Emp types pcType stateType) at 2 3.
        clear. intros. eapply MM.PROPS.fold_rec with (m := impures0); intros.
          rewrite MM.PROPS.fold_Empty; eauto with typeclass_instances hprop. reflexivity.

          rewrite MM.PROPS.fold_Add; eauto with typeclass_instances hprop.
            rewrite H2. heq_canceler.
      Qed.

      Lemma starred_In : forall T (F : T -> sexpr _ _ _) x ls' b ls,
        (starred F (ls ++ x :: ls') b) <===> (Star (starred F (ls ++ ls') b) (F x)).
      Proof.
        intros. repeat rewrite starred_def. revert b.
        induction ls; intros; simpl; heq_canceler.
          rewrite IHls. heq_canceler.
      Qed.

      Lemma sheapD_pures : forall stn sm h,
        ST.satisfies cs (sexprD funcs preds U G (sheapD h)) stn sm ->
        AllProvable funcs U G (pures h).
      Proof.
        intros. eapply ST.satisfies_himp in H.
        Focus 2. rewrite sheapD_def. rewrite starred_def. reflexivity.
        simpl in *.

        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : ST.satisfies _ (ST.star _ _) _ _ |- _ ] =>
                   apply ST.satisfies_star in H
                 | [ H : _ /\ _ |- _ ] => destruct H
               end.
        revert H2; clear. revert x1.
        induction (pures h); simpl; auto.
        unfold Provable. destruct (exprD funcs U G a tvProp); intros; unfold BadInj in *;
        repeat match goal with
                 | [ H : exists x, _ |- _ ] => destruct H
                 | [ H : ST.satisfies _ (ST.star _ _) _ _ |- _ ] =>
                   apply ST.satisfies_star in H
                 | [ H : ST.satisfies _ (ST.inj _) _ _ |- _ ] =>
                   apply ST.satisfies_pure in H
                 | [ H : _ /\ _ |- _ ] => destruct H
                 | [ |- _ /\ _ ] => split
                 | [ |- _ ] => propxFo
               end; eauto.
      Qed.

      Lemma sheapD_pull_impure : forall h f argss,
        FM.find f (impures h) = Some argss ->
        (sheapD h) <===>
        (Star (sheapD {| impures := FM.remove f (impures h)
          ; pures   := pures h
          ; other   := other h |})
        (starred (Func f) argss Emp)).
      Proof.
        intros. repeat rewrite sheapD_def. simpl.
        rewrite impuresD_Add with (f := f) (argss := argss) (i := FM.remove f (impures h)).
        heq_canceler.
        unfold MM.PROPS.Add; intros; repeat rewrite MM.FACTS.add_o; repeat rewrite MM.FACTS.remove_o.
        destruct (FM.E.eq_dec f y); subst; auto.
        apply FM.remove_1; auto.
      Qed.

      Lemma fold_starred : forall X (F : nat -> X -> sexpr _ _ _) m b,
        (FM.fold (fun k ls a => Star (F k ls) a) m b) <===>
        (Star (FM.fold (fun k ls a => Star (F k ls) a) m Emp) b).
      Proof.
        do 2 intro.
        intro. apply NatMap.IntMapProperties.fold_rec with (m := m).
          intros. rewrite NatMap.IntMapProperties.fold_Empty; eauto with typeclass_instances.
          autorewrite with hprop. reflexivity.

          intros. erewrite MM.PROPS.fold_Add; eauto with typeclass_instances hprop.
          rewrite H2. heq_canceler.
      Qed.

      Theorem starred_app : forall T (F : T -> _) a b B,
        (starred F (a ++ b) B) <===> (starred F a (starred F b B)).
      Proof.
        intros; repeat rewrite starred_def.
        induction a; simpl; intros; repeat rewrite starred_def; try reflexivity.
        rewrite IHa. reflexivity.
      Qed.

      Theorem starred_perm : forall T L R,
        Permutation.Permutation L R ->
        forall (F : T -> _) base,
          (starred F L base) <===> (starred F R base).
      Proof.
        clear. intros.
        repeat rewrite starred_def.
        induction H; simpl; intros;
          repeat match goal with
                   | [ H : _ |- _ ] => rewrite H
                 end; try reflexivity; heq_canceler.
      Qed.

      Theorem impuresD_Equiv : forall a b,
        MM.mmap_Equiv a b ->
        (impuresD a) <===> (impuresD b).
      Proof.
        intro. eapply MM.PROPS.map_induction with (m := a); intros.
        { repeat rewrite impuresD_Empty; auto. reflexivity.
          apply MF.find_empty_iff. intros.
          destruct H0.
          specialize (H0 k).
          eapply MF.find_empty_iff with (k := k) in H.
          apply MM.FACTS.not_find_mapsto_iff.
          intro. apply H0 in H2. apply MM.FACTS.not_find_mapsto_iff in H. auto. }
        { generalize (@MF.Equiv_Add _ _ _ _ _ _ _ H2 H0 H1); intro.
          do 2 destruct H3. intuition.
          repeat rewrite impuresD_Add by eauto. symmetry.
          repeat rewrite impuresD_Add by eauto. symmetry.
          rewrite H; eauto. rewrite starred_perm; eauto. heq_canceler. }
      Qed.

      Lemma multimap_join_star : forall
        (impures0 impures1 : MM.mmap (exprs types)) B,
        (FM.fold
          (fun (k : nat) (ls : list (exprs types)) acc =>
            Star (starred (Func k) ls Emp) acc)
          (MM.mmap_join impures0 impures1) B)
        <===>
        (FM.fold
          (fun (k : nat) (ls : list (exprs types)) acc =>
            Star (starred (Func k) ls Emp) acc) impures0
          (FM.fold
            (fun (k : nat) (ls : list (exprs types)) acc =>
              Star (starred (Func k) ls Emp) acc) impures1 B)).
      Proof.
        unfold MM.mmap_join.
        intro. apply NatMap.IntMapProperties.map_induction with (m := impures0).
        * intros.
          repeat rewrite NatMap.IntMapProperties.fold_Empty with (m := m); eauto with typeclass_instances.
          reflexivity.

        * intros.
          generalize (@NatMap.IntMapProperties.fold_Add (list (exprs types)) _ (@FM.Equal (list (exprs types)))).
          intro.
          rewrite NatMap.IntMapProperties.fold_Equal; try solve [ clear; eauto with typeclass_instances ].
          4: eapply H2; eauto with typeclass_instances.
          clear H2. simpl in *.
          unfold exprs, MM.mmap_extend; simpl in *.
          match goal with
            | [ |- context [ FM.find ?x ?y ] ] => remember y
          end.
          case_eq (FM.find x t); intros.
          { subst.
            rewrite NatMap.IntMapProperties.fold_Equal; eauto with typeclass_instances.
            4: eapply MF.add_remove_Equal.
            symmetry.
            rewrite NatMap.IntMapProperties.fold_Add.
            6: eassumption.
            5: eauto.
            2: eauto with typeclass_instances.
            rewrite fold_starred.
            rewrite NatMap.IntMapProperties.fold_Add with (m2 := impures1).
            2: eauto with typeclass_instances.
            instantiate (3 := x). instantiate (2 := l).
            instantiate (1 := FM.remove x impures1).
            rewrite NatMap.IntMapProperties.fold_add.
            rewrite starred_app. heq_canceler.

            generalize (@MM.mmap_join_remove_acc _ x m impures1 H0). unfold MM.mmap_join. intro.
            symmetry. rewrite NatMap.IntMapProperties.fold_Equal.
            5: eapply H3. clear H3.
            rewrite H. rewrite fold_starred with (b := FM.fold _ _ _). heq_canceler. eauto with typeclass_instances.

            solve [ clear; eauto with typeclass_instances hprop ].

            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            apply FM.remove_1; auto.
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            apply FM.remove_1; auto.

            {
              generalize MM.mmap_join_o.
              unfold MM.mmap_join. intros. unfold MM.mmap_extend in H3. rewrite H3 in H2; auto.
              apply MM.PROPS.F.not_find_in_iff in H0. unfold exprs in H0. rewrite H0 in H2.

              revert H2; clear; intros.
              unfold NatMap.IntMapProperties.Add; intros.
                repeat (rewrite NatMap.IntMapFacts.add_o || rewrite NatMap.IntMapFacts.remove_o).
                destruct (NatMap.Ordered_nat.eq_dec x y); subst; auto.
            }

            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
            solve [ clear; eauto with typeclass_instances hprop ].
        }
        { subst.
          rewrite NatMap.IntMapProperties.fold_add; eauto with typeclass_instances.
          rewrite H. symmetry. rewrite fold_starred.
          rewrite NatMap.IntMapProperties.fold_Add; eauto with typeclass_instances.
          symmetry. rewrite fold_starred with (b := FM.fold _ _ _). heq_canceler.

          repeat (red; intros; subst). rewrite H3. heq_canceler.
          red; intros; heq_canceler.
          repeat (red; intros; subst). rewrite H3; heq_canceler.
          red; intros; heq_canceler.
          intro.
          apply NatMap.IntMapProperties.F.in_find_iff in H3. auto.
        }
        eauto with typeclass_instances.
        solve [ clear; eauto with typeclass_instances hprop ].
        solve [ clear; eauto with typeclass_instances hprop ].
        clear; repeat (red; intros; subst). unfold MM.mmap_extend. rewrite H.
          destruct (FM.find (elt:=list (exprs types)) y y1); try rewrite H; reflexivity.

        eapply MM.transpose_neqkey_mmap_extend.
      Qed.

      Lemma star_SHeap_denote : forall s1 s2,
        (Star (sheapD s1) (sheapD s2)) <===> (sheapD (star_SHeap s1 s2)).
      Proof.
        intros. symmetry. repeat rewrite sheapD_def.
        destruct s1; destruct s2; intros; simpl; unfold star_SHeap; simpl.
        match goal with
          | [ |- heq _ _ _ _ _ _ (Star (Star ?FL (Star ?PL ?OL)) (Star ?FR (Star ?PR ?OR))) ] =>
            transitivity (Star (Star FL FR) (Star (Star PL PR) (Star OL OR)))
        end.
        repeat rewrite starred_app.
        unfold impuresD.
        rewrite multimap_join_star; auto. heq_canceler.
        rewrite <- fold_starred. heq_canceler.

        heq_canceler.
      Qed.


    End with_envs.

    Ltac heq_canceler :=
        repeat match goal with
                 | [ H : SE.heq _ _ _ _ _ _ _ |- _ ] => rewrite H
                 | [ |- context [ starred ?F ?L ?B ] ] =>
                   match B with
                     | SE.Emp => fail 1
                     | _ => rewrite (@starred_base _ _ _ _ F L B)
                   end
               end;
        SE_FACTS.heq_canceler.

    Hint Resolve transpose_neqkey_starred transpose_neqkey_Star : hprop.
    Hint Extern 1 (Morphisms.Proper _ _) =>
      (unfold Morphisms.Proper, Morphisms.respectful; intros; subst;
        repeat match goal with
                 | [ H : heq _ _ _ _ _ _ _ |- _ ] => rewrite H
               end; reflexivity) : hprop.
    Hint Extern 1 (MM.PROPS.transpose_neqkey _ _) =>
      (clear; red; intros; subst; repeat rewrite MM.FACTS.add_o;
        repeat match goal with
                 | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                   destruct (FM.E.eq_dec X Y)
                 | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
               end; solve [ auto | exfalso; auto | heq_canceler ]) : hprop.

    Lemma heq_ex : forall U G cs t P Q,
      (forall v : tvarD types t, heq funcs preds U (existT (tvarD types) t v :: G) cs P Q) ->
      heq funcs preds U G cs (Exists t P) (Exists t Q).
    Proof.
      unfold heq; simpl; intros; apply ST.heq_ex; auto.
    Qed.

    Lemma heq_existsEach : forall cs X v Y (P Q : sexpr types pcType stateType),
      (forall Z, map (@projT1 _ _) Z = rev v -> heq funcs preds X (Z ++ Y) cs P Q) ->
      heq funcs preds X Y cs (existsEach v P) (existsEach v Q).
    Proof.
      induction v; simpl; intros.
        specialize (H nil); simpl in *; auto.

        apply heq_ex. intros. eapply IHv. intros.
        simpl. specialize (H (Z ++ @existT _ _ _ v0 :: nil)). rewrite map_app in *.
        rewrite H0 in *. simpl in *.
        rewrite app_ass in *. simpl in *. auto.
    Qed.

    Lemma existsEach_app : forall X cs b a Y (P : sexpr _ _ _),
      heq funcs preds X Y cs (existsEach a (existsEach b P)) (existsEach (a ++ b) P).
    Proof.
      induction a; simpl.
      reflexivity.
      intros. apply heq_ex; intros. apply IHa.
    Qed.

    Lemma star_pull_exists : forall EG cs a G s s2,
      heq funcs preds EG G cs (Star (Exists a s) s2) (Exists a (Star s (liftSExpr 0 0 0 1 s2))).
    Proof.
      intros. unfold heq. simpl. rewrite ST.heq_ex_star. apply ST.heq_ex. intros.
      apply ST.heq_star_cancel.
       apply (liftSExpr_sexprD funcs preds cs s2 nil EG nil nil G (existT _ a v :: nil)).
    Qed.

    Lemma star_pull_existsEach : forall EG cs v G s s2,
      heq funcs preds EG G cs (Star (existsEach v s) s2)
                              (existsEach v (Star s (liftSExpr 0 0 0 (length v) s2))).
    Proof.
      induction v; simpl.
        intros; rewrite liftSExpr_0. reflexivity.

        intros.
        rewrite star_pull_exists. apply heq_ex. intros.
        rewrite IHv.

        rewrite liftSExpr_combine. reflexivity.
    Qed.

    Lemma starred_liftSExpr : forall F ua ub a b (ls : exprs types) base,
      (forall a0, liftSExpr ua ub a b (F a0) = F (liftExpr ua ub a b a0)) ->
      liftSExpr ua ub a b (starred F ls base) = starred F (map (liftExpr ua ub a b) ls) (liftSExpr ua ub a b base).
    Proof.
      induction ls; simpl; intros; try reflexivity.
      case_eq (starred F ls base); intros;
        rewrite <- IHls; repeat rewrite H0; simpl; repeat rewrite H; simpl; eauto.
    Qed.

    Lemma liftSExpr_existsEach : forall EG cs v0 s G n v,
      heq funcs preds EG G cs
        (liftSExpr 0 0 n v (existsEach v0 s))
        (existsEach v0 (liftSExpr 0 0 (n + length v0) v s)).
    Proof.
      induction v0; simpl; intros.
        intros. rewrite Plus.plus_0_r. reflexivity.

        apply heq_ex; intros. rewrite IHv0. cutrewrite (S n + length v0 = n + S (length v0)); try reflexivity; omega.
    Qed.

    Lemma skipn_skipn : forall T a (ls : list T) b,
      skipn b (skipn a ls) = skipn (b + a) ls.
    Proof.
      clear; induction a; simpl; intros.
        rewrite Plus.plus_0_r. auto.
        rewrite Plus.plus_comm. simpl. destruct ls; auto. destruct b; auto.
        rewrite IHa. rewrite Plus.plus_comm. auto.
    Qed.

    Lemma heq_liftSExpr : forall cs EG G G' G'' P Q,
      heq funcs preds EG (G ++ G'') cs P Q ->
      heq funcs preds EG (G ++ G' ++ G'') cs (liftSExpr 0 0 (length G) (length G') P) (liftSExpr 0 0 (length G) (length G') Q).
    Proof.
      unfold heq; intros.
      generalize (liftSExpr_sexprD funcs preds cs P nil EG nil). simpl in *.
      generalize (liftSExpr_sexprD funcs preds cs Q nil EG nil). simpl in *. intros.
      etransitivity. symmetry. eapply H1. rewrite H. eauto.
    Qed.

    Lemma sheapD_sexprD_liftVars : forall EG cs s G G' G'',
      heq funcs preds EG (G ++ G' ++ G'') cs
        (liftSExpr 0 0 (length G) (length G') (sheapD' s))
        (sheapD' (liftSHeap 0 0 (length G) (length G') s)).
    Proof.
      destruct s; unfold liftSHeap, sheapD'; simpl; intros; repeat apply heq_star_frame; intros.
      { clear. change Emp with (liftSExpr 0 0 (length G) (length G') (@Emp types pcType stateType)) at 2.
        generalize (@Emp types pcType stateType).
        unfold MM.mmap_map. intros. rewrite MF.fold_map_fusion; eauto with typeclass_instances.
        { revert s.
          apply NatMap.IntMapProperties.map_induction with (m := impures0); intros.
          repeat (rewrite MM.PROPS.fold_Empty; eauto with typeclass_instances). reflexivity.

          symmetry. rewrite MM.PROPS.fold_Add. 6: eauto. 5: eauto. 2: eauto with typeclass_instances.
          rewrite starred_base. rewrite <- H. clear H.
          assert (forall base, heq funcs preds EG (G ++ G' ++ G'') cs
            (starred (Func x) (map (map (liftExpr 0 0 (length G) (length G'))) e) (liftSExpr 0 0 (length G) (length G') base))
            (liftSExpr 0 0 (length G) (length G') (starred (Func x) e base))).
          { clear.
            induction e; intros; try reflexivity. rewrite starred_def. simpl. rewrite <- starred_def.
            rewrite IHe. solve [ destruct (starred (Func x) e base); simpl; heq_canceler ]. }
          rewrite H with (base := Emp).
          change (Star
            (liftSExpr 0 0 (length G) (length G')
              (FM.fold
                (fun (k : FM.key) => starred (Func k)) m s))
            (liftSExpr 0 0 (length G) (length G') (starred (Func x) e Emp)))
            with (liftSExpr 0 0 (length G) (length G')
              (Star
                (FM.fold
                  (fun (k : FM.key) => starred (Func k)) m s)
                (starred (Func x) e Emp))).
          eapply heq_liftSExpr.

          symmetry.
          rewrite MM.PROPS.fold_Add. 6: eauto. rewrite <- starred_base. reflexivity.
          eauto with typeclass_instances hprop.
          eauto with typeclass_instances hprop.
          clear; red; intros; subst; repeat rewrite MM.FACTS.add_o;
            repeat match goal with
                     | [ |- context [ FM.E.eq_dec ?X ?Y ] ] =>
                       destruct (FM.E.eq_dec X Y)
                     | [ H : FM.E.eq ?X ?Y |- _ ] => rewrite H in *
                   end; auto.
          heq_canceler.
          eauto with typeclass_instances hprop.
          clear; do 4 (red; intros; subst); heq_canceler.

          clear; red; intros; subst; repeat rewrite MM.FACTS.add_o.
          heq_canceler. }
          eapply transpose_neqkey_starred. }

        Opaque starred.
        { symmetry. rewrite starred_def. induction pures0; try reflexivity.
          simpl. rewrite IHpures0.
          match goal with
            | [ |- heq _ _ _ _ _ ?X _ ] =>
              change X with
                (liftSExpr 0 0 (length G) (length G') (Star (Inj a) (starred (@Inj types pcType stateType) pures0 Emp)))
          end.
          apply heq_liftSExpr. symmetry. repeat rewrite starred_def. simpl. heq_canceler. }

        { symmetry. etransitivity. rewrite starred_def. reflexivity. induction other0; try reflexivity.
          simpl. rewrite IHother0.
          match goal with
            | [ |- heq _ _ _ _ _ ?X _ ] =>
              change X with
                (liftSExpr 0 0 (length G) (length G') (Star (Const a) (starred (@Const types pcType stateType) other0 Emp)))
          end.
          apply heq_liftSExpr. symmetry. repeat rewrite starred_def. simpl. reflexivity. }
    Qed.

    Lemma hash_denote' : forall EG cs (s : sexpr _ _ _) G,
      heq funcs preds EG G cs s (existsEach (fst (hash s)) (sheapD' (snd (hash s)))).
    Proof.
      Opaque star_SHeap.
      induction s; simpl; try solve [ unfold sheapD'; simpl; intros; repeat (rewrite heq_star_emp_r || rewrite heq_star_emp_l); reflexivity ].
      { (** Star **)
        intros. rewrite IHs1 at 1. intros.
        destruct (hash s1); destruct (hash s2); simpl in *.
        rewrite IHs2.
        rewrite <- (@existsEach_app EG cs) with (Y := G).
        rewrite star_pull_existsEach. apply heq_existsEach. intros.
        rewrite heq_star_comm.

        rewrite liftSExpr_existsEach.
        rewrite star_pull_existsEach. eapply heq_existsEach; intros.
        generalize star_SHeap_denote.
        symmetry. rewrite <- sheapD_sheapD'.
        rewrite <- star_SHeap_denote. simpl plus.
        cutrewrite (length v0 = length Z0).
        cutrewrite (length v = length Z).
        repeat rewrite sheapD_sheapD'.
        rewrite sheapD_sexprD_liftVars.
        rewrite sheapD_sexprD_liftVars with (G := nil). heq_canceler.
        rewrite <- rev_length; rewrite <- H; apply map_length.
        rewrite <- rev_length; rewrite <- H0; apply map_length. }

      { (** Exists **)
        unfold sheapD'; simpl; intros. case_eq (hash s); intros; simpl.
        eapply heq_ex. intros. specialize (IHs (existT (tvarD types) t v0 :: G)). simpl in *.
        rewrite H in IHs. simpl in *. eauto. }
    Qed.

    Theorem hash_denote : forall EG G cs (s : sexpr _ _ _),
      heq funcs preds EG G cs s (existsEach (fst (hash s)) (sheapD (snd (hash s)))).
    Proof.
      intros. specialize (@hash_denote' EG cs s G). etransitivity.
      eassumption. apply heq_existsEach. intros. rewrite sheapD_sheapD'. reflexivity.
    Qed.

    Lemma WellTyped_impures_eq : forall tf tp tU tG impures,
      WellTyped_impures tf tp tU tG impures = true <->
      (forall k v, FM.find k impures = Some v ->
        match v with
          | nil => True
          | _ => match nth_error tp k with
                   | None => False
                   | Some ts =>
                     allb (fun argss => all2 (is_well_typed tf tU tG) argss ts) v = true
                 end
        end).
    Proof.
      clear. do 5 intro. unfold WellTyped_impures. eapply MF.PROPS.map_induction with (m := impures0); intros.
      { rewrite MF.PROPS.fold_Empty; eauto with typeclass_instances. split; intro; auto.
        intros. exfalso. rewrite MF.find_Empty in H1; auto. congruence. }
      { rewrite MF.PROPS.fold_Add. 5: eauto. 5: eauto. split; intros.
        { destruct (FM.E.eq_dec k x); subst.
          { specialize (H1 x).
            rewrite H3 in H1. rewrite MF.FACTS.add_o in H1. destruct (FM.E.eq_dec x x); try congruence.
            inversion H1; clear H1; subst. clear e0. destruct e; auto.
            apply andb_true_iff in H2. destruct H2. destruct (nth_error tp x); auto; congruence. }
          { apply andb_true_iff in H2. destruct H2. eapply H in H2. eauto.
            specialize (H1 k). rewrite H3 in H1. rewrite MF.FACTS.add_o in H1.
            destruct (FM.E.eq_dec x k); subst; try congruence. } }
        { apply andb_true_iff; split. apply H. intros.
          specialize (H1 k). rewrite MF.FACTS.add_o in H1. destruct (FM.E.eq_dec x k); subst.
          exfalso. apply MF.FACTS.find_mapsto_iff in H3. apply H0.
          exists v. auto. rewrite H3 in H1. eapply H2; eauto.

          specialize (H1 x). rewrite MF.FACTS.add_o in H1. destruct (FM.E.eq_dec x x); try congruence.
          specialize (H2 _ _ H1). destruct e; auto. destruct (nth_error tp x); auto. }
        eauto with typeclass_instances.
        { clear; repeat (red; intros; subst). reflexivity. }
        { clear; repeat (red; intros; subst). repeat rewrite <- andb_assoc. f_equal.
          apply andb_comm. } }
    Qed.

    Lemma eq_iff : forall a b A B,
      (a = true <-> A) ->
      (b = true <-> B) ->
      (A <-> B) ->
      a = b.
    Proof.
      clear. destruct a; destruct b; intros; intuition.
    Qed.

    Lemma andb_iff : forall a b A B,
      (a = true <-> A) ->
      (b = true <-> B) ->
      (a && b = true <-> A /\ B).
    Proof.
      clear. destruct a; destruct b; intros; intuition.
    Qed.

    Theorem WellTyped_sheap_weaken : forall tf tp tU tG tU' tG' h,
      WellTyped_sheap tf tp tU tG h = true ->
      WellTyped_sheap tf tp (tU ++ tU') (tG ++ tG') h = true.
    Proof.
      clear. unfold WellTyped_sheap. simpl; intros.
      think. apply andb_true_iff. split. clear - H.
      { rewrite WellTyped_impures_eq in *. intros.
        eapply H in H0. destruct v; auto.
        destruct (nth_error tp k); auto.
        generalize dependent (e :: v). clear.
        intros. eapply allb_impl; eauto; intros.
        simpl in *. eapply all2_impl; eauto. intros. apply is_well_typed_weaken; auto. }
      { eapply allb_impl; eauto. intros. apply is_well_typed_weaken. auto. }
    Qed.

    Theorem WellTyped_sheap_star : forall tf tp tU tG h0 h1,
      WellTyped_sheap tf tp tU tG h0 && WellTyped_sheap tf tp tU tG h1 =
      WellTyped_sheap tf tp tU tG (star_SHeap h0 h1).
    Proof.
      Transparent star_SHeap.
      clear. destruct h0; destruct h1; unfold WellTyped_sheap, star_SHeap; simpl; intros.
      eapply eq_iff;
        repeat match goal with
                 | [ |- _ && _ = true <-> _ ] => eapply andb_iff
                 | [ |- WellTyped_impures _ _ _ _ _ = true <-> _ ] => eapply WellTyped_impures_eq
                 | [ |- _ ] => reflexivity
               end.
      split; intuition.
      { rewrite MM.mmap_join_o in H1.
        repeat match goal with
                 | [ H : match FM.find ?A ?B with _ => _ end = _ |- _ ] =>
                   consider (FM.find A B) ; intros
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ H : forall x y, FM.find _ _ = Some _ -> _ , H' : FM.find _ _ = _ |- _ ] =>
                   specialize (H _ _ H')
                 | [ H : match ?X with nil => _ | _ => _ end |- _ ] => destruct X; simpl in *
                 | [ H : match nth_error ?A ?B with _ => _ end |- _ ] => destruct (nth_error A B)
               end; auto;  think; repeat (rewrite allb_app || (apply andb_true_iff; split)); think; simpl; auto. }
      { rewrite allb_app. apply andb_true_iff. auto. }
      { consider (FM.find k impures1); intros.
        specialize (H0 k (v ++ l)). rewrite MM.mmap_join_o in H0.
        think. specialize (H0 refl_equal).
        destruct v; auto. simpl in *. destruct (nth_error tp k); auto.
        think. rewrite allb_app in H3. apply andb_true_iff in H3. intuition.
        specialize (H0 k v). rewrite MM.mmap_join_o in H0. think.
        apply H0. auto. }
      { rewrite allb_app in H1. apply andb_true_iff in H1. destruct H1; auto. }
      { consider (FM.find k impures0); intros.
        specialize (H0 k (l ++ v)). rewrite MM.mmap_join_o in H0. think. specialize (H0 refl_equal).
        destruct v. auto. destruct (nth_error tp k); destruct l; simpl in *; auto.
        think. rewrite allb_app in H3. simpl in *.  think; auto.
        specialize (H0 k v). rewrite MM.mmap_join_o in H0. think. eapply H0; auto. }
      { rewrite allb_app in H1. apply andb_true_iff in H1. destruct H1; auto. }
      Opaque star_SHeap.
    Qed.

    Lemma WellTyped_star_SHeap : forall tf tp tU tG h1 h2,
      WellTyped_sheap tf tp tU tG h1 = true ->
      WellTyped_sheap tf tp tU tG h2 = true ->
      WellTyped_sheap tf tp tU tG (star_SHeap h1 h2) = true.
    Proof.
      clear; intros. rewrite <- WellTyped_sheap_star. think. reflexivity.
    Qed.

    Opaque star_SHeap.

    Lemma fold_ext : forall U V (F F' : _ -> U -> V -> V),
      (forall k v a, F k v a = F' k v a) ->
      forall m a,
        FM.fold F m a = FM.fold F' m a.
    Proof.
      unfold FM.fold. destruct m. simpl. induction this; simpl; try reflexivity.
      inversion is_bst; subst. intros. think. auto.
    Qed.

    Lemma liftExpr_wt : forall (types : list type) tf
      (U U' U'' G G' G'' : list tvar)
      (e : expr types) (t : tvar),
      is_well_typed tf (U'' ++ U) (G'' ++ G) e t =
      is_well_typed tf (U'' ++ U' ++ U) (G'' ++ G' ++ G)
      (liftExpr (length U'') (length U') (length G'') (length G') e) t.
    Proof.
      clear. induction e; simpl; intros;
      repeat match goal with
               | [ |- context [ NPeano.ltb ?a ?b ] ] => consider (NPeano.ltb a b) ; intros
               | [ |- _ ] => rewrite nth_error_app_L by omega
               | [ |- _ ] => rewrite nth_error_app_R by omega
             end; think; auto.
      cutrewrite (length G' + x - length G'' - length G' = x - length G''); [ | omega ]. auto.
      cutrewrite (length U' + x - length U'' - length U' = x - length U''); [ | omega ]. auto.
      consider (nth_error tf f); auto; intros. consider (tvar_seqb t (TRange t0)); intros; auto. think.
      destruct t0; simpl in *. clear -H. revert TDomain; induction H; simpl; auto.
      destruct TDomain; auto. think.  auto.
    Qed.

    Lemma liftSHeap_wt : forall tf tp tU G G' G'' h,
      WellTyped_sheap tf tp tU (G ++ G'') h =
      WellTyped_sheap tf tp tU (G ++ G' ++ G'') (liftSHeap 0 0 (length G) (length G') h).
    Proof.
      clear. unfold liftSHeap, WellTyped_sheap, WellTyped_impures. intros; simpl.

      f_equal. unfold MM.mmap_map. rewrite MF.fold_map_fusion.

      eapply fold_ext; intros. f_equal. destruct v; simpl; auto. destruct (nth_error tp k); auto.
      generalize (liftExpr_wt (types := types) tf tU nil nil G'' G' G). simpl. repeat rewrite app_nil_r.
      intro.

      rewrite all2_map_1.
      erewrite all2_eq. 2: intros; rewrite H; reflexivity.
      destruct (all2
        (fun (x : expr types) (y : tvar) =>
          is_well_typed tf tU (G ++ G' ++ G'')
          (liftExpr 0 0 (length G) (length G') x) y) l t); auto.

      rewrite allb_map.

      apply allb_ext; auto. intros. rewrite all2_map_1. apply all2_eq; auto.
      auto with typeclass_instances.
      { repeat (red; intros; subst). repeat rewrite <- andb_assoc. f_equal. apply andb_comm. }
      { repeat (red; intros; subst). auto. }
      rewrite allb_map. apply allb_ext.
      generalize (liftExpr_wt (types := types) tf tU nil nil G'' G' G). simpl. auto.
    Qed.

    Theorem WellTyped_hash : forall tf tp tU tG (s : SE.sexpr types pcType stateType),
      SE.WellTyped_sexpr tf tp tU tG s =
      WellTyped_sheap tf tp tU (rev (fst (hash s)) ++ tG) (snd (hash s)).
    Proof.
      clear. intros tf tp tU tG s. revert tG.
      induction s; simpl; intros; unfold WellTyped_sheap; simpl in *; think; auto.
      { destruct (is_well_typed tf tU tG e tvProp); auto. }
      { destruct (hash s1); destruct (hash s2); simpl in *.
        rewrite <- WellTyped_sheap_eq. rewrite <- WellTyped_sheap_star.
        rewrite rev_app_distr. rewrite app_ass.
        f_equal.
        rewrite (liftSHeap_wt tf tp tU nil (rev v0) (rev v ++ tG)). simpl. rewrite rev_length. reflexivity.
        rewrite (liftSHeap_wt tf tp tU (rev v0) (rev v) tG). repeat rewrite rev_length. reflexivity. }
      { destruct (hash s); simpl in *. destruct s0; simpl in *.
        rewrite WellTyped_sheap_eq. simpl. repeat rewrite app_ass; reflexivity. }
      { unfold WellTyped_impures, MM.mmap_add. simpl. rewrite andb_true_r.
        rewrite MF.PROPS.fold_add; eauto with typeclass_instances.
        rewrite MF.PROPS.fold_Empty; eauto using FM.empty_1 with typeclass_instances.
        destruct (nth_error tp f); auto. simpl. destruct (all2 (is_well_typed tf tU tG) l t); auto.
        repeat (red; intros);
          repeat match goal with
                   | |- context [ match ?X with _ => _ end ] => destruct X
                   | |- _ => rewrite Bool.andb_true_l
                   | |- _ => rewrite Bool.andb_true_r
                   | |- context [ allb ?A ?B ] => destruct (allb A B)
                 end; try reflexivity.
        rewrite MF.FACTS.empty_in_iff; auto. }
    Qed.

(*
    Theorem WellTyped_hash : forall tf tp tU tG (s : SE.sexpr types pcType stateType),
      SE.WellTyped_sexpr tf tp tU tG s =
      WellTyped_sheap tf tp tU (rev (fst (hash s)) ++ tG) (snd (hash s)).
    Proof.
      clear. intros tf tp tU tG s. revert tG.
      induction s; simpl; intros; unfold WellTyped_sheap; simpl in *; think; auto.
      { destruct (hash s1). destruct (hash s2). simpl in *.
        eapply WellTyped_star_SHeap.
        apply IHs1 in H. rewrite rev_app_distr.
        rewrite (liftSHeap_wt tf tp tU nil (rev v0) (rev v ++ tG)) in H. rewrite app_ass. simpl in *.
        rewrite rev_length in H. auto.
        apply IHs2 in H0. rewrite rev_app_distr. rewrite app_ass.
        rewrite (liftSHeap_wt tf tp tU (rev v0) (rev v) tG) in H0. repeat rewrite rev_length in *; auto. }
      { destruct (hash s); simpl in *. destruct s0; simpl in *. eapply IHs in H.
        repeat rewrite app_ass in *. simpl in *. auto. }
      { unfold WellTyped_impures, MM.mmap_add. simpl. rewrite andb_true_r.
        unfold FM.fold, FM.Raw.fold. simpl. rewrite H. rewrite H0. auto. }
    Qed.
*)

    Definition applySHeap (F : expr types -> expr types) (sh : SHeap) : SHeap :=
      {| impures := MM.mmap_map (map F) (impures sh)
       ; pures := map F (pures sh)
       ; other := other sh
       |}.

    Theorem applySHeap_defn : forall F sh,
      applySHeap F sh =
      {| impures := MM.mmap_map (map F) (impures sh)
       ; pures := map F (pures sh)
       ; other := other sh
       |}.
    Proof. reflexivity. Qed.


    Lemma starred_nil : forall T U G cs (F : T -> _) B,
      heq funcs preds U G cs (starred F nil B) B.
    Proof.
      clear. reflexivity.
    Qed.


    Lemma starred_cons : forall T U G cs (F : T -> _) a A B,
      heq funcs preds U G cs (starred F (a :: A) B) (Star (F a) (starred F A B)).
    Proof.
      clear. intros; rewrite starred_def. simpl. rewrite <- starred_def. reflexivity.
    Qed.

    Theorem applySHeap_spec : forall cs U G U' G' s F,
      (forall e t,
        exprD funcs U G e t = exprD funcs U' G' (F e) t) ->
      SE.ST.heq cs (sexprD funcs preds U G (sheapD s))
                   (sexprD funcs preds U' G' (sheapD (applySHeap F s))).
    Proof.
      clear. intros.
      do 2 rewrite sheapD_def. simpl. repeat eapply SE.ST.heq_star_frame.
      { eapply MM.PROPS.map_induction with (m := impures s); intros.
        repeat rewrite impuresD_Empty by eauto using MF.map_Empty. reflexivity.
        rewrite impuresD_Add by eauto using MF.map_Add, MF.map_not_In.
        symmetry. unfold MM.mmap_map in *. rewrite impuresD_Add. 2: eapply MF.map_Add; eauto.
        2: eapply MF.map_not_In; eauto.
        simpl. rewrite H0. apply ST.heq_star_frame; try reflexivity.
        clear - H. induction e; simpl. reflexivity. repeat rewrite starred_cons.
        simpl. rewrite IHe. apply ST.heq_star_frame; try reflexivity.
        destruct (nth_error preds x); try reflexivity.
        match goal with
          | |- ST.heq _ match ?X with _ => _ end match ?Y with _ => _ end =>
            cutrewrite (X = Y); try reflexivity
        end.
        destruct p. simpl in *; clear -H. generalize dependent SDomain0.
        clear -H; induction a; destruct SDomain0; simpl; intros; auto; try congruence; try reflexivity.
        rewrite H. destruct (exprD funcs U' G' (F a) t); try reflexivity. rewrite IHa. reflexivity. }
      { induction (pures s); try reflexivity.
        simpl. repeat rewrite starred_cons. simpl. rewrite H. rewrite IHl. reflexivity. }
      { induction (other s). reflexivity. etransitivity. rewrite starred_cons. reflexivity.
        etransitivity. 2: rewrite starred_cons; reflexivity. simpl. rewrite IHl. reflexivity. }
    Qed.

    Theorem applySHeap_wt_spec : forall cs U G U' G' s F,
      (forall e t,
        is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G) e t = true ->
        exprD funcs U G e t = exprD funcs U' G' (F e) t) ->
      WellTyped_sheap (typeof_funcs funcs) (typeof_preds preds) (typeof_env U) (typeof_env G) s = true ->
      SE.ST.heq cs (sexprD funcs preds U G (sheapD s))
                   (sexprD funcs preds U' G' (sheapD (applySHeap F s))).
    Proof.
      clear. intros. rewrite WellTyped_sheap_eq in H0. apply andb_true_iff in H0. destruct H0.
      do 2 rewrite sheapD_def. simpl. repeat eapply SE.ST.heq_star_frame.
      { revert H0. clear H1. rewrite WellTyped_impures_spec_eq. eapply MM.PROPS.map_induction with (m := impures s); intros.
        repeat rewrite impuresD_Empty by eauto using MF.map_Empty. reflexivity.
        rewrite impuresD_Add by eauto using MF.map_Add, MF.map_not_In.
        symmetry. unfold MM.mmap_map in *. rewrite impuresD_Add. 2: eapply MF.map_Add; eauto.
        2: eapply MF.map_not_In; eauto.
        simpl. symmetry. rewrite NatMap.IntMapProperties.fold_Add in H3. 5: eauto. 5: eauto.
        apply andb_true_iff in H3. destruct H3. apply ST.heq_star_frame.
        cut (ST.heq cs (sexprD funcs preds U G SE.Emp) (sexprD funcs preds U' G' SE.Emp)); [ | reflexivity ].
        generalize (@SE.Emp types pcType stateType). revert H. clear - H4.
        induction e; simpl; intros. repeat rewrite starred_nil. auto.
        repeat rewrite starred_cons. simpl in *. apply ST.heq_star_frame; eauto.
        unfold typeof_preds in H4. rewrite map_nth_error_full in H4.
        destruct (nth_error preds x); try reflexivity.
        consider (all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G)) a (typeof_pred p)). intros.
        rewrite applyD_map. revert H1. clear -H. destruct p; simpl. generalize dependent SDomain0.
        { induction a; destruct SDomain0; intros; simpl; auto; try reflexivity.
          simpl in H1. consider (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G) a t); intros.
          rewrite H; eauto. destruct (exprD funcs U' G' (F a) t); eauto. reflexivity. }
        { destruct (nth_error (typeof_preds preds) x); try congruence.
          consider (all2 (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G)) a t); intros.
          destruct e. simpl; repeat rewrite starred_nil. eauto.
          generalize dependent (e :: e0); intros.
          eapply IHe; eauto. }
        { eapply H0; eauto. }
        { unfold Basics.flip; constructor; eauto. }
        { clear. unfold Basics.flip. repeat (red; intros; subst). auto. }
        { clear. repeat (red; intros; subst). repeat rewrite <- andb_assoc. f_equal. apply andb_comm. } }
      { cut (ST.heq cs (sexprD funcs preds U G SE.Emp) (sexprD funcs preds U' G' SE.Emp)); [ | reflexivity ].
        revert H1. clear H0. generalize (@SE.Emp types pcType stateType). induction (pures s); intros;
        repeat (rewrite starred_nil || rewrite starred_cons); auto. simpl map. rewrite starred_cons.
        simpl. simpl in H1.
        consider (is_well_typed (typeof_funcs funcs) (typeof_env U) (typeof_env G) a tvProp); intros.
        rewrite IHl; eauto. rewrite H; auto. reflexivity. }
      { cut (ST.heq cs (sexprD funcs preds U G SE.Emp) (sexprD funcs preds U' G' SE.Emp)); [ | reflexivity ].
        generalize (@SE.Emp types pcType stateType). induction (other s); intros.
        etransitivity. rewrite starred_nil. reflexivity. etransitivity; [ | rewrite starred_nil; reflexivity ].
        auto.

        etransitivity; [ rewrite starred_cons; reflexivity | ].
        etransitivity; [ |  rewrite starred_cons; reflexivity ]. simpl. rewrite IHl; eauto. reflexivity. }
    Qed.

    Lemma applySHeap_typed_eq : forall tf tp U G U' G' s F,
      (forall e t,
        is_well_typed tf U G e t = is_well_typed tf U' G' (F e) t) ->
      WellTyped_sheap tf tp U G s = WellTyped_sheap tf tp U' G' (applySHeap F s).
    Proof.
      clear. intros. repeat rewrite WellTyped_sheap_eq in *. destruct s; unfold applySHeap; simpl in *.
      f_equal. unfold WellTyped_impures.
      unfold MM.mmap_map. rewrite MF.fold_map_fusion. eapply fold_ext. intros.
      destruct a; simpl; auto.
      destruct (nth_error tp k); auto; try solve [ destruct v; simpl; auto ].
      cutrewrite (allb (fun args : list (expr types) => all2 (is_well_typed tf U G) args t) v =
        allb (fun args : list (expr types) => all2 (is_well_typed tf U' G') args t) (map (map F) v)); [ destruct v; auto | ].
      induction v; simpl; intros; think; auto.
      rewrite all2_map_1. erewrite all2_eq. 2: eapply H. auto. auto with typeclass_instances.
      repeat red; intros; repeat match goal with
                                   | |- context [ match ?X with _ => _ end ] => destruct X
                                   | |- _ => rewrite andb_true_l
                                   | |- _ => rewrite andb_true_r
                                   | |- context [ allb ?A ?B ] => destruct (allb A B)
                                 end; auto.
      repeat red; intros; repeat match goal with
                                   | |- _ => subst
                                   | |- context [ match ?X with _ => _ end ] => destruct X
                                   | |- _ => rewrite andb_true_l
                                   | |- _ => rewrite andb_true_r
                                   | |- context [ allb ?A ?B ] => destruct (allb A B)
                                 end; auto.
      rewrite allb_map. apply allb_ext. intros. apply H.
    Qed.

    Lemma applySHeap_typed_impl : forall tf tp U G U' G' s F,
      (forall e t,
        is_well_typed tf U G e t = true ->
        is_well_typed tf U' G' (F e) t = true) ->
      WellTyped_sheap tf tp U G s = true ->
      WellTyped_sheap tf tp U' G' (applySHeap F s) = true.
    Proof.
      clear. intros. rewrite WellTyped_sheap_eq in *. destruct s; unfold applySHeap; simpl in *.
      think. apply andb_true_iff; split.
      rewrite WellTyped_impures_eq in H0. apply WellTyped_impures_eq. intros.
      unfold MM.mmap_map in *. rewrite MM.FACTS.map_o in H2. unfold MM.FACTS.option_map in H2.
      consider (FM.find (elt:=list (list (expr types))) k impures0); intros. think.
      specialize (H0 _ _ H2). Opaque allb. destruct l; simpl in *; auto. Transparent allb.
      change (map F l :: map (map F) l0) with (map (map F) (l :: l0)). generalize dependent (l :: l0); intros.
      think. revert H3. clear - H. induction l1; simpl in *; intros; think; auto.
      rewrite all2_map_1. erewrite all2_impl; eauto. congruence.
      rewrite allb_map. eapply allb_impl; eauto.
    Qed.

(*
    (** replace "real" variables [a,b) and replace them with
     ** uvars [c,..]
     **)
    Definition sheapSubstU (a b c : nat) (s : SHeap) : SHeap :=
      {| impures := MM.mmap_map (map (exprSubstU a b c)) (impures s)
       ; pures := map (exprSubstU a b c) (pures s)
       ; other := other s
       |}.
*)

    Theorem hash_Func : forall p (args : exprs types),
      hash (Func p args) = (nil, {| impures := MM.mmap_add p args (MM.empty _)
                                  ; pures   := nil
                                  ; other   := nil
                                  |}).
    Proof. reflexivity. Qed.

  End env.

  Implicit Arguments Emp [ types pcType stateType ].
  Implicit Arguments Star [ types pcType stateType ].
  Implicit Arguments Exists [ types pcType stateType ].
  Implicit Arguments Func [ types pcType stateType ].
  Implicit Arguments Const [ types pcType stateType ].
  Implicit Arguments Inj [ types pcType stateType ].


  Lemma change_ST_himp_himp : forall (types : list type)
    (funcs : functions types) (pc st : tvar)
    (sfuncs : list (predicate types pc st))
    EG G
    (cs : codeSpec (tvarD types pc) (tvarD types st))
    (L R : sexpr types pc st),
    himp funcs sfuncs EG G cs L R ->
    ST.himp cs
      (@sexprD types pc st funcs sfuncs EG G L)
      (@sexprD types pc st funcs sfuncs EG G R).
  Proof.
    unfold himp. intros. auto.
  Qed.

End Make.

Module SepHeapFacts (SH : SepHeap).
  Import SH.SE.
  Module SEP_FACTS := SepExprFacts SH.SE.
  Import SEP_FACTS.

  Section with_env.
    Variable types : list type.
    Variables pcT stT : tvar.
    Variable funcs : functions types.
    Variable preds : predicates types pcT stT.
    Variable cs : PropX.codeSpec (tvarD types pcT) (tvarD types stT).

    Lemma starred_nil : forall T U G cs (F : T -> _) B,
      heq funcs preds U G cs (SH.starred F nil B) B.
    Proof.
      clear. intros; rewrite SH.starred_def. reflexivity.
    Qed.

    Lemma starred_cons : forall T U G cs (F : T -> _) a A B,
      heq funcs preds U G cs (SH.starred F (a :: A) B) (Star (F a) (SH.starred F A B)).
    Proof.
      clear. intros; rewrite SH.starred_def. simpl. rewrite <- SH.starred_def. reflexivity.
    Qed.

    Lemma starred_app : forall T U G cs (F : T -> _) ls ls'  B,
      heq funcs preds U G cs (SH.starred F (ls ++ ls') B) (Star (SH.starred F ls Emp) (SH.starred F ls' B)).
    Proof.
      clear; intros; rewrite SH.starred_def. rewrite fold_right_app. rewrite <- SH.starred_def.
      rewrite SH.starred_base. rewrite <- SH.starred_def. heq_canceler.
    Qed.

    Ltac heq_canceler :=
      repeat (rewrite starred_nil || rewrite starred_cons || rewrite starred_app ||
        match goal with
          | [ |- context [ SH.starred ?A ?B ?X ] ] =>
            match X with
              | Emp => fail 1
              | _ => rewrite SH.starred_base with (F := A) (ls := B) (base := X)
            end
        end);
      SEP_FACTS.heq_canceler.

    Lemma starred_perm : forall T L R,
      Permutation.Permutation L R ->
      forall (F : T -> _) U G cs base,
      heq funcs preds U G cs (SH.starred F L base) (SH.starred F R base).
    Proof.
      clear. intros.
      repeat rewrite SH.starred_def.
      induction H; simpl; intros;
      repeat match goal with
               | [ H : _ |- _ ] => rewrite H
             end; try reflexivity; heq_canceler.
    Qed.

    Lemma himp_pull_pures : forall cs U G s Q,
      (AllProvable funcs U G (SH.pures s) ->
       ST.himp cs (sexprD funcs preds U G (SH.sheapD s)) Q) ->
      ST.himp cs (sexprD funcs preds U G (SH.sheapD s)) Q.
    Proof. clear.
      destruct s; simpl in *. generalize dependent pures.
      induction pures; simpl; intros.
      { apply H; auto. }
      { repeat rewrite SH.sheapD_def in *.
        simpl in *. rewrite starred_cons in *.
        rewrite ST.heq_star_comm with (P := sexprD funcs preds U G (SH.impuresD pcT stT impures)).
        simpl in *.
        repeat rewrite (ST.heq_star_assoc _ (match exprD funcs U G a tvProp with
                                                | Some p => ST.inj [|p|]
                                                | None => ST.inj [|BadInj a|]
                                              end)).
        unfold himp, Provable in *.
        destruct (exprD funcs U G a tvProp).
        { eapply ST.himp_star_pure_c. intros.
          etransitivity. 2: eapply IHpures. Focus 2. intros. etransitivity. 2: eapply H; eauto.
          rewrite SH.sheapD_def. simpl.
          repeat (eapply ST.himp_star_frame; [ reflexivity | ]).
          rewrite ST.heq_star_assoc with (P := ST.inj [| t |]).
          eapply ST.himp_star_pure_cc; auto. reflexivity.
          rewrite SH.sheapD_def. simpl.
          repeat (eapply ST.himp_star_frame; [ reflexivity | ]).
          rewrite ST.himp_star_comm. reflexivity. }
        { eapply ST.himp_star_pure_c. intros.
          inversion H0. } }
    Qed.

(*
   Lemma himp_pull_pures : forall cs U G s Q,
      (AllProvable funcs U G (SH.pures s) ->
       himp funcs preds U G cs (SH.sheapD s) Q) ->
      himp funcs preds U G cs (SH.sheapD s) Q.
    Proof. clear.
      destruct s; simpl in *. generalize dependent pures.
      induction pures; simpl; intros.
      { apply H; auto. }
      { repeat rewrite SH.sheapD_def in *.
        simpl in *. rewrite starred_cons in *.
        rewrite heq_star_comm with (P := SH.impuresD pcT stT impures).
        repeat rewrite heq_star_assoc with (P := Inj a).
        unfold himp, Provable in *. simpl in *.
        destruct (exprD funcs U G a tvProp).
        { eapply ST.himp_star_pure_c. intros.
          etransitivity. 2: eapply IHpures. Focus 2. intros. etransitivity. 2: eapply H; eauto.
          rewrite SH.sheapD_def. simpl.
          repeat (eapply ST.himp_star_frame; [ reflexivity | ]).
          rewrite ST.heq_star_assoc with (P := ST.inj [| t |]).
          eapply ST.himp_star_pure_cc; auto. reflexivity.
          rewrite SH.sheapD_def. simpl.
          repeat (eapply ST.himp_star_frame; [ reflexivity | ]).
          rewrite ST.himp_star_comm. reflexivity. }
        { eapply ST.himp_star_pure_c. intros.
          inversion H0. } }
    Qed.
*)

    Definition sheapSubstU (a b c : nat) : SH.SHeap types pcT stT -> SH.SHeap types pcT stT :=
      SH.applySHeap (Expr.exprSubstU a b c).

    Lemma sheapSubstU_WellTyped_eq : forall tf tp tu tg tg' tg'' s,
      SH.WellTyped_sheap (types := types) (pcType := pcT) (stateType := stT) tf tp tu (tg ++ tg' ++ tg'') s =
      SH.WellTyped_sheap tf tp (tu ++ tg') (tg ++ tg'') (sheapSubstU (length tg) (length tg' + length tg) (length tu) s).
    Proof.
      clear. intros.
      eapply SH.applySHeap_typed_eq; eauto. clear.
      intros. rewrite <- exprSubstU_wt. auto.
    Qed.

    (** TODO: deprecated **)
    Lemma sheapSubstU_WellTyped : forall tf tp tu tg tg' tg'' s,
      SH.WellTyped_sheap (types := types) (pcType := pcT) (stateType := stT) tf tp tu (tg ++ tg' ++ tg'') s = true ->
      SH.WellTyped_sheap tf tp (tu ++ tg') (tg ++ tg'') (sheapSubstU (length tg) (length tg' + length tg) (length tu) s) = true.
    Proof.
      clear. intros.
      eapply SH.applySHeap_typed_impl; eauto. clear.
      intros. rewrite <- exprSubstU_wt. auto.
    Qed.

    Lemma sheapSubstU_sheapD : forall U G G' G'' s,
      ST.heq cs (sexprD funcs preds U (G ++ G' ++ G'') (SH.sheapD s))
                (sexprD funcs preds (U ++ G') (G ++ G'') (SH.sheapD (sheapSubstU (length G) (length G' + length G) (length U) s))).
    Proof.
      intros. eapply SH.applySHeap_spec. intros.
      apply exprSubstU_exprD.
    Qed.

  End with_env.

  Ltac heq_canceler :=
    repeat (rewrite starred_nil || rewrite starred_cons || rewrite starred_app ||
      match goal with
        | [ |- context [ SH.starred ?A ?B ?X ] ] =>
          match X with
            | Emp => fail 1
            | _ => rewrite SH.starred_base with (F := A) (ls := B) (base := X)
          end
      end);
    SEP_FACTS.heq_canceler.

  Lemma applySHeap_singleton : forall types pcT stT funcs (preds : SH.SE.predicates types pcT stT)  meta_env vars_env cs F f l,
    heq funcs preds meta_env vars_env cs
    (SH.sheapD (SH.applySHeap F
      {| SH.impures := MM.mmap_add f l (MM.empty (list (expr types)))
        ; SH.pures := nil
        ; SH.other := nil |}))
    (SH.sheapD
      {| SH.impures := MM.mmap_add f (map F l) (MM.empty (list (expr types)))
        ; SH.pures := nil
        ; SH.other := nil |}).
  Proof.
    clear. intros. rewrite SH.applySHeap_defn; simpl. repeat rewrite SH.sheapD_def; simpl.
    heq_canceler. unfold MM.mmap_add. repeat rewrite MM.FACTS.empty_o.
    rewrite SH.impuresD_Add with (f := f) (argss := map F l :: nil) (i := MM.empty _). symmetry.
    rewrite SH.impuresD_Add with (f := f) (argss := map F l :: nil) (i := MM.empty _). reflexivity.
    red; reflexivity. intro; eapply MM.FACTS.empty_in_iff; eassumption.
    red; reflexivity. intro; eapply MM.FACTS.empty_in_iff; eassumption.
  Qed.

  Export SEP_FACTS.

End SepHeapFacts.
