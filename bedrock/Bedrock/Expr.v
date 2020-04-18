Require Import Coq.omega.Omega.
Require Import Coq.Lists.List Bedrock.DepList.
Require Import Bedrock.EqdepClass.
Require Import Bedrock.Word.
Require Import Coq.Bool.Bool Bedrock.Folds.
Require Import Bedrock.Reflection Bedrock.Tactics.

Set Implicit Arguments.

(** The reification mechanism use instances of this type-class to
decide how to reify the types *)
Module ReificationHint.
  Class Pkg (T : Type) := mk_Pkg
    {
      Eqb : forall (x y : T), bool;
      Eqb_correct : forall x y, Eqb x y = true -> x = y
    }.
End ReificationHint.

Section env.
  (** Syntax **)
  Record type := Typ {
    Impl : Type;
    Eqb : forall x y : Impl, bool;
    Eqb_correct : forall x y, Eqb x y = true -> x = y
  }.

  Definition Impl_ (o : option type) : Type :=
    match o return Type with
      | None => Empty_set
      | Some t => Impl t
    end.

  Variable types : list type.

  (** this type requires decidable equality **)
  Inductive tvar : Type :=
  | tvProp
  | tvType : nat -> tvar.

  Definition tvarD (x : tvar) :=
    match x return Type with
      | tvProp => Prop
      | tvType x =>
        Impl_ (nth_error types x)
    end.

  Definition EmptySet_type : type :=
  {| Impl := Empty_set
   ; Eqb := fun x _ => match x with end
   ; Eqb_correct := fun x _ _ => match x with end
   |}.

  Definition Prop_type : type.
  refine ({| Impl := Prop
       ; Eqb := fun _ _ => false
       ; Eqb_correct := _
   |}). abstract (discriminate).
  Defined.

  Definition typeFor (t : tvar) : type :=
    match t with
      | tvProp => Prop_type
      | tvType t =>
        match nth_error types t with
          | None => EmptySet_type
          | Some v => v
        end
    end.

  Definition tvar_val_seqb (t : tvar) : forall (x y : tvarD t), bool :=
    match t with
      | tvProp => fun _ _ => false
      | tvType t =>
        match nth_error types t as k return forall x y : match k with
                                                           | None => Empty_set
                                                           | Some t => Impl t
                                                         end, bool with
          | None => fun x _ => match x with end
          | Some t => fun x y =>  Eqb t x y
        end
    end.

  Global Instance SemiReflect_Eqb (t : type) (x y : Impl t) : SemiReflect (Eqb _ x y) (x = y).
  Proof.
    consider (Eqb t x y); intros; constructor.
    apply Eqb_correct; auto.
  Qed.

  Lemma tvar_val_seqb_correct t x y : tvar_val_seqb t x y = true -> x = y.
  Proof.
    revert x y. destruct t; simpl.
    discriminate.
    destruct (nth_error types n); simpl.
    refine (fun x y H => Eqb_correct _ x y H).
    intros [].
  Defined.

  Global Instance SemiReflect_tvar_val_seqb t x y : SemiReflect (tvar_val_seqb t x y) (x = y).
  Proof.
    revert x y. destruct t; simpl; intros; try constructor.
    destruct (nth_error types n); simpl.
    consider (Eqb t x y); intros; constructor. auto.
    destruct x.
  Qed.

  Fixpoint functionTypeD (domain : list Type) (range : Type) : Type :=
    match domain with
      | nil => range
      | d :: domain' => d -> functionTypeD domain' range
    end.

  Record signature := Sig {
    Domain : list tvar;
    Range : tvar;
    Denotation : functionTypeD (map tvarD Domain) (tvarD Range)
  }.

  Definition Default_signature : signature :=
  {| Domain := nil
   ; Range := tvProp
   ; Denotation := True
   |}.

  Definition functions := list signature.
  Definition variables := list tvar.

  Variable funcs : functions.
  Variable uvars : variables.
  Variable vars : variables.

  Definition func := nat.
  Definition var := nat.
  Definition uvar := nat.

  Unset Elimination Schemes.

  Inductive expr : Type :=
  | Const : forall t : tvar, tvarD t -> expr
  | Var : var -> expr
  | Func : forall f : func, list expr -> expr
  | Equal : tvar -> expr -> expr -> expr
  | Not : expr -> expr
  | UVar : uvar -> expr.

  Definition exprs : Type := list expr.

  Set Elimination Schemes.

  Section expr_ind.
    Variable P : expr -> Prop.

    Hypotheses
      (Hc : forall (t : tvar) (t0 : tvarD t), P (Const t t0))
      (Hv : forall x : var, P (Var x))
      (Hu : forall x : uvar, P (UVar x))
      (Hf : forall (f : func) (l : list expr), Forall P l -> P (Func f l))
      (He : forall t e1 e2, P e1 -> P e2 -> P (Equal t e1 e2))
      (Hn : forall e, P e -> P (Not e)).

    Theorem expr_ind : forall e : expr, P e.
    Proof.
      refine (fix recur e : P e :=
        match e as e return P e with
          | Const t v => @Hc t v
          | Var x => Hv x
          | UVar x => Hu x
          | Func f xs => @Hf f xs ((fix prove ls : Forall P ls :=
            match ls as ls return Forall P ls with
              | nil => Forall_nil _
              | l :: ls => Forall_cons _ (recur l) (prove ls)
            end) xs)
          | Equal tv e1 e2 => He tv (recur e1) (recur e2)
          | Not e => Hn (recur e)
        end).
    Defined.
  End expr_ind.

  Global Instance EqDec_tvar : EqDec _ (@eq tvar).
   red. change (forall x y : tvar, {x = y} + {x <> y}).
    decide equality. eapply Peano_dec.eq_nat_dec.
  Defined.

  Definition tvar_seqb (x y : tvar) : bool :=
    match x, y with
        | tvProp , tvProp => true
        | tvType x , tvType y => EqNat.beq_nat x y
        | _,_ => false
    end.

  Lemma tvar_seqb_correct (x y : tvar) : tvar_seqb x y = true -> x = y.
  Proof.
    revert x y. intros [|x] [|y]; simpl; try (reflexivity|| discriminate).
    consider (EqNat.beq_nat x y). auto.
  Defined.

  Global Instance Reflect_tvar_seqb a b : Reflect (tvar_seqb a b) (a = b) (a <> b).
  Proof.
    destruct a; destruct b; try constructor; auto; try congruence.
      simpl. consider (EqNat.beq_nat n n0); constructor; auto.
      congruence.
  Qed.

  Lemma tvar_seqb_refl : forall a, tvar_seqb a a = true.
  Proof. intros; consider (tvar_seqb a a); auto. Qed.

  Definition env : Type := list (sigT tvarD).

  Definition env_empty : env := nil.

  Definition lookupAs (ls : env) (t : tvar) (i : nat)
    : option (tvarD t) :=
    match nth_error ls i with
      | None => None
      | Some tv =>
        match equiv_dec (projT1 tv) t with
          | left pf =>
            Some match pf in _ = t return tvarD t with
                   | refl_equal => projT2 tv
                 end
          | right _ => None
        end
    end.

  Lemma lookupAs_det : forall v x t1 t2,
    lookupAs v t1 x <> None
    -> lookupAs v t2 x <> None
    -> t1 = t2.
    unfold lookupAs. clear.
    induction v; destruct x; simpl; intros; try congruence.
      destruct a; simpl in *.
      destruct (equiv_dec x t1); destruct (equiv_dec x t2); try congruence.
      eauto.
  Qed.

  Variable meta_env : env.
  Variable var_env : env.

  Section applyD.
    Variable exprD : expr -> forall t, option (tvarD t).

    Fixpoint applyD domain (xs : list expr) {struct xs}
      : forall range, functionTypeD (map tvarD domain) range -> option range :=
        match domain as domain , xs
          return forall range, functionTypeD (map tvarD domain) range -> option range
          with
          | nil , nil => fun _ v => Some v
          | t :: ts , e :: es =>
            match exprD e t with
              | None => fun _ _ => None
              | Some v => fun r f => applyD ts es r (f v)
            end
          | _ , _ => fun _ _ => None
        end.
  End applyD.

  Fixpoint exprD (e : expr) (t : tvar) : option (tvarD t) :=
    match e with
      | Const t' c =>
        match equiv_dec t' t with
          | left pf =>
            Some match pf in _ = t return tvarD t with
                   | refl_equal => c
                 end
          | right _ => None
        end
      | Var x => lookupAs var_env t x
      | UVar x => lookupAs meta_env t x
      | Func f xs =>
        match nth_error funcs f with
          | None => None
          | Some f =>
            match equiv_dec (Range f) t with
              | right _ => None
              | left pf =>
                match pf in _ = t return option (tvarD t) with
                  | refl_equal =>
                    applyD (exprD) _ xs _ (Denotation f)
                end
            end
        end
      | Equal t' e1 e2 =>
        match t with
          | tvProp => match exprD e1 t', exprD e2 t' with
                        | Some v1, Some v2 => Some (v1 = v2)
                        | _, _ => None
                      end
          | _ => None
        end
      | Not e1 => match t with
                    | tvProp =>
                      match exprD e1 tvProp with
                        | None => None
                        | Some p => Some (not p)
                      end
                    | _ => None
                  end
    end.

  Theorem exprD_det : forall e t1 t2, exprD e t1 <> None
    -> exprD e t2 <> None
    -> t1 = t2.
  Proof.
    induction e; simpl; intros; try solve [ eapply lookupAs_det; eauto ];
      repeat match goal with
               | [ H : context [ match ?Y with
                                   | left _ => _ | right _ => _
                                 end ] |- _ ] => destruct Y; try congruence
               | [ H : context [ match nth_error ?A ?B with
                                   | Some _ => _ | None => _
                                 end ] |- _ ] => destruct (nth_error A B); try congruence
             end;
    destruct t1; destruct t2; auto.
  Qed.

  Section type_system.
    Definition tenv : Type := list tvar.
    Record tsignature : Type := SigT {
      TDomain : list tvar ;
      TRange  : tvar
    }.

    Definition tfunctions : Type := list tsignature.

    Variable tfuncs : tfunctions.
    Variable tmeta_env : tenv.
    Variable tvar_env : tenv.


    Fixpoint typeof (e : expr) : option tvar :=
      match e with
        | Const t _ => Some t
        | Var x => nth_error tvar_env x
        | UVar x => nth_error tmeta_env x
        | Func f _ => match nth_error tfuncs f with
                        | None => None
                        | Some r => Some (TRange r)
                      end
        | Equal _ _ _
        | Not _ => Some tvProp
      end.

    Definition typeof_env : env -> tenv :=
      map (@projT1 _ _).
    Definition typeof_sig (s : signature) : tsignature :=
      {| TDomain := Domain s
       ; TRange  := Range s
       |}.
    Definition typeof_funcs : functions -> tfunctions :=
      map typeof_sig.

    Definition WellTyped_env (t : tenv) (g : env) : Prop :=
      t = typeof_env g.
    Definition WellTyped_sig (t : tsignature) (g : signature) : Prop :=
      TDomain t = Domain g /\ TRange t = Range g.

    Definition WellTyped_funcs (t : tfunctions) (g : functions) : Prop :=
      Forall2 WellTyped_sig t g.

    Theorem typeof_env_WellTyped_env : forall g,
      WellTyped_env (typeof_env g) g.
    Proof.
      clear. intros. reflexivity.
    Qed.
    Theorem typeof_sig_WellTyped_sig : forall f,
      WellTyped_sig (typeof_sig f) f.
    Proof.
      clear. unfold WellTyped_sig; intuition.
    Qed.
    Theorem typeof_funcs_WellTyped_funcs : forall f,
      WellTyped_funcs (typeof_funcs f) f.
    Proof.
      clear; induction f; simpl; intros; econstructor; auto using typeof_sig_WellTyped_sig.
    Qed.

    Lemma typeof_env_length : forall g,
      length (typeof_env g) = length g.
    Proof.
      intros. apply map_length.
    Qed.

    Lemma typeof_env_app : forall a b,
      typeof_env (a ++ b) = typeof_env a ++ typeof_env b.
    Proof.
      clear. unfold typeof_env. intros. rewrite map_app. reflexivity.
    Qed.

    Lemma typeof_env_rev : forall g,
      typeof_env (rev g) = rev (typeof_env g).
    Proof.
      clear. induction g; simpl; auto. rewrite typeof_env_app. simpl. rewrite IHg. auto.
    Qed.



    Fixpoint is_well_typed (e : expr) (t : tvar) {struct e} : bool :=
      match e with
        | Const t' _ =>
          if tvar_seqb t' t then true else false
        | Var x => match nth_error tvar_env x with
                     | None => false
                     | Some t' => if tvar_seqb t t' then true else false
                   end
        | UVar x => match nth_error tmeta_env x with
                      | None => false
                      | Some t' => if tvar_seqb t t' then true else false
                    end
        | Func f xs =>
          match nth_error tfuncs f with
            | None => false
            | Some f =>
              if tvar_seqb t (TRange f) then
                all2 is_well_typed xs (TDomain f)
              else false
          end
        | Equal t' e1 e2 =>
          match t with
            | tvProp => is_well_typed e1 t' && is_well_typed e2 t'
            | _ => false
          end
        | Not e1 => match t with
                      | tvProp => is_well_typed e1 tvProp
                      | _ => false
                    end
      end.

    Section Mentions.
      Variable uv : uvar.

      Fixpoint mentionsU (e : expr) : bool :=
        match e with
          | Const _ _
          | Var _ => false
          | UVar n => if EqNat.beq_nat uv n then true else false
          | Func _ args =>
            (fix anyb ls : bool :=
              match ls with
                | nil => false
                | l :: ls => mentionsU l || anyb ls
              end) args
          | Equal _ l r => mentionsU l || mentionsU r
          | Not e => mentionsU e
        end.
    End Mentions.

    Hypothesis WT_meta : WellTyped_env tmeta_env meta_env.
    Hypothesis WT_vars : WellTyped_env tvar_env var_env.
    Hypothesis WT_funcs : WellTyped_funcs tfuncs funcs.

    Lemma WellTyped_env_nth_error_Some : forall g t n T,
      WellTyped_env t g ->
      nth_error t n = Some T ->
      exists v, nth_error g n = Some (@existT _ _ T v).
    Proof.
      clear. induction g; destruct t; destruct n; simpl; unfold WellTyped_env, error, value in *; simpl; intros; try congruence.
      inversion H0; clear H0; subst. inversion H; subst.
      exists (projT2 a). destruct a; auto.
      inversion H. eapply IHg; eauto.
    Qed.

    Lemma WellTyped_env_nth_error_None : forall g t n,
      WellTyped_env t g ->
      nth_error t n = None ->
      nth_error g n = None.
    Proof.
      clear. induction g; destruct t; destruct n; simpl; unfold WellTyped_env, error, value in *; simpl; intros; try congruence.
      inversion H. eapply IHg; eauto.
    Qed.

    Lemma Forall2_nth_error_both_Some : forall T U (P : T -> U -> Prop) l r,
      Forall2 P l r ->
      forall n L R,
        nth_error l n = Some L ->
        nth_error r n = Some R ->
        P L R.
    Proof.
      clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
    Qed.
    Lemma Forall2_nth_error_L_None : forall T U (P : T -> U -> Prop) l r,
      Forall2 P l r ->
      forall n,
        nth_error l n = None ->
        nth_error r n = None.
    Proof.
      clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
    Qed.

    Lemma Forall2_nth_error_L : forall T U (P : T -> U -> Prop) l r,
      Forall2 P l r ->
      forall n L,
        nth_error l n = Some L ->
        exists R,
          nth_error r n = Some R /\ P L R.
    Proof.
      clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
      inversion H1; subst; eauto.
    Qed.


    Theorem exprD_principal : forall e t, exprD e t <> None
      -> match typeof e with
           | None => False
           | Some t' => exprD e t' <> None
         end.
    Proof.
      induction e; simpl; unfold lookupAs; intros;
        try solve [ repeat (simpl in *; try congruence;
          match goal with
            | [ |- context[nth_error ?E ?F] ] => case_eq (nth_error E F); intros
            | [ H : nth_error _ _ = _ |- _ ] =>
              (eapply WellTyped_env_nth_error_Some in H; [ | eassumption ]) ||
              (eapply WellTyped_env_nth_error_None in H; [ | eassumption ])
            | [ |- context[ equiv_dec ?A ?A ] ] => rewrite (EquivDec_refl_left A)
            | [ H : context [ match ?X with
                                | left _ => _ | right _ => _
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : context [ match ?X with
                                | tvProp => _ | tvType _ => _
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : match ?pf with refl_equal => _ end = _ |- _ ] => rewrite (UIP_refl pf) in H
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => rewrite H in *
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
          end) ].
      repeat (simpl in *; try congruence;
          match goal with
            | [ |- context[nth_error ?E ?F] ] => case_eq (nth_error E F); intros
            | [ H : nth_error _ _ = _ |- _ ] =>
              (eapply WellTyped_env_nth_error_Some in H; [ | eassumption ]) ||
              (eapply WellTyped_env_nth_error_None in H; [ | eassumption ])
            | [ |- context[ equiv_dec ?A ?A ] ] => rewrite (EquivDec_refl_left A)
            | [ H : context [ match ?X with
                                | left _ => _ | right _ => _
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : context [ match ?X with
                                | tvProp => _ | tvType _ => _
                              end ] |- _ ] => destruct X; [ | solve [ exfalso; auto ] ]
            | [ H : match ?pf with refl_equal => _ end = _ |- _ ] => rewrite (UIP_refl pf) in H
            | [ H : exists x, _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => rewrite H in *
            | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
          end).

      eapply Forall2_nth_error_both_Some in WT_funcs; eauto. destruct WT_funcs. destruct (equiv_dec (Range s) (TRange t0)); try congruence.
      unfold equiv in *. subst. destruct s; simpl in *. subst. revert H. rewrite (UIP_refl e0).
      induction 1; simpl; destruct TDomain; auto; try congruence.


      eapply Forall2_nth_error_L_None in WT_funcs; try eassumption.
      rewrite WT_funcs in *. congruence.
  Qed.

  Lemma exprD_typeof : forall a1 t D,
    exprD a1 t = Some D ->
    typeof a1 = Some t.
  Proof.
    intros.
    assert (exprD a1 t <> None); try congruence.
    apply exprD_principal in H0.
    destruct (typeof a1); try contradiction.
    f_equal.
    eapply exprD_det in H0. symmetry; eassumption. congruence.
  Qed.

  Definition ValidProp (e : expr) :=
    exists v, exprD e tvProp = Some v.
  Definition ValidExp (e : expr) :=
    exists t, exists v, exprD e t = Some v.

  Theorem is_well_typed_correct : forall e t,
    is_well_typed e t = true ->
    exists v, exprD e t = Some v.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | [ H : context [ equiv_dec ?X ?Y ] |- _ ] =>
               destruct (equiv_dec X Y)
             | [ |- context [ equiv_dec ?X ?Y ] ] =>
               destruct (equiv_dec X Y)
             | [ H : context [ match nth_error ?X ?Y with | _ => _ end ] |- _ ] =>
               revert H; case_eq (nth_error X Y); intros
             | [ H : nth_error _ _ = _ , H' : WellTyped_env _ _ |- _ ] =>
               rewrite (@WellTyped_env_nth_error_Some H' H)
             | [ H : nth_error _ _ = _ |- _ ] =>
              (eapply WellTyped_env_nth_error_Some in H; [ destruct H | eassumption ]) ||
              (eapply WellTyped_env_nth_error_None in H; [ | eassumption ])
             | [ H : _ = _ |- _ ] => rewrite H
             | [ H : match ?X with
                       | _ => _
                     end = true |- _ ] => consider X; try congruence
             | [ |- _ ] => unfold lookupAs in *; simpl in *
        end; intros; eauto; try congruence.
    { eapply Forall2_nth_error_L in WT_funcs; eauto. destruct WT_funcs. intuition. subst.
      destruct H5. rewrite H1 in *; clear H1. rewrite H3 in *; clear H3. rewrite H4.
      rewrite EquivDec_refl_left. destruct x; simpl in *. revert H2. clear - H.
      generalize dependent Domain0. induction H; destruct Domain0; simpl in *; intros; eauto; try congruence.
      consider (is_well_typed x t); intros. apply H in H1. destruct H1. rewrite H1. eapply IHForall; auto. }
    { apply andb_true_iff in H0. intuition. apply IHe1 in H1. apply IHe2 in H2.
      destruct H1. destruct H2. think. eauto. }
    { apply IHe in H0. destruct H0; think; eauto. }
  Qed.

  Lemma WellTyped_env_nth_error_Some' : forall g t n V,
    WellTyped_env t g ->
    nth_error g n = Some V ->
    nth_error t n = Some (projT1 V).
  Proof.
    clear. induction g; destruct t; destruct n; simpl; unfold WellTyped_env, error, value in *; simpl; intros; try congruence.
    inversion H0; clear H0; subst. inversion H; subst. auto.
  Qed.

  Lemma WellTyped_env_nth_error_None' : forall g t n,
    WellTyped_env t g ->
    nth_error g n = None ->
    nth_error t n = None.
  Proof.
    clear. induction g; destruct t; destruct n; simpl; unfold WellTyped_env, error, value in *; simpl; intros; try congruence.
    inversion H. eapply IHg; eauto.
  Qed.
  Lemma Forall2_nth_error_R : forall T U (P : T -> U -> Prop) l r,
    Forall2 P l r ->
    forall n R,
      nth_error r n = Some R ->
      exists L,
        nth_error l n = Some L /\ P L R.
  Proof.
    clear; induction 1; destruct n; simpl; unfold value, error; intros; try congruence; eauto.
    inversion H1; subst; eauto.
  Qed.

  Theorem is_well_typed_correct_only : forall e t v,
    exprD e t = Some v ->
    is_well_typed e t = true.
  Proof.
    induction e; simpl; intros;
    repeat match goal with
             | [ H : @equiv _ _ _ _ _ |- _ ] => unfold equiv in H; subst
             | [ H : context [ equiv_dec ?X ?Y ] |- _ ] =>
               destruct (equiv_dec X Y)
             | [ |- context [ equiv_dec ?X ?Y ] ] =>
               destruct (equiv_dec X Y)
             | [ H : context [ match nth_error ?X ?Y with | _ => _ end ] |- _ ] =>
               revert H; case_eq (nth_error X Y); intros
             | [ |- _ ] =>
               (erewrite WellTyped_env_nth_error_Some' by eauto) ||
               (erewrite WellTyped_env_nth_error_None' by eauto)
             | [ |- _ ] => unfold lookupAs in *; simpl in *
        end; think; eauto; try congruence.
    { consider (tvar_seqb t1 t1); auto. }
    { consider (tvar_seqb (projT1 s) (projT1 s)); intros; auto. }
    { consider (tvar_seqb (projT1 s) (projT1 s)); intros; auto. }
    { eapply Forall2_nth_error_R in WT_funcs; eauto. destruct WT_funcs. intuition.
      rewrite H3. destruct H4. rewrite H4. consider (tvar_seqb (Range s) (Range s)); intros; try congruence.
      destruct s; simpl in *; subst. destruct x; simpl in *; subst.
      clear - H H1. generalize dependent TDomain0. induction H; destruct TDomain0; simpl; auto; intros; try congruence.
      consider (exprD x t); intros; eauto. erewrite H; eauto. congruence. }
  Qed.

  Theorem is_well_typed_typeof : forall e t,
    is_well_typed e t = true -> typeof e = Some t.
  Proof.
    induction e; simpl; intros;
      repeat (progress (unfold equiv in *; subst) ||
        match goal with
          | [ H : context [ match nth_error ?X ?Y with | _ => _ end ] |- _ ] =>
            revert H; case_eq (nth_error X Y); intros; try congruence
          | [ H : match ?X with
                    | _ => _
                  end = true |- _ ] => consider X; try congruence
        end); auto.
  Qed.

  Lemma is_well_typed_only : forall t t' e,
    is_well_typed e t = true ->
    t <> t' ->
    is_well_typed e t' = false.
  Proof.
    intros. consider (is_well_typed e t'); auto; intros.
    apply is_well_typed_typeof in H.
    apply is_well_typed_typeof in H1; congruence.
  Qed.

  End type_system.

  Lemma expr_seq_dec_Equal : forall t1 t2 e1 f1 e2 f2,
    t1 = t2
    -> e1 = e2
    -> f1 = f2
    -> Equal t1 e1 f1 = Equal t2 e2 f2.
  Proof. congruence. Qed.

  Lemma expr_seq_dec_Not : forall e1 e2,
    e1 = e2
    -> Not e1 = Not e2.
  Proof. congruence. Qed.

  Definition get_Eq (t : tvar) : forall x y : tvarD t, bool :=
    match t as t return forall x y : tvarD t, bool with
      | tvProp => fun _ _ => false
      | tvType t =>
        match nth_error types t as k
          return forall x y : match k with
                                | Some t => Impl t
                                | None => Empty_set
                              end, bool
          with
          | None => fun x _ => match x with end
          | Some t => Eqb t
        end
    end.

  Definition const_seqb  t t' : tvarD t -> tvarD t' -> bool :=
    match t as t , t' as t' return tvarD t -> tvarD t' -> bool with
      | tvType x , tvType y =>
        match Peano_dec.eq_nat_dec x y with
          | left pf =>
            match pf in _ = t return Impl_ (nth_error types x) -> Impl_ (nth_error types t) -> bool with
              | refl_equal =>
                match nth_error types x as ty return Impl_ ty -> Impl_ ty -> bool with
                  | None => fun _ _ => false
                  | Some t => @Eqb t
                end
            end
          | right _ => fun _ _ => false
        end
      | _ , _ => fun _ _ => false
    end.

  Global Instance SemiReflect_const_seqb t t' c c'
    : SemiReflect (@const_seqb t t' c c') (exists pf : t = t',
      match pf in _ = t return tvarD t with
        | refl_equal => c
      end = c').
  Proof.
    unfold const_seqb.
    repeat match goal with
             | [ |- SemiReflect (match ?X with | _ => _ end _ _) _ ] =>
               destruct X; try constructor
           end.

    unfold tvarD.
    case_eq (match
                nth_error types n as ty return (Impl_ ty -> Impl_ ty -> bool)
              with
                | Some t => Eqb t
                | None => fun _ _ : Impl_ None => false
              end c c');
      constructor.
    exists (eq_refl).
    revert H. revert c c'.
    unfold tvarD.
    refine (match (nth_error types n) as t return forall c c' : Impl_ t,
              match t as ty return (Impl_ ty -> Impl_ ty -> bool) with
                | Some t => Eqb t
                | None => fun _ _ : Impl_ None => false
              end c c' = true -> c = c'
            with
              | Some t => _
              | None => _
            end).
    apply Eqb_correct.
    discriminate.
  Qed.


  Fixpoint expr_seq_dec (a b : expr) : bool :=
    match a,b  with
      | Const t c , Const t' c' =>
        const_seqb t t' c c'
      | Var x , Var y =>
        EqNat.beq_nat x y
      | UVar x , UVar y =>
        EqNat.beq_nat x y
      | Func x xs , Func y ys =>
        EqNat.beq_nat x y &&
          (fix seq_dec' a b : bool :=
            match a, b with
              | nil , nil => true
              | x :: xs , y :: ys =>
                if  expr_seq_dec x y then
                  seq_dec' xs ys
                  else false
              | _ , _ => false
            end) xs ys
      | Equal t1 e1 f1 , Equal t2 e2 f2 =>
        tvar_seqb t1 t2 && expr_seq_dec e1 e2 && expr_seq_dec f1 f2
      | Not e1 , Not e2 =>
        expr_seq_dec e1 e2
      | _ , _ => false
    end.

  Lemma expr_seq_dec_correct : forall (a b : expr),  expr_seq_dec a b = true -> a = b.
  Proof.
    induction a; destruct b; simpl; try congruence;
      repeat match goal with
               | [ |- context [ EqNat.beq_nat ?X ?Y ] ] =>
                 consider (EqNat.beq_nat X Y)
               | [ |- context [ expr_seq_dec ?X ?Y ] ] =>
                 consider (expr_seq_dec X Y); intro
               | [ |- context [ tvar_seqb ?X ?Y ] ] =>
                 consider (tvar_seqb X Y); intro
               | [ H : _ , H' : expr_seq_dec _ _ = true |- _ ] => apply H in H'; try subst
             end; simpl in *; subst; try congruence; auto.
    consider (const_seqb t t1 t0 t2). intro. destruct H. subst. eauto.
    intro; subst. intros; f_equal. generalize dependent l0. induction H; destruct l0; try congruence.
      consider (expr_seq_dec x e). intros. apply H in H1. subst. apply IHForall in H2. f_equal; auto.
  Qed.

  Global Instance SemiReflect_expr_seq_dec a b : SemiReflect (expr_seq_dec a b) (a = b).
  Proof.
    apply impl_to_semireflect; exact expr_seq_dec_correct.
  Qed.

  Section liftExpr.
    Variables ua ub : nat.
    Variables a b : nat.

    (** insert into the domain of e:
     ** exprD (U ++ U') (G ++ G') e t =
     ** exprD (U ++ U'' ++ U') (G ++ G'' ++ G') (liftExpr (length U) (length U'') (length G) (length G'') e) t
     **)
    Fixpoint liftExpr (e : expr) : expr :=
      match e with
        | Const _ _ => e
        | Var x =>
          Var (if NPeano.ltb x a then x else b + x)
        | UVar x =>
          UVar (if NPeano.ltb x ua then x else ub + x)
        | Func f xs =>
          Func f (map liftExpr xs)
        | Equal t e1 e2 => Equal t (liftExpr e1) (liftExpr e2)
        | Not e1 => Not (liftExpr e1)
      end.

    Lemma liftExpr_0 : ub = 0 -> b = 0 -> forall e, liftExpr e = e.
    Proof.
      induction e; simpl; intros; think; simpl; auto;
        try match goal with
              | [ |- context [ if ?X then _ else _ ] ] => destruct X
            end; auto.
      f_equal. induction H1; simpl in *; think; auto.
    Qed.
  End liftExpr.

  Lemma liftExpr_combine : forall ua ub uc a b c e,
    liftExpr ua ub a b (liftExpr ua uc a c e) = liftExpr ua (uc + ub) a (c + b) e.
  Proof.
    induction e; simpl; intros; think; auto; f_equal; unfold var, uvar in *;
      repeat match goal with
               | [ |- context [ if ?X then _ else _ ] ] => consider X; intros
             end; try solve [ reflexivity | omega ].
    induction H; intros; simpl; think; auto.
  Qed.

  (** This function replaces "real" variables [a, b) with existential variables (c,...)
   **)
  Fixpoint exprSubstU (a b c : nat) (s : expr (*a (b ++ c ++ d)*)) {struct s}
    : expr (* (c ++ a) (b ++ d) *) :=
    match s with
      | Const _ t => Const _ t
      | Var x =>
        if NPeano.ltb x a
        then Var x
        else if NPeano.ltb x b
             then UVar (c + x - a)
             else Var (x + a - b)
      | UVar x =>
        if NPeano.ltb x c
        then UVar x
        else UVar (x + b - a)
      | Func f args => Func f (map (exprSubstU a b c) args)
      | Equal t e1 e2 => Equal t (exprSubstU a b c e1) (exprSubstU a b c e2)
      | Not e1 => Not (exprSubstU a b c e1)
    end.

  Lemma nth_error_app_L : forall T (A B : list T) n,
    (n < length A)%nat ->
    nth_error (A ++ B) n = nth_error A n.
  Proof.
    induction A; destruct n; simpl; intros; try omega; auto.
    eapply IHA. omega.
  Qed.

  Lemma nth_error_app_R : forall T (A B : list T) n,
    (length A <= n)%nat ->
    nth_error (A ++ B) n = nth_error B (n - length A).
  Proof.
    induction A; destruct n; simpl; intros; try omega; auto.
    apply IHA. omega.
  Qed.

  Lemma nth_error_weaken : forall T ls' (ls : list T) n v,
    nth_error ls n = Some v ->
    nth_error (ls ++ ls') n = Some v.
  Proof.
    clear. induction ls; destruct n; simpl; intros; unfold value, error in *; try congruence; auto.
  Qed.

  Lemma nth_error_past_end : forall T (ls : list T) n,
    (n >= length ls)%nat ->
    nth_error ls n = None.
  Proof.
    clear. induction ls; destruct n; simpl; intros; auto.
    exfalso; omega. rewrite IHls; auto. omega.
  Qed.

  Lemma exprSubstU_wt : forall tf tu tg tg' tg'' s t,
    is_well_typed tf tu (tg ++ tg' ++ tg'') s t =
    is_well_typed tf (tu ++ tg') (tg ++ tg'') (exprSubstU (length tg) (length tg' + length tg) (length tu) s) t.
  Proof.
    induction s; simpl; intros; think; auto.
    { consider (NPeano.ltb x (length tg)); intros; simpl.
      repeat rewrite nth_error_app_L in * by omega. reflexivity.
      consider (NPeano.ltb x (length tg' + length tg)); simpl; intros.
      repeat rewrite nth_error_app_R in * by omega.
      repeat rewrite nth_error_app_L in * by omega.
      repeat rewrite nth_error_app_R in * by omega.
      cutrewrite (length tu + x - length tg - length tu = x - length tg); [ | omega ]. reflexivity.
      repeat (rewrite nth_error_app_R in * by omega).
      cutrewrite (x + length tg - (length tg' + length tg) - length tg = x - length tg - length tg'); [ | omega ].
      reflexivity. }
    { consider (NPeano.ltb x (length tu)); intros; simpl.
      rewrite nth_error_app_L in * by omega. reflexivity.
      rewrite nth_error_app_R in * by omega.
      repeat rewrite nth_error_past_end by omega. auto. }
    { destruct (nth_error tf f); auto.
      destruct (tvar_seqb t (TRange t0)); auto.
      rewrite all2_map_1. destruct t0; simpl in *.
      clear - H; generalize dependent TDomain0; induction H; destruct TDomain0; simpl; intros; auto.
      think. reflexivity. }
  Qed.

  Lemma nth_error_length : forall T (ls ls' : list T) n,
    nth_error (ls ++ ls') (n + length ls) = nth_error ls' n.
  Proof.
    induction ls; simpl; intros.
    rewrite Plus.plus_0_r. auto.
    cutrewrite (n + S (length ls) = S n + length ls); [ | omega ]. simpl. auto.
  Qed.


  (** first variable in the list is the first one quantified
   **)
  Fixpoint forallEach (ls : variables) : (env -> Prop) -> Prop :=
    match ls with
      | nil => fun cc => cc nil
      | a :: b => fun cc =>
        forall x : tvarD a, forallEach b (fun r => cc (existT _ a x :: r))
    end.

  Theorem forallEach_sem : forall ls P,
    forallEach ls P <-> (forall env, typeof_env env = ls -> P env).
  Proof.
    induction ls; simpl; split; intros.
      destruct env0; auto. simpl in *; congruence.
      eapply H; reflexivity.

      destruct env0; simpl in *; try congruence.
      inversion H0; clear H0; subst. specialize (H (projT2 s)).
      eapply IHls in H; eauto. destruct s; simpl in *; auto.

      eapply IHls. intros. subst. eapply H. auto.
  Qed.

  (** first variable in the list is the first one quantified
   **)
  Fixpoint existsEach (ls : variables) : (env.env -> Prop) -> Prop :=
    match ls with
      | nil => fun cc => cc nil
      | a :: b => fun cc =>
        exists x : tvarD a, existsEach b (fun r => cc (existT _ a x :: r))
    end.

  Theorem existsEach_sem : forall ls P,
    existsEach ls P <-> (exists env, typeof_env env = ls /\ P env).
  Proof.
    induction ls; simpl; split; intros.
      exists nil; auto.
      destruct H. destruct x; intuition (simpl in *; eauto; congruence).

      destruct H. eapply IHls in H. destruct H.
      intuition; subst. eexists; eauto. split; eauto. reflexivity.

      destruct H. intuition; subst. destruct x; simpl in *; try congruence.
      destruct s. simpl in *. inversion H0; clear H0; subst.
      exists t. eapply IHls. eauto.
  Qed.

  Lemma existsEach_ext : forall vs (F G : env.env -> Prop),
    (forall ls, F ls -> G ls) ->
    existsEach vs F -> existsEach vs G.
  Proof.
    clear. induction vs; simpl; intros; auto.
    destruct H0. exists x. eapply IHvs. 2: eassumption.
    intros. simpl in *. auto.
  Qed.

  Lemma existsEach_projT1_env' : forall (F : env.env -> Prop) vars r,
    F (r ++ vars) ->
    existsEach (typeof_env vars) (fun x => F (r ++ x)).
  Proof.
    clear. induction vars; simpl; intros; auto.
    exists (projT2 a). specialize (IHl (r ++ a :: nil)). destruct a; simpl in *.
    repeat rewrite app_ass in *. simpl in *.
    apply IHl in H.
    eapply existsEach_ext. 2: eapply H. intros; simpl in *.
    rewrite app_ass in *; simpl in *; auto.
  Qed.

  Lemma existsEach_projT1_env : forall (F : env.env -> Prop) vars,
    F vars ->
    existsEach (typeof_env vars) F.
  Proof.
    clear. intros. generalize (existsEach_projT1_env' F vars nil H). intros.
    eapply existsEach_ext; try eassumption. simpl. auto.
  Qed.

  Lemma existsEach_app : forall (P : env.env -> Prop) ls' ls,
    existsEach (ls ++ ls') P <->
    existsEach ls (fun e => existsEach ls' (fun e' => P (e ++ e'))).
  Proof.
    clear. split; generalize dependent P; generalize dependent ls; induction ls; simpl; intros;
      try solve [ eapply existsEach_ext; eauto ].

      destruct H.
      exists x. eapply IHls in H. eauto.
      destruct H; exists x. eapply IHls. eauto.
  Qed.

  Section Provable.
    Definition Provable (e : expr) : Prop :=
      match exprD e tvProp with
        | None => False
        | Some p => p
      end.

    Section all_provable.
      Variable ctor : Prop -> Prop -> Prop.
      Variable base : Prop.

      Fixpoint AllProvable_gen (es : list expr) : Prop :=
        match es with
          | nil => base
          | e :: es => ctor (Provable e) (AllProvable_gen es)
        end.
    End all_provable.

    Definition AllProvable := AllProvable_gen and True.
    Definition AllProvable_impl := AllProvable_gen Basics.impl.
    Definition AllProvable_and := AllProvable_gen and.

    Lemma AllProvable_app : forall a b,
      AllProvable a ->
      AllProvable b ->
      AllProvable (a ++ b).
    Proof.
      induction a; simpl; intuition auto.
    Qed.

    Lemma AllProvable_app' : forall b a,
      AllProvable (a ++ b) ->
      AllProvable a /\ AllProvable b.
    Proof.
      induction a; simpl; try solve [ intuition auto ]; intros.
    Qed.

    Lemma Provable_ValidProp : forall goal, Provable goal -> ValidProp goal.
      unfold Provable, ValidProp in *; intros;
        repeat match goal with
                 | [ _ : match ?E with None => _ | Some _ => _ end |- _ ] =>
                   destruct E
               end; intuition eauto.
    Qed.

  End Provable.

End env.

Lemma lookupAs_weaken : forall types t vars vars' x v,
  lookupAs (types := types) vars t x = Some v ->
  lookupAs (vars ++ vars') t x = Some v.
Proof.
  unfold lookupAs. intros. revert H.
  case_eq (nth_error vars x); intros.
  eapply nth_error_weaken in H. rewrite H. eauto.
  congruence.
Qed.


Lemma exprSubstU_exprD : forall ts tf tu tg tg' tg'' s t,
  exprD (types := ts) tf tu (tg ++ tg' ++ tg'') s t =
  exprD tf (tu ++ tg') (tg ++ tg'') (exprSubstU (length tg) (length tg' + length tg) (length tu) s) t.
Proof.
  induction s; simpl; intros; think; auto.
  { consider (NPeano.ltb x (length tg)); intros; simpl; unfold lookupAs in *; simpl.
    repeat rewrite nth_error_app_L in * by omega. reflexivity.
    consider (NPeano.ltb x (length tg' + length tg)); simpl; unfold lookupAs in *; intros.
    repeat rewrite nth_error_app_R in * by omega.
    repeat rewrite nth_error_app_L in * by omega.
    repeat rewrite nth_error_app_R in * by omega.
    cutrewrite (length tu + x - length tg - length tu = x - length tg); [ | omega ]. reflexivity.
    repeat (rewrite nth_error_app_R in * by omega).
    cutrewrite (x + length tg - (length tg' + length tg) - length tg = x - length tg - length tg'); [ | omega ].
    reflexivity. }
  { consider (NPeano.ltb x (length tu)); intros; simpl; unfold lookupAs.
    rewrite nth_error_app_L in * by omega. reflexivity.
    rewrite nth_error_app_R in * by omega.
    repeat rewrite nth_error_past_end by omega. reflexivity. }
  { destruct (nth_error tf f); auto. destruct (equiv_dec (Range s) t); auto.
    destruct s; simpl in *. unfold equiv in *; subst.
    generalize dependent Domain0; clear -H; induction H; destruct Domain0; simpl in *; intros; auto.
    think. destruct (exprD tf (tu ++ tg') (tg ++ tg'')
       (exprSubstU (length tg) (length tg' + length tg) (length tu) x) t0); auto. }
Qed.

Lemma exprD_weaken : forall types (fs : functions types) uvars uvars' vars vars' e t v,
  exprD fs uvars vars e t = Some v ->
  exprD fs (uvars ++ uvars') (vars ++ vars') e t = Some v.
Proof.
  clear. induction e; simpl; intros; eauto using lookupAs_weaken;
  repeat match goal with
           | [ H : match ?X with
                     | _ => _
                   end = _ |- _ ] => revert H; case_eq X; intros; try congruence
           | [ H : _ |- _ ] => rewrite H
           | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
             (revert H; case_eq X; intros; try congruence) ; []
           | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
             (destruct X; try congruence) ; []
           | [ H : forall x y, _ |- _ ] =>
             erewrite H by eauto
           | [ H : _ === _ |- _ ] =>
             unfold Equivalence.equiv in *; subst
         end; eauto using lookupAs_weaken.
  { destruct s; simpl in *.
    clear H0. generalize dependent Denotation. generalize dependent Domain0.
    generalize dependent l. clear. induction l; simpl; intros; destruct Domain0; auto.
    inversion H; clear H; subst.
    revert H2. case_eq (exprD fs uvars vars a t); intros.
    erewrite H3 by eassumption. eauto. congruence. }
Qed.

Lemma applyD_weaken : forall types (funcs : functions types) l D R F U G UE GE v,
  applyD (exprD funcs U G) D l R F = Some v ->
  applyD (exprD funcs (U ++ UE) (G ++ GE)) D l R F = Some v.
Proof.
  induction l; destruct D; simpl; intros; try congruence.
  consider (exprD funcs U G a t); intros.
  erewrite exprD_weaken by eauto. auto. congruence.
Qed.

Lemma Provable_weaken : forall types (fs : functions types) P U G UE GE,
  Provable fs U G P ->
  Provable fs (U ++ UE) (G ++ GE) P.
Proof.
  unfold Provable; intros. consider (exprD fs U G P tvProp); intros; try contradiction.
  erewrite exprD_weaken; eauto.
Qed.

Lemma AllProvable_weaken : forall types (fs : functions types) U G UE GE P,
  AllProvable fs U G P ->
  AllProvable fs (U ++ UE) (G ++ GE) P.
Proof.
  induction P; auto; intros; simpl in *; intuition eauto using Provable_weaken.
Qed.

Lemma liftExpr_ext : forall types (funcs : functions types) U U' U'' G G' G'' e t,
  exprD funcs (U'' ++ U) (G'' ++ G) e t =
  exprD funcs (U'' ++ U' ++ U) (G'' ++ G' ++ G) (liftExpr (length U'') (length U') (length G'') (length G') e) t.
Proof.
  clear. induction e; simpl; intros; unfold lookupAs; think; try reflexivity;
    repeat match goal with
             | [ |- context [ NPeano.ltb ?X ?Y ] ] =>
               consider (NPeano.ltb X Y); intros
             | [ |- _ ] => rewrite nth_error_app_L by omega
             | [ |- _ ] => rewrite nth_error_app_R by omega
             | [ |- match nth_error _ ?X with _ => _ end = match nth_error _ ?Y with _ => _ end ] =>
               cutrewrite (X = Y); try (reflexivity || omega)
           end; auto.
  destruct (nth_error funcs f); auto. destruct (equiv_dec (Range s) t); auto. unfold equiv in *. subst.
    destruct s; simpl. generalize dependent Domain0; induction H; destruct Domain0; simpl; intros; think; auto.
    destruct (exprD funcs (U'' ++ U' ++ U) (G'' ++ G' ++ G)
       (liftExpr (length U'') (length U') (length G'') (length G') x) t); think; auto.
Qed.

Section exists_subst.
  Variable types : list type.
  Variable funcs : functions types.

  Theorem exprSubstU_spec : forall e a b c e',
    exprSubstU a b c e = e' ->
    forall A B C D t v,
      length B = a ->
      length B + length C = b ->
      length A = c ->
      exprD funcs A (B ++ C ++ D) e t = Some v ->
      exprD funcs (A ++ C) (B ++ D) e' t = Some v.
  Proof.
    intros.
    rewrite exprSubstU_exprD in H3. subst. rewrite Plus.plus_comm. auto.
  Qed.

  Variable U1 : env types.

  (* Unification variables corresponding to genuine Coq existentials *)
  Fixpoint exists_subst (CU : env types)
    (U : list (tvar * option (expr types)))
    : (env types -> Prop) -> Prop :=
    match U , CU with
      | nil , nil => fun cc => cc nil
      | (t,v) :: U' , existT t' v' :: CU'  => fun cc =>
        match v with
          | None =>
            exists v : tvarD types t, exists_subst (match CU with
                                                      | nil => nil
                                                      | _ :: CU' => CU'
                                                    end) U' (fun z => cc (existT _ t v :: z))
          | Some v =>
            match exprD funcs CU U1 v t' with
              | None => False
              | Some v1 => v' = v1 /\ exists_subst CU' U' (fun z => cc (existT _ t' v1 :: z))
            end
        end
      | _ , _ => fun _ => False
    end.

Lemma exists_subst_exists : forall (B : list (tvar * option (expr types))) CU P,
  exists_subst CU B P ->
  exists C, P C.
Proof.
  clear. induction B; simpl; intros.
    destruct CU. eauto.
    contradiction.

    destruct a; destruct CU; simpl in *; try contradiction.
    destruct s; destruct o.
    match goal with
      | [ H : match ?X with | None => _ | Some _ => _ end |- _ ] => destruct X
    end; intuition; subst; auto.
    apply IHB in H1. destruct H1. eauto.
    destruct H. eapply IHB in H. destruct H; eauto.
Qed.

Lemma nth_error_Some_length : forall T (ls : list T) n v,
  nth_error ls n = Some v ->
  (n < length ls)%nat.
Proof.
  clear; induction ls; destruct n; intros; simpl in *; unfold value, error in *; try (congruence || omega).
  eapply IHls in H. omega.
Qed.

Definition is_well_typed_not_mentionsU_last : forall tfuncs tU tG t (e : expr types) t',
  is_well_typed tfuncs (tU ++ t :: nil) tG e t' = true ->
  mentionsU (length tU) e = false ->
  is_well_typed tfuncs tU tG e t' = true.
Proof.
  clear; induction e; intros; simpl in *; auto;
    repeat match goal with
             | [ H : context [ match ?X with _ => _ end ] |- _ ] =>
               consider X; intros
             | [ H : _ && _ = true |- _ ] => apply andb_true_iff in H; destruct H
             | [ H : _ || _ = false |- _ ] => apply orb_false_iff in H; destruct H
             | [ H : _ |- _ ] => erewrite H by eauto
             | [ H : _ === _ |- _ ] => unfold equiv in H; subst
           end; try congruence; auto.
  { rewrite nth_error_app_L in H; auto. rewrite H. consider (tvar_seqb t0 t0); auto.
    apply nth_error_Some_length in H. rewrite app_length in H. simpl in *. omega. }
  { destruct t0; simpl in *. clear H0. generalize dependent TDomain0. revert H1.
    induction H; destruct TDomain0; intros; simpl in *; try congruence.
    apply orb_false_iff in H1. destruct H1.
    consider (is_well_typed tfuncs (tU ++ t :: nil) tG x t0); intros.
    rewrite H by eauto. eapply IHForall; eauto. }
Qed.

Lemma is_well_typed_weaken : forall tf tu tg u' g' (e : expr types) t,
  is_well_typed tf tu tg e t = true ->
  is_well_typed tf (tu ++ u') (tg ++ g') e t = true.
Proof.
  clear; induction e; simpl in *; intros; think; auto.
  { erewrite nth_error_weaken by eauto. consider (tvar_seqb t0 t0); auto. }
  { erewrite nth_error_weaken by eauto. consider (tvar_seqb t0 t0); auto. }
  { destruct t0; simpl in *; clear H0. generalize dependent TDomain0. induction H; intros; simpl in *; think; auto. }
Qed.

Lemma all2_is_well_typed_weaken : forall tf tU tG es ts,
  all2 (is_well_typed (types := types) tf tU tG) es ts = true ->
  forall u g,
    all2 (is_well_typed tf (tU ++ u) (tG ++ g)) es ts = true.
Proof.
  clear. intros. eapply all2_impl; eauto using is_well_typed_weaken.
Qed.

End exists_subst.

Lemma applyD_impl_Forall : forall types F F' P Dom args R D v,
  applyD (types := types) F Dom args R D = Some v ->
  Forall P args ->
  (forall x y v, P x -> F x y = Some v -> F' x y = Some v) ->
  applyD F' Dom args R D = Some v.
Proof.
  induction Dom; destruct args; simpl; intros; think; auto. inversion H0; subst; intros.
  erewrite H1; eauto.
Qed.

Lemma applyD_impl : forall types F F' Dom args R D,
  (forall x y, F x y = F' x y) ->
  applyD (types := types) F Dom args R D = applyD F' Dom args R D.
Proof.
  induction Dom; destruct args; simpl; intros; think; auto.
  destruct (F' e a); auto.
Qed.

Lemma applyD_map : forall types F F' Dom args R D,
  applyD (types := types) F Dom (map F' args) R D = applyD (fun x y => F (F' x) y) Dom args R D.
Proof.
  induction Dom; destruct args; simpl; intros; think; auto.
  destruct (F (F' e) a); auto.
Qed.

(** Use this function to get an environment extension
 ** - n is the length of the old environment
 **)
Definition env_ext (T : Type) n (ls : list T) : list T :=
  firstn (length ls - n) ls.

(** TODO: There probably need to be some facts about this... **)

Arguments Const {types} {t} (_).
Arguments Var {types} (_).
Arguments UVar {types} (_).
Arguments Func {types} (_) (_).
Arguments Equal {types} (_) (_) (_).
Arguments Not {types} (_).
