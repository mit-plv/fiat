Require Import ADTSynthesis.FiatToFacade.Utilities ADTSynthesis.FiatToFacade.BedrockUtilities ADTSynthesis.FiatToFacade.StringMapUtilities.
Require Import ADTSynthesis.FiatToFacade.FacadeNotations ADTSynthesis.FiatToFacade.StringMapNotations.
Require Import Bedrock.Bedrock Bedrock.Platform.Facade.DFacade Bedrock.Platform.Facade.examples.FiatADTs Bedrock.Platform.Cito.StringMap.
Require Import Bedrock.Platform.Cito.SyntaxExpr.
Require Import Coq.Lists.List Coq.Program.Program.

Lemma binop_Eq_true_iff :
  forall w1 w2,
    Some (IL.wneb (eval_binop (inr IL.Eq) w1 w2)
                  (Word.natToWord 32 0)) = Some true ->
    w1 = w2.
Proof.
  unfold eval_binop, IL.evalTest, IL.wneb, IL.weqb; intros.
  destruct (Word.weqb w1 w2) eqn:eq0;
  try solve [compute in *; discriminate];
  rewrite ?Word.weqb_true_iff, ?weqb_false_iff in eq0;
  assumption.
Qed.

Lemma BoolToW_eval :
  forall {av} state var b1 b2,
    b1 = negb b2 ->
    state[var >> SCA av (BoolToW b1)] ->
    eval_bool state (var = 0)%facade = Some b2.
Proof.
  unfold_coercions; unfold BoolToW, eval_bool, eval, eval_binop_m;
  intros; destruct_pairs; subst; subst_find; destruct b2; subst; reflexivity.
Qed.

Lemma SCA_inj :
  forall av v v',
    SCA av v = SCA av v' -> v = v'.
Proof.
  autoinj.
Qed.

Lemma ADT_inj :
  forall av v v',
    @ADT av v = @ADT av v' -> v = v'.
Proof.
  autoinj.
Qed.

Lemma List_inj :
  forall (x y : list Memory.W),
    ADT (List x) = ADT (List y) ->
    x = y.
Proof.
  autoinj.
Qed.

Lemma List_inj' : forall x y : list W, List x = List y -> x = y.
  intros * _eq; injection _eq; intros; assumption.
Qed.

Lemma eval_binop_inv :
  forall (test: bool),
    IL.wneb (eval_binop (inr IL.Eq) (if test then 1 else 0) 0)
            (Word.natToWord 32 0) = negb test.
Proof.
  intros; destruct test; simpl; reflexivity.
Qed.

Require Import Bedrock.Platform.Cito.SyntaxExpr.

Fixpoint AllVariables expr :=
  match expr with
    | Var str => (str :: nil)
    | Const _ => nil
    | Binop _ e1 e2 => (AllVariables e1 ++ AllVariables e2)%list
    | TestE _ e1 e2 => (AllVariables e1 ++ AllVariables e2)%list
  end.

Lemma eval_expr_some_sca {av} :
  forall expr state,
    (forall k, List.In k (AllVariables expr) -> exists v, state[k >> SCA av v]) ->
    exists sca, eval state expr = Some (SCA _ sca).
Proof.
  induction expr; simpl; intros * h.

  destruct (h s (or_introl eq_refl)) as [v maps_to].
  eexists; rewrite <- StringMapFacts.find_mapsto_iff; eauto.

  eexists; eauto.

  setoid_rewrite in_app_iff in h.
  destruct (IHexpr1 _ (fun k => or_left_imp (h k))) as [x hx].
  destruct (IHexpr2 _ (fun k => or_right_imp (h k))) as [y hy].
  eexists; rewrite hx, hy; simpl; eauto.

  setoid_rewrite in_app_iff in h.
  destruct (IHexpr1 _ (fun k => or_left_imp (h k))) as [x hx].
  destruct (IHexpr2 _ (fun k => or_right_imp (h k))) as [y hy].
  eexists; rewrite hx, hy; simpl; eauto.
Qed.

Ltac inversion_facade :=
  match goal with
    | [ H: RunsTo _ ?p _ _ |- _ ] =>
      match p with
        | DFacade.Skip => idtac
        | DFacade.Seq _ _ => idtac
        | DFacade.If _ _ _ => idtac
        | DFacade.While _ _ => idtac
        | DFacade.Call _ _ _ => idtac
        | DFacade.Assign _ _ => idtac
        | _ => fail 1
      end; inversion_clear' H
  end.

Ltac BoolToW_eval_helper :=
  try match goal with
        | [ |- true = negb ?a ] => unify a false; reflexivity
        | [ |- false = negb ?a ] => unify a true; reflexivity
      end.

Lemma mapM_MapsTo_0 :
  forall av st,
    ListFacts4.mapM (@sel av st) (nil) = Some nil.
Proof.
  firstorder.
Qed.

Lemma mapM_MapsTo_1 :
  forall av st k v,
    st [k >> v] ->
    ListFacts4.mapM (@sel av st) (k :: nil) = Some (v :: nil).
Proof.
  unfold sel; intros; simpl.
  subst_find; reflexivity.
Qed.

Lemma mapM_MapsTo_2 :
  forall (av : Type) (st : StringMap.t (Value av))
         (k k' : StringMap.key) (v v' : Value av),
    (st) [k >> v] ->
    (st) [k' >> v'] ->
    ListFacts4.mapM (sel st) (k :: k' :: nil) = Some (v :: v' :: nil).
Proof.
  intros; unfold sel; simpl.
  repeat subst_find; reflexivity.
Qed.

Lemma mapM_not_in_args :
  forall {av} (st st': State av) args input k w,
    ~ List.In k args ->
    StringMap.Equal st' (StringMap.add k (SCA _ w) st) ->
    ListFacts4.mapM (sel st) args = Some input ->
    ListFacts4.mapM (sel st') args = Some input.
Proof.
  induction args; simpl in *; intros.
  + congruence.
  + destruct (sel st a) eqn:eq1;
    destruct (ListFacts4.mapM (sel st) args) eqn:eq2;
    try discriminate.
    erewrite IHargs; eauto.
    replace (sel st' a) with (sel st a).
    rewrite eq1; assumption.

    unfold sel; rewrite H0.
    symmetry; apply StringMapFacts.add_neq_o; intuition.
Qed.

Lemma true_and_false :
  forall {av} st expr,
    @is_true av st expr ->
    @is_false av st expr ->
    False.
Proof.
  unfold is_true, is_false; intros.
  eq_transitive; discriminate.
Qed.

Lemma unchanged :
  forall av (st: State av) arg val,
    StringMap.find arg st = Some (ADT val) ->
    StringMap.Equal
      st (add_remove_many (arg :: nil) (ADT val :: nil) (Some (ADT val) :: nil) st).
Proof.
  simpl; intros.
  red; intro arg'.
  destruct (StringMap.E.eq_dec arg arg'); subst.

  rewrite StringMapFacts.add_eq_o; trivial.
  rewrite StringMapFacts.add_neq_o; trivial.
Qed.


Lemma eval_bool_eq_false_sca :
  forall {av} k v1 v2 state,
    SCA av v1 <> SCA av v2 ->
    state[k >> SCA _ v1] ->
    @eval_bool av state (Var k = Const v2)%facade = Some false.
Proof.
  intros; unfold eval_bool; simpl; subst_find; simpl.
  rewrite weqb_false by congruence; reflexivity.
Qed.

Lemma is_true_eq :
  forall {av} state var w,
    is_true state (Var var = Const w)%facade <->
    state[var >> SCA av w].
Proof.
  unfold is_true, eval_bool, eval, eval_binop_m; split; intros.

  destruct (StringMap.find var state) as [ [ | ] | ] eqn:eq0;
    try discriminate;
    apply binop_Eq_true_iff in H;
    rewrite StringMapFacts.find_mapsto_iff; congruence.

  subst_find.
  simpl; unfold IL.weqb; rewrite weqb_refl; reflexivity.
Qed.


Lemma NoDup_0 :
  forall {A},
    NoDup (@nil A).
Proof.
  intros; constructor.
Qed.

Lemma NoDup_1 :
  forall {A} (a: A),
    NoDup (a :: nil).
Proof.
  intros; constructor; eauto using NoDup_0.
Qed.

Lemma NoDup_2 :
  forall {A} (a b: A),
    a <> b -> NoDup (a :: b :: nil).
Proof.
  intros; constructor; eauto using NoDup_1. simpl; intuition.
Qed.

(*
Lemma RunsTo_label :
  forall av env st1 st2 vpointer label w,
    Label2Word env label = Some w ->
    @RunsTo av env (Label vpointer label) st1 st2 ->
    StringMap.Equal st2 (StringMap.add vpointer (SCA _ w) st1).
Proof.
  intros.
  inversion_facade.
  eq_transitive; autoinj.
Qed.


Lemma RunsTo_Var :
  forall env st st' vpointer label w args label',
    Label2Word env label = Some w ->
    (st) [vpointer >> SCA FacadeADT w]
    -> RunsTo env (Facade.Call label' (Var vpointer) args) st st'
    -> RunsTo env (Facade.Call label' w args) st st'.
Proof.
  intros.
  inversion_facade;
    simpl in *;
    rewrite StringMapFacts.find_mapsto_iff in *;
    eq_transitive; autoinj.
  - rewrite H0 in H6; autoinj; econstructor; eauto.
  - rewrite H0 in H6; autoinj; econstructor 10; eauto.
Qed. *)

Lemma SafeSeq_inv :
  forall {av env} {a b : Stmt} {st st' : State av},
    RunsTo env a st st' ->
    Safe env (Seq a b) st ->
    Safe env b st'.
Proof.
  intros * h' h; inversion h. intuition.
Qed.

Lemma mapsto_eval :
  forall {av} scas k w,
    (scas) [k >> SCA av w] ->
    eval scas k = Some (SCA av w).
Proof.
  intros; simpl.
  subst_find; reflexivity.
Qed.
