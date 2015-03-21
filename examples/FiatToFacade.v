Ltac rnm a b :=
  rename a into b.

Require Import Cito.facade.Facade.

Require Import StringMap.
Require Import SyntaxExpr.
Require Import Memory.

Require Import AutoDB.

Unset Implicit Arguments.

Lemma length_0 :
  forall {A: Type} (l: list A),
    0 = Datatypes.length l <-> l = [].
Proof.
  destruct l; intros; simpl in *; intuition congruence.
Qed.

(* Generic notations *)

Notation "table [ key >> value ]" := (StringMap.MapsTo key value table) (at level 0).

(* Facade notations and coercions *)

Definition nat_as_word n : Word.word 32 := Word.natToWord 32 n.
Coercion nat_as_word : nat >-> Word.word.

Definition string_as_var str : Expr := Var str.
Coercion string_as_var : string >-> Expr.

Definition word_as_constant w : Expr := Const w.
Coercion word_as_constant : W >-> Expr.

Definition nat_as_constant n : Expr := Const (Word.natToWord 32 n).
Coercion nat_as_constant : nat >-> Expr.

Ltac unfold_coercions :=
  unfold string_as_var, nat_as_constant, nat_as_word, word_as_constant in *.

Notation "A ; B" := (Seq A B) (at level 201,
                               B at level 201,
                               left associativity,
                               format "'[v' A ';' '/' B ']'") : facade_scope.
Delimit Scope facade_scope with facade.

Notation "x <- y" := (Assign x y) (at level 100) : facade_scope.
Notation "y <- f" := (Call y f nil) (at level 100, no associativity) : facade_scope.
Notation "y <- f x1 .. xn" := (Call y f (cons x1 .. (cons xn nil) ..))
                                 (at level 100, no associativity) : facade_scope.

Notation "A < B" := (TestE IL.Lt A B) : facade_scope.
Notation "A <= B" := (TestE IL.Le A B) : facade_scope.
Notation "A <> B" := (TestE IL.Ne A B) : facade_scope.
Notation "A = B" := (TestE IL.Eq A B) : facade_scope.
Notation "! x" := (x = 0)%facade (at level 70, no associativity).

Notation "A * B" := (Binop IL.Times A B) : facade_scope.
Notation "A + B" := (Binop IL.Plus A B) : facade_scope.
Notation "A - B" := (Binop IL.Minus A B) : facade_scope.

Notation "'While' A B" := (While A B)
                            (at level 200,
                             A at level 0,
                             B at level 1000,
                             format "'[v    ' 'While'  A '/' B ']'")
                          : facade_scope.

Notation "'If' a 'then' b 'else' c" := (Facade.If a b c)
                                          (at level 200,
                                           a at level 1000,
                                           b at level 1000,
                                           c at level 1000,
                                          format "'[v' '[v    ' 'If'  a  'then' '/' b ']' '/' '[v    ' 'else' '/' c ']' ']'")
                                       : facade_scope.

Definition Fold (head is_empty seq: StringMap.key)
                _pop_ _empty_ loop_body := (
    Call is_empty _empty_ (seq :: nil);
    While (!is_empty) (
        Call head _pop_ (seq :: nil);
        loop_body;
        Call is_empty _empty_ (seq :: nil)
    )
)%facade.

Print Fold.

(* Tactics *)

Ltac autoinj :=
  intros; repeat (match goal with
                    | [ H: ?f ?a = ?f ?b |- _ ] =>
                      (injection H; intros; clear H)
                    | [ H: ?f ?x ?a = ?f ?x ?b |- _ ] =>
                      (injection H; intros; clear H)
                    | [ H: ?f ?a1 ?b1 = ?f ?a2 ?b2 |- _ ] =>
                      (injection H; intros; clear H)
                  end; try subst); try solve [intuition].

Ltac autoinj' :=
  intros;
  repeat match goal with
           | [ H: context[?f ?A _ = ?f ?A _] |- _ ] =>
             let H' := fresh in
             assert (forall x y, f A x = f A y <-> x = y)
               as H'
                 by (
                     let H'' := fresh in
                     split;
                     intros ** H'';
                     [injection H'' | rewrite H''];
                     intuition);
               try rewrite H' in *; clear H'
         end;
  try solve [intuition].

Ltac autospecialize :=
  repeat match goal with
           | [ H: forall a b, ?x a -> ?y a b -> _, H': ?x _, H'': ?y _ _ |- _ ]
             => specialize (H _ _ H' H'')
           | [ H: forall a b, ?x a /\ ?x' a -> ?y a b -> _, H'1: ?x _, H'2: ?x' _, H'': ?y _ _ |- _ ]
             => specialize (H _ _ (conj H'1 H'2) H'')
           | [ H: forall a b, ?x a /\ ?x' a /\ ?x'' a -> ?y a b -> _, H'1: ?x _, H'2: ?x' _, H'3: ?x'' _, H'': ?y _ _ |- _ ]
             => specialize (H _ _ (conj (conj H'1 H'2) H'3) H'')
         end.

Ltac expand :=
  repeat match goal with
           | [ H := _ |- _ ] => unfold H in *; clear H
         end.

Ltac autorewrite_equal :=
  match goal with
    | [ H: StringMap.Equal ?a _, H': context[?a] |- _ ] => rewrite H in H'
    | [ H: StringMap.Equal ?a _ |- _ ] => rewrite H in *
    | [ H: StringMap.Equal ?a _ |- _ ] => setoid_rewrite H
  end.

Ltac subst_find :=
  match goal with
    | [H : StringMap.find ?a ?b = _,
           H': context[match StringMap.find ?a ?b with | Some _ => _ | None => _ end] |- _] =>
      setoid_rewrite H in H' (* Wonder why setoid is needed here *)
  end. (* TODO: Generalize to use MapsTo, and use instread of calling StringMapFacts.find_mapsto_iff everywhere. *)

Ltac autodestruct :=
  repeat match goal with
           | [ H: exists x, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
         end.

Ltac inversion_clear' hyp :=
  inversion hyp; expand; subst; clear hyp.

Ltac eq_transitive :=
  match goal with
    | [ H: ?a = ?b, H': ?a = ?c |- _ ] =>
      let H'' := fresh in
      assert (b = c) as H'' by (rewrite <- H, <- H'; reflexivity)
  end. (* TODO: Use more. Extend to cover a single map mapping the same key to two variables *)

Ltac map_iff_solve' fallback :=
  match goal with
    | [ |- ?A /\ ?B ] => split; map_iff_solve' fallback
    | [ |- (?a = ?a /\ _) \/ (?a <> ?a /\ _) ] => left; split; [ apply eq_refl | map_iff_solve' fallback ]
    | [ |- (?a = ?b /\ _) \/ (?a <> ?b /\ _) ] => right; split; [ congruence | map_iff_solve' fallback ]
    | _ => fallback
  end.

Ltac map_iff_solve fallback :=
  StringMapFacts.map_iff;
  map_iff_solve' fallback.

Lemma Some_inj : forall A (x y: A),
                   Some x = Some y -> x = y.
  autoinj.
Qed.

Lemma SCA_inj :
  forall av v v',
    SCA av v = SCA av v' -> v = v'.
Proof.
  autoinj.
Qed.

Lemma ADT_inj :
  forall av v v',
    @Facade.ADT av v = @Facade.ADT av v' -> v = v'.
Proof.
  autoinj.
Qed.

Lemma List_inj :
  forall x y : list W,
    Facade.ADT (List x) = Facade.ADT (List y) ->
    x = y.
Proof.
  autoinj.
Qed.

Lemma MapsTo_unique :
  forall {A} map key (v1 v2: A),
    StringMap.MapsTo key v1 map ->
    StringMap.MapsTo key v2 map ->
    v1 = v2.
Proof.
  intros;
  rewrite StringMapFacts.find_mapsto_iff in *;
  eq_transitive; autoinj; assumption.
Qed.

Definition cond_respects_MapEq {elt} :=
  Proper (StringMap.Equal (elt := elt) ==> iff).

Definition BoolToW (b: bool) := if b then WOne else WZero.

Definition WToBool (w: @Word.word 32) := negb (Word.weqb w WZero).

Lemma BoolToW_invert : forall b, WToBool (BoolToW b) = b.
Proof.
  destruct b; intuition.
Qed.

Lemma eval_binop_inv :
  forall (test: bool),
    IL.wneb (eval_binop (inr IL.Eq) (if test then WOne else WZero) WZero)
            (Word.natToWord 32 0) = negb test.
Proof.
  intros; destruct test; simpl; reflexivity.
Qed.

Lemma compile_if :
  forall { av env } (testvar: StringMap.key) {retvar} {ret_type} (wrapper: ret_type -> Value av) (test: bool) (precond postcond: _ -> Prop) truecase falsecase,
  refine (Pick (fun prog => forall init_state final_state,
                              precond init_state ->
                              @RunsTo av env prog init_state final_state ->
                              (StringMap.MapsTo retvar (wrapper (if test then truecase else falsecase)) final_state
                               /\ postcond final_state)))
         (Bind (Pick (fun progtest => forall init_state inter_state,
                                        precond init_state ->
                                        RunsTo env progtest init_state inter_state ->
                                        (StringMap.MapsTo testvar (SCA av (BoolToW test)) inter_state /\
                                         precond inter_state)))
               (fun ptest =>
                  (Bind (Pick (fun prog1 => forall inter_state final_state,
                                              (test = true /\
                                               precond inter_state /\
                                               StringMap.MapsTo testvar (SCA av (BoolToW test)) inter_state) ->
                                              RunsTo env prog1 inter_state final_state ->
                                              (StringMap.MapsTo retvar (wrapper truecase) final_state /\
                                               postcond final_state)))
                        (fun p1 =>
                           Bind
                             (Pick (fun prog2 =>
                                      forall inter_state final_state,
                                        (test = false /\
                                         precond inter_state /\
                                         StringMap.MapsTo testvar (SCA av (BoolToW test)) inter_state) ->
                                        RunsTo env prog2 inter_state final_state ->
                                        (StringMap.MapsTo retvar (wrapper falsecase) final_state /\
                                         postcond final_state)))
                             (fun p2 => ret (Seq ptest
                                                 (Facade.If (SyntaxExpr.TestE IL.Eq
                                                                              (testvar)
                                                                              (0))
                                                            (p2)
                                                            (p1)))))))).
Proof.
  unfold refine.
  unfold_coercions.

  intros av env testvar retvar ret_type wrapper test precond postcond truecase falsecase wrapper_inj ** .
  inversion_by computes_to_inv.
  rnm x ptest.
  rnm x0 ptrue.
  rnm x1 pfalse.
  rnm H pfalse_retval.
  rnm H4 pfalse_postcond.
  rnm H2 ptrue_retval.
  rnm H5 ptrue_postcond.
  rnm H1 ptest_testvar.
  rnm H6 ptest_precond.

  constructor. intros ? ? init_state_consistent v_runs.
  subst.

  inversion_clear v_runs; subst.
  inversion_clear H0; subst;
  unfold is_true, is_false, eval_bool, eval, eval_binop_m in H1;
    rnm st' inter_state;
    (destruct (StringMap.find (elt:=Value av) testvar inter_state) as [ v | ] eqn:testvar_correct; try congruence);
  (destruct v as [ testw | ]; try congruence);
    apply Some_inj in H1;
  specialize (ptest_testvar init_state inter_state init_state_consistent H);
  rewrite <- StringMapFacts.find_mapsto_iff in *;
  pose proof (MapsTo_unique _ _ _ _ ptest_testvar testvar_correct) as Heq; apply SCA_inj in Heq; subst; clear testvar_correct;
  unfold BoolToW in H1;
  rewrite eval_binop_inv, ?negb_true_iff, ?negb_false_iff in H1; subst;
  specialize (ptest_precond init_state inter_state init_state_consistent H).

  (* TODO extend autospecialize to deal with this *)
  specialize (pfalse_retval inter_state final_state (conj (@eq_refl _ _) (conj ptest_precond ptest_testvar)) H2).
  specialize (pfalse_postcond inter_state final_state (conj (@eq_refl _ _) (conj ptest_precond ptest_testvar)) H2).
  intuition.

  specialize (ptrue_retval inter_state final_state (conj (@eq_refl _ _) (conj ptest_precond ptest_testvar)) H2).
  specialize (ptrue_postcond inter_state final_state (conj (@eq_refl _ _) (conj ptest_precond ptest_testvar)) H2).
  intuition.
Qed.

Lemma compile_binop :
  forall op,
  forall retvar temp1 temp2,
  forall av env,
  forall (precond postcond: State _ -> Prop),
  forall w1 w2,
    cond_respects_MapEq postcond ->
    (forall x state, postcond state -> postcond (StringMap.add retvar x state)) ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                (StringMap.MapsTo retvar (SCA av ((IL.evalBinop op) w1 w2)) final_state
                                 /\ postcond final_state)))
           (Bind (Pick (fun prog1 => forall init_state inter_state,
                                       precond init_state ->
                                       RunsTo env prog1 init_state inter_state ->
                                       (StringMap.MapsTo temp1 (SCA av w1) inter_state
                                        /\ precond inter_state)))
                 (fun p1 =>
                    Bind
                      (Pick (fun prog2 =>
                               forall inter_state final_state,
                                 precond inter_state /\ inter_state[temp1 >> SCA av w1] ->
                                 RunsTo env prog2 inter_state final_state ->
                                 final_state[temp2 >> SCA av w2]
                                  /\ final_state[temp1 >> SCA av w1]
                                  /\ postcond final_state))
                      (fun p2 => ret (Seq p1
                                          (Seq p2
                                               (Assign retvar
                                                       (SyntaxExpr.Binop
                                                          op
                                                          (temp1)
                                                          (temp2)))))))).
  unfold refine; simpl.
  intros op retvar temp1 temp2 av env precond postcond w1 w2 postcond_meaningful postcond_indep_retvar ** .
  inversion_by computes_to_inv.
  rnm x prog1.
  rnm x0 prog2.
  rnm H prog2_returns_w2.
  rnm H3 prog1_returns_w1.
  rnm H5 prog1_consistent.
  rnm H1 prog2_consistent.
  rnm H4 prog2_ensures_postcond.
  constructor; intros.
  rnm H init_state_consistent.
  subst.
  inversion H0; subst; clear H0.
  inversion H5; subst; clear H5.
  rnm st' post_prog1_state.
  rnm st'0 post_prog2_state.


  autospecialize.
  clear H2.
  clear H1.

  inversion_clear H6.

  unfold cond_respects_MapEq in postcond_meaningful.
  rewrite H1; clear H1.

  unfold eval in H; simpl in H;
  unfold eval_binop_m in H; simpl in H.

  set (StringMap.find temp1 _) as r1 in H.
  set (StringMap.find temp2 _) as r2 in H.
  destruct r1 eqn:eq1; subst; try congruence.
  destruct v; try congruence.
  destruct r2 eqn:eq2; subst; try congruence.
  destruct v; try congruence.

  rewrite StringMapFacts.find_mapsto_iff in *.
  rewrite <- StringMapFacts.find_mapsto_iff in *.
  subst.

  inversion_clear H.

  pose proof (MapsTo_unique _ _ _ _ eq1 prog2_consistent); apply SCA_inj in H; subst; clear eq1; clear prog1_returns_w1.
  pose proof (MapsTo_unique _ _ _ _ eq2 prog2_returns_w2); apply SCA_inj in H; subst; clear eq2; clear prog2_returns_w2.

  split.

  apply StringMap.add_1; reflexivity.
  apply postcond_indep_retvar; eauto.
Qed.

Lemma compile_test : (* Exactly the same proof as compile_binop *)
  forall op,
  forall (retvar temp1 temp2: StringMap.key),
  forall av env,
  forall (precond postcond: State _ -> Prop),
  forall w1 w2,
    cond_respects_MapEq postcond ->
    (forall x state, postcond state -> postcond (StringMap.add retvar x state)) ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                final_state[retvar >> SCA av (BoolToW ((IL.evalTest op) w1 w2))]
                                 /\ postcond final_state))
           (Bind (Pick (fun prog1 => forall init_state inter_state,
                                       precond init_state ->
                                       RunsTo env prog1 init_state inter_state ->
                                       (inter_state[temp1 >> SCA av w1]
                                        /\ precond inter_state)))
                 (fun p1 =>
                    Bind
                      (Pick (fun prog2 =>
                               forall inter_state final_state,
                                 precond inter_state /\ inter_state[temp1 >> SCA av w1] ->
                                 RunsTo env prog2 inter_state final_state ->
                                 final_state[temp2 >> SCA av w2]
                                  /\ final_state[temp1 >> SCA av w1]
                                  /\ postcond final_state))
                      (fun p2 => ret (Seq p1
                                          (Seq p2
                                               (Assign retvar
                                                       (SyntaxExpr.TestE
                                                          op
                                                          (temp1)
                                                          (temp2)))))))).
  unfold refine; simpl.
  unfold_coercions.

  intros op retvar temp1 temp2 av env precond postcond w1 w2 postcond_meaningful postcond_indep_retvar ** .
  inversion_by computes_to_inv.
  rnm x prog1.
  rnm x0 prog2.
  rnm H prog2_returns_w2.
  rnm H3 prog1_returns_w1.
  rnm H5 prog1_consistent.
  rnm H1 prog2_consistent.
  rnm H4 prog2_ensures_postcond.
  constructor; intros.
  rnm H init_state_consistent.
  subst.
  inversion H0; subst; clear H0.
  inversion H5; subst; clear H5.
  rnm st' post_prog1_state.
  rnm st'0 post_prog2_state.

  autospecialize.
  clear H2.
  clear H1.

  inversion_clear H6.

  unfold cond_respects_MapEq in postcond_meaningful.
  rewrite H1; clear H1.

  unfold eval in H; simpl in H;
  unfold eval_binop_m in H; simpl in H.

  set (StringMap.find temp1 _) as r1 in H.
  set (StringMap.find temp2 _) as r2 in H.
  destruct r1 eqn:eq1; subst; try congruence.
  destruct v; try congruence.
  destruct r2 eqn:eq2; subst; try congruence.
  destruct v; try congruence.

  rewrite StringMapFacts.find_mapsto_iff in *.
(*  rewrite <- prog2_consistent in *.
  rewrite <- prog1_returns_w1 in *; clear prog1_returns_w1. *)
  rewrite <- StringMapFacts.find_mapsto_iff in *.
  subst.

  inversion_clear H.

  pose proof (MapsTo_unique _ _ _ _ eq1 prog2_consistent); apply SCA_inj in H; subst; clear eq1; clear prog1_returns_w1.
  pose proof (MapsTo_unique _ _ _ _ eq2 prog2_returns_w2); apply SCA_inj in H; subst; clear eq2; clear prog2_returns_w2.

  split.

  apply StringMap.add_1; reflexivity.
  apply postcond_indep_retvar; eauto.
Qed.

Lemma weaken_preconditions :
  forall av env (old_precond new_precond postcond: State av -> Prop),
    (forall s, old_precond s -> new_precond s) ->
    refine
      (Pick (fun prog =>
               forall init_state final_state,
                 old_precond init_state ->
                 RunsTo env prog init_state final_state ->
                 postcond final_state))
      (Pick (fun prog =>
               forall init_state final_state,
                 new_precond init_state ->
                 RunsTo env prog init_state final_state ->
                 postcond final_state)).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  constructor; intros; eapply H0; intuition. apply H; eassumption. eassumption.
Qed.

Lemma drop_preconditions :
  forall av env (precond postcond: State av -> Prop),
    refine
      (Pick (fun prog =>
               forall init_state final_state,
                 precond init_state ->
                 RunsTo env prog init_state final_state ->
                 postcond final_state))
      (Pick (fun prog =>
               forall init_state final_state,
                 (fun _ => True) init_state ->
                 RunsTo env prog init_state final_state ->
                 postcond final_state)).
Proof.
  eauto using weaken_preconditions.
Qed.

Lemma strengthen_postconditions :
  forall av env (precond old_postcond new_postcond: State av -> Prop),
    (forall s, new_postcond s -> old_postcond s) ->
    refine
      (Pick (fun prog =>
               forall init_state final_state,
                 precond init_state ->
                 RunsTo env prog init_state final_state ->
                 old_postcond final_state))
      (Pick (fun prog =>
               forall init_state final_state,
                 precond init_state ->
                 RunsTo env prog init_state final_state ->
                 new_postcond final_state)).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  constructor; intros; eapply H; intuition; eapply H0; eassumption.
Qed.

Lemma start_compiling' ret_var :
  forall {av env init_state} v,
    refine (ret v)
           (Bind (Pick (fun prog =>
                          forall init_state final_state,
                            (fun x => True) init_state ->
                            RunsTo env prog init_state final_state ->
                            final_state[ret_var >> SCA av v]
                            /\ (fun x => True) final_state))
                 (fun prog =>
                    Bind (Pick (fun final_state => RunsTo env prog init_state final_state))
                         (fun final_state => Pick (fun x => final_state[ret_var >> SCA av x])))).
  intros.
  unfold refine.
  intros.
  inversion_by computes_to_inv.
  apply eq_ret_compute.

  apply (H _ _ I) in H1.
  eapply SCA_inj.
  eapply MapsTo_unique; eauto.
Qed.

Lemma compile_constant :
  forall (retvar: StringMap.key) av env,
  forall w1 (precond postcond: State av -> Prop),
    cond_respects_MapEq postcond ->
    (forall x state, precond state ->
                     postcond (StringMap.add retvar x state)) ->
    refine (Pick (fun prog1 => forall init_state final_state,
                                 precond init_state ->
                                 RunsTo env prog1 init_state final_state ->
                                 final_state[retvar >> SCA av w1]
                                 /\ postcond final_state))
           (ret (Assign retvar w1)).
Proof.
  unfold refine; intros; constructor; intros; inversion_by computes_to_inv; subst.
  inversion_clear H3.
  unfold eval in H1.
  unfold_coercions.
  apply Some_inj, SCA_inj in H1; subst.

  unfold cond_respects_MapEq in *.
  rewrite H5; clear H5.

  split.
  apply StringMap.add_1; reflexivity.
  intuition.
Qed.

Lemma unchanged :
  forall av (st: State av) arg val,
    StringMap.find arg st = Some (Facade.ADT val) ->
    StringMap.Equal
      st (add_remove_many (arg :: nil) (Facade.ADT val :: nil) (Some (Facade.ADT val) :: nil) st).
Proof.
  simpl; intros.
  red; intro arg'.
  destruct ( StringMap.E.eq_dec arg arg'); subst.

  rewrite StringMapFacts.add_eq_o; trivial.
  rewrite StringMapFacts.add_neq_o; trivial.
Qed.

Opaque add_remove_many.

Lemma weqb_false_iff :
  forall {sz} (w1 w2: @Word.word sz),
    Word.weqb w1 w2 = false <-> w1 <> w2.
Proof.
  split; try rewrite <- Word.weqb_true_iff in *; try congruence.
  destruct (Word.weqb w1 w2); intuition.
Qed.

Lemma a_neq_a_False :
  forall {A: Type} (a: A),
    a <> a <-> False.
Proof.
  intuition.
Qed.

Lemma a_eq_a_True :
  forall {A: Type} (a: A),
    a = a <-> True.
Proof.
  intuition.
Qed.

Lemma equiv_true :
  forall P : Prop, (True <-> P) <-> P.
  intuition.
Qed.

Lemma equiv_true' :
  forall {P Q: Prop},
    P -> (P <-> Q) -> Q.
Proof.
  intuition.
Qed.

Definition cond_indep {A} cond var :=
  forall (x: A) state, cond state -> cond (StringMap.add var x state). (* TODO Use more *)

Transparent add_remove_many.

(* TODO generalize this for is_empty as well *)
Lemma runsto_pop :
  forall hd tl (vseq thead: StringMap.key) env (st st': State FacadeADT) ppop,
    vseq <> thead ->
    st [vseq >> Facade.ADT (List (hd :: tl))] ->
    Word2Spec env ppop  = Some (Axiomatic List_pop) ->
    RunsTo env (Call thead ppop (vseq :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add thead (Facade.SCA _ hd) (StringMap.add vseq (Facade.ADT (List tl)) st)).
Proof.
  intros * vseq_thead vseq_init ppop_is_pop runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  Print List_pop.
  rewrite ppop_is_pop in *; autoinj;
  unfold List_pop in *; clear ppop_is_pop; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

Lemma add_noop :
  forall {A: Type} {k: StringMap.key} {v: A} {map},
    StringMap.find k map = Some v ->
    StringMap.Equal (StringMap.add k v map) map.
Proof.
  unfold StringMap.Equal; intros ** k';
  destruct (StringMap.E.eq_dec k k');
  subst;
  [ rewrite StringMapFacts.add_eq_o | rewrite StringMapFacts.add_neq_o ];
  auto.
Qed.

(* TODO: refactor to share code with runsto_pop *)
Lemma runsto_is_empty :
  forall seq (vseq tis_empty: StringMap.key) env (st st': State FacadeADT) pis_empty,
    vseq <> tis_empty ->
    st [vseq >> Facade.ADT (List seq)] ->
    Word2Spec env pis_empty  = Some (Axiomatic List_empty) ->
    RunsTo env (Call tis_empty pis_empty (vseq :: nil)) st st' ->
    exists ret,
      (ret <> SCAZero <-> seq = nil) /\
      StringMap.Equal st' (StringMap.add tis_empty ret st).
Proof.
  intros * vseq_tis_empty vseq_init pis_empty_is_is_empty runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite pis_empty_is_is_empty in *; autoinj;
  unfold List_pop in *; clear pis_empty_is_is_empty; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |-;
                                                unfold sel in *;
  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj; simpl in *.
  repeat autorewrite_equal.

  eexists; split; eauto.
  rewrite (add_noop vseq_init).
  reflexivity.
Qed.

Lemma runsto_copy :
  forall seq (vseq vcopy: StringMap.key) env (st st': State FacadeADT) pcopy,
    st [vseq >> Facade.ADT (List seq)] ->
    Word2Spec env pcopy  = Some (Axiomatic List_copy) ->
    RunsTo env (Call vcopy pcopy (vseq :: nil)) st st' ->
    StringMap.Equal st' (StringMap.add vcopy (Facade.ADT (List seq)) (StringMap.add vseq (Facade.ADT (List seq)) st)).
Proof.
  intros * vseq_seq pcopy_is_copy runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite pcopy_is_copy in *; autoinj;
  unfold List_copy in *; clear pcopy_is_copy; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |- ;
  unfold sel in *.

  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj.
Qed.

Lemma RunsToAssignKnownValue :
  forall {av env} {k1 k2: StringMap.key} {v} {st st': State av},
    st[k2 >> v] ->
    @RunsTo av env (Assign k1 k2) st st' ->
    StringMap.Equal st' (StringMap.add k1 v st).
Proof.
  intros * maps_to runs_to;
  inversion_clear' runs_to;
  simpl in *.
  autorewrite_equal.
  rewrite StringMapFacts.find_mapsto_iff in *.
  rewrite maps_to in *; autoinj.
Qed.

Opaque add_remove_many.

Definition LoopBodyOk acc_type (wrapper: acc_type -> Value FacadeADT) env f (sloop_body:Stmt) (vret vseq thead: StringMap.key) (precond: State _ -> Prop) :=
  cond_indep precond vret ->
  forall (acc: acc_type) (head: W) (seq: list W),
  forall (st1 st2: State FacadeADT),
    precond st1 /\
    (st1) [vret >> wrapper acc] /\
    (st1) [vseq >> Facade.ADT (List seq)] /\
    (st1) [thead >> Facade.SCA _ head] ->
    RunsTo env sloop_body st1 st2 ->
    (st2) [vret >> wrapper (f acc head)] /\
    (st2) [vseq >> Facade.ADT (List seq)] /\
    precond st2.

Lemma compile_fold_base :
  forall env,
  forall precond: State _ -> Prop,
  forall (vseq vret: StringMap.key),
  forall acc_type wrapper,
  forall (thead tis_empty: StringMap.key) ppop pempty f sloop_body,
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    cond_respects_MapEq precond ->
    cond_indep precond vret ->
    cond_indep precond tis_empty ->
    cond_indep precond thead ->
    cond_indep precond vseq ->
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    LoopBodyOk acc_type wrapper env f sloop_body vret vseq thead precond ->
    forall seq init,
      refine (Pick (fun prog => forall init_state final_state,
                                  init_state[vseq >> Facade.ADT (List seq)] /\
                                  init_state[vret >> wrapper init] /\
                                  precond init_state ->
                                  RunsTo env prog init_state final_state ->
                                  final_state[vret >> wrapper (List.fold_left f seq init)]
                                   /\ precond final_state))
             (ret ((Fold thead tis_empty vseq ppop pempty sloop_body))).
Proof.
  intros * vret_vseq vret_tis_empty thead_vret thead_vseq tis_empty_vseq precond_meaningful precond_indep_vret precond_indep_tis_empty precond_indep_thead precond_indep_vseq zero_to_empty one_to_pop loop_body_ok.

  induction seq;
  unfold refine; simpl;
  intros init  ** ;

  inversion_by computes_to_inv;
  constructor; intros;
  destruct H0 as (init_vseq & init_vinit);
  subst;
  inversion_clear' H1;

  [ apply (runsto_is_empty nil) in H2
  | apply (runsto_is_empty (a :: seq)) in H2 ];
  eauto;
  destruct H2 as [ret (ret_correct & st'_init_state)];
  unfold_coercions;

  (inversion_clear' H5;
   match goal with
     | [ H: is_true _ _ |- _] => rnm H test
     | [ H: is_false _ _ |- _] => rnm H test
   end;
   unfold
     is_true, is_false, eval_bool,
     eval, eval_binop_m, eval_binop,
     IL.wneb, IL.evalTest, IL.weqb in test;
   autorewrite_equal;
   (rewrite StringMapFacts.add_eq_o in * by trivial);
   (destruct ret; [ | discriminate]); (* ret is SCA *)
   unfold SCAZero, SCAOne in *;
     autoinj';
   repeat match goal with
            | [ H: context[(if ?a then _ else _) = _] |- _ ] => let H' := fresh in destruct a eqn:H'; try discriminate
          end;
   [ clear n H test | clear e H test ];
   match goal with
     | [ H: Word.weqb _ _ = _ |- _ ] =>
       rewrite ?weqb_false_iff, ?Word.weqb_true_iff in H
   end;
   subst).

  (* 4 cases here: *)
  (* 1 & 2 are for the base case; 3 & 4, for the induction case *)

  (* 1 *)
  rewrite a_neq_a_False, a_eq_a_True in ret_correct.
  tauto.

  (* 4 *)
  Focus 3.
  destruct ret_correct as (ret_correct, _).
  specialize (ret_correct H0). (* TODO: Let specialize pick the right hypothesis? *)
  congruence.

  (* 2: interesting part of the base case *)
  unfold cond_respects_MapEq in *.
  rewrite st'_init_state.
  split;
    [ map_iff_solve intuition | apply precond_indep_tis_empty];
  intuition.

  (* 4: interesting part of the induction *)
  specialize (IHseq (f init a) (Fold thead tis_empty vseq ppop pempty sloop_body)).
  specialize (IHseq (eq_ret_compute _ _ _ (eq_refl))).
  inversion_by computes_to_inv.
  rnm H1 IHseq_vret.
  rnm H3 IHseq_precond.

  unfold cond_respects_MapEq, cond_indep in *.

  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  inversion_clear' H2. (* Start chomping at loop body *)

  apply (runsto_pop a seq) in H4; [
    | solve [eauto]
    | autorewrite_equal;
      map_iff_solve intuition
    | solve [eauto] ].

  (* Now the loop body *)

  (* Just because it feels nice: specialize the induction hypotheses *)
  inversion_clear' H8.

  pose proof (RunsToSeq H9 H6) as new_loop.
  clear H9 H6.

  unfold Fold in IHseq_vret.
  specialize (fun pre => IHseq_vret _ _ pre new_loop).
  specialize (fun pre => IHseq_precond _ _ pre new_loop).
  (* yay *)

  unfold LoopBodyOk in loop_body_ok.

  specialize (loop_body_ok precond_indep_vret init a seq st'1 st'2).
  rewrite st'_init_state in H4. (* Thus st1' = ... *)

  (* TODO find prettier way to do these asserts *)

  assert ((st'1) [vret >> wrapper init])
    as h1 by (rewrite H4; map_iff_solve intuition).

  assert ((st'1) [vseq >> Facade.ADT (List seq)])
    as h2 by (rewrite H4; map_iff_solve intuition).

  assert ((st'1) [thead >> Facade.SCA _ a])
    as h3 by (rewrite H4; map_iff_solve intuition).

  assert (precond st'1) as h4 by (rewrite H4; intuition).

  specialize (loop_body_ok (conj h4 (conj h1 (conj h2 h3))) H3); clear h1 h2 h3 h4.

  destruct loop_body_ok as (loop_body_ok1 & loop_body_ok2 & ?).

  intuition.
Qed.

Lemma compile_fold_no_pick :
  forall {env},
  forall {precond postcond: State _ -> Prop},
  forall (vinit vseq: StringMap.key) {vret},
  forall acc_type wrapper,
  forall thead tis_empty ppop pempty f sloop_body,
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    cond_respects_MapEq postcond ->
    cond_indep postcond vret ->
    cond_indep postcond tis_empty ->
    cond_indep postcond thead ->
    cond_indep postcond vseq ->
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    LoopBodyOk acc_type wrapper env f sloop_body vret vseq thead postcond ->
    forall (seq: list W) (init: acc_type),
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                (final_state[vret >> wrapper (List.fold_left f seq init)]
                                 /\ postcond final_state)))
           (Bind (Pick (fun pinit => forall init_state inter_state,
                                       precond init_state ->
                                       RunsTo env pinit init_state inter_state ->
                                       (inter_state[vinit >> wrapper init] /\ precond inter_state)))
                 (fun pinit =>
                    Bind
                      (Pick (fun pseq =>
                               forall inter_state final_state,
                                 precond inter_state /\ inter_state[vinit >> wrapper init] ->
                                 RunsTo env pseq inter_state final_state ->
                                 (final_state[vseq >> Facade.ADT (List seq)]
                                  /\ final_state[vinit >> wrapper init]
                                  /\ postcond final_state)))
                      (fun pseq => ret (pinit;
                                        pseq;
                                        Assign vret vinit;
                                        Fold thead tis_empty vseq ppop pempty sloop_body)%facade))).
Proof.
  unfold refine; intros * vret_vseq vret_tis_empty thead_vret thead_vseq tis_empty_vseq postcond_meaningful postcond_indep_vret postcond_indep_tis_empty postcond_indep_thead postcond_indep_vseq zero_to_empty one_to_pop loop_body_ok * **.

  inversion_by computes_to_inv.
  rnm x pinit.
  rnm x0 pseq.
  rnm H progseq_returns_seq.
  rnm H3 proginit_returns_init.
  rnm H5 proginit_consistent.
  rnm H1 progseq_consistent.
  rnm H4 progseq_ensures_postcond.
  constructor; intros.

  rnm H init_state_consistent.

  subst.
  inversion H0; subst; clear H0.
  inversion H5; subst; clear H5.
  inversion H6; subst; clear H6.

  autospecialize.
  clear H2. (* RunsTo relative to pseq *)
  clear H1. (* RunsTo relative to pinit *)

  apply (RunsToAssignKnownValue progseq_consistent) in H3.

  unfold cond_respects_MapEq in *.

  assert ((st'1) [vseq >> Facade.ADT (List seq)] /\ (st'1) [vret >> wrapper init] /\ postcond st'1)
    as lemma_precond by (rewrite H3; map_iff_solve intuition).

  pose proof (compile_fold_base env postcond vseq vret acc_type wrapper thead tis_empty ppop pempty f sloop_body) as lemma.
  intuition; (* specializes compile_fold_base *)

  match goal with
    | [ H0: forall _ _, refine _ _ |- _ ] =>
      specialize (H0 seq init);
        unfold refine in H0;

        specialize (H0 (Fold thead tis_empty vseq ppop pempty sloop_body));
        specialize (H0 (eq_ret_compute _ _ _ (eq_refl)))
  end;

  inversion_by computes_to_inv;

  unfold State in *;

  repeat match goal with
           | [ H0: forall (a b: StringMap.t (Value FacadeADT)), _ |- _ ] =>
             specialize (H0 st'1 final_state) (* Specialize the conditions arising from inversion *)
         end;

  intuition.
Qed.

Lemma PickComputes_inv: forall {A} (x: A) P,
                          computes_to (Pick (fun x => P x)) x -> P x.
Proof.
  intros; inversion_by computes_to_inv; assumption.
Qed.

Print LoopBodyOk.

Lemma compile_fold :
  forall {env},
  forall {precond postcond: State _ -> Prop},
  forall vinit vseq {vret},
  forall acc_type wrapper,
  forall thead tis_empty ppop pempty f,
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    cond_respects_MapEq postcond ->
    cond_indep postcond vret ->
    cond_indep postcond tis_empty ->
    cond_indep postcond thead ->
    cond_indep postcond vseq ->
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    forall (seq: list W) (init: acc_type),
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                (final_state[vret >> wrapper (List.fold_left f seq init)]
                                 /\ postcond final_state)))
           (Bind (Pick (fun loop_body => LoopBodyOk acc_type wrapper env f loop_body vret vseq thead postcond))
                 (fun sloop_body =>
                    Bind
                      (Pick (fun pinit => forall init_state inter_state,
                                             precond init_state ->
                                             RunsTo env pinit init_state inter_state ->
                                             (inter_state[vinit >> wrapper init] /\ precond inter_state)))
                      (fun pinit =>
                         Bind
                           (Pick (fun pseq =>
                                    forall inter_state final_state,
                                      precond inter_state /\ inter_state[vinit >> wrapper init] ->
                                      RunsTo env pseq inter_state final_state ->
                                      (final_state[vseq >> Facade.ADT (List seq)]
                                       /\ final_state[vinit >> wrapper init]
                                       /\ postcond final_state)))
                           (fun pseq => ret (pinit;
                                             pseq;
                                             Assign vret vinit;
                                             Fold thead tis_empty vseq ppop pempty sloop_body)%facade)))).
Proof.
  unfold refine; intros * vret_vseq vret_tis_empty thead_vret thead_vseq tis_empty_vseq postcond_meaningful postcond_indep_vret postcond_indep_tis_empty postcond_indep_thead postcond_indep_vseq zero_to_empty one_to_pop loop_body_ok * ** .

  apply computes_to_inv in H.
  destruct H as [loop_body (loop_valid & H)].

  apply PickComputes_inv in loop_valid.

  pose proof (@compile_fold_no_pick env precond postcond vinit vseq vret acc_type wrapper thead tis_empty ppop pempty f loop_body) as lemma.
  unfold refine in *.
  intuition.
Qed.

Definition compile_fold_sca
           {env} {precond postcond: State _ -> Prop}
           vinit vseq {vret} :=
  @compile_fold env precond postcond vinit vseq vret W (@Facade.SCA _).

Definition compile_fold_adt (* TODO: Rename *)
           {env} {precond postcond: State _ -> Prop}
           vinit vseq {vret} :=
  @compile_fold env precond postcond vinit vseq vret (list W) (fun x => Facade.ADT (List x)).

Lemma copy_word :
  forall {av env},
  forall k1 {k2} w (precond postcond: State av -> Prop),
    cond_respects_MapEq postcond ->
    (forall state, precond state -> state[k1 >> Facade.SCA _ w]) ->
    (forall x state, precond state -> postcond (StringMap.add k2 x state)) ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                final_state[k2 >> Facade.SCA _ w] /\
                                postcond final_state))
           (ret (Assign k2 k1)).
Proof.
  unfold refine; intros; constructor; intros.
  inversion_by computes_to_inv; subst.
  unfold cond_respects_MapEq in *.

  inversion_clear' H4.
  specialize (H0 _ H3).
  autorewrite_equal; simpl in *.
  StringMapFacts.map_iff.
  rewrite StringMapFacts.find_mapsto_iff in *.
  rewrite H0 in *. autoinj.
Qed.

Lemma no_op :
  forall {av env},
  forall (precond postcond: State av -> Prop),
    (forall state, precond state -> postcond state) ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                postcond final_state))
           (ret Skip).
Proof.
  unfold refine; intros; constructor; intros.
  inversion_by computes_to_inv; subst; inversion_clear' H2.
  intuition.
Qed.

Lemma pull_forall :
  forall {A B C} {av env} P b
         (precond': State av -> Prop)
         (precond postcond: A -> B -> C -> State av -> Prop),
  (forall (x1: A) (x2: B) (x3: C),
     P precond' ->
     refine (Pick (fun prog => forall (st1 st2: State av),
                                 precond' st1 /\ precond x1 x2 x3 st1 ->
                                 RunsTo env prog st1 st2 ->
                                 postcond x1 x2 x3 st2)) b) ->
  refine (Pick (fun prog => P precond' ->
                            forall x1 x2 x3,
                            forall (st1 st2: State av),
                              precond' st1 /\ precond x1 x2 x3 st1 ->
                              RunsTo env prog st1 st2 ->
                              postcond x1 x2 x3 st2)) b.
Proof.
  unfold refine; intros; econstructor; intros.
  generalize (H x1 x2 x3 X _ H0); intros.
  inversion_by computes_to_inv.
  specialize (H3 st1 st2 (conj H4 H5)).
  intuition.
Qed.

Lemma start_compiling_with_precondition ret_var : (* TODO: Supersedes start_compiling *)
  forall {av env init_state precond} ret_type wrapper (v: ret_type),
    (forall x y, wrapper x = wrapper y -> x = y) ->
    precond init_state ->
    refine (ret v)
           (Bind (Pick (fun prog =>
                          forall init_state final_state,
                            precond init_state ->
                            @RunsTo av env prog init_state final_state ->
                            final_state[ret_var >> wrapper v]
                            /\ (fun x => True) final_state))
                 (fun prog =>
                    Bind (Pick (fun final_state => RunsTo env prog init_state final_state))
                         (fun final_state => Pick (fun x => final_state[ret_var >> wrapper x])))).
  intros * wrapper_inj ** .
  unfold refine.
  intros.
  inversion_by computes_to_inv.
  apply eq_ret_compute.

  apply (H _ _ X) in H1.
  apply wrapper_inj.
  eapply MapsTo_unique; eauto.
Qed.

Lemma compile_new :
  forall {env} pnew vret,
  forall precond postcond,
    Word2Spec env pnew = Some (Axiomatic List_new) ->
    cond_respects_MapEq postcond ->
    (forall state x, precond state -> postcond (StringMap.add vret x state)) ->
    refine (Pick (fun prog =>
                    forall init_state final_state : State FacadeADT,
                      precond init_state ->
                      RunsTo env prog init_state final_state ->
                      final_state[vret >> Facade.ADT (List nil)] /\
                      postcond final_state))
           (ret (Call vret pnew nil)).
Proof.
  unfold refine, List_new, cond_respects_MapEq; intros; constructor; intros.
  inversion_by computes_to_inv; subst;
  inversion_clear' H3; simpl in *; [ | congruence ].

  autoinj; subst;
  eq_transitive; autoinj; subst; simpl in *;
  match goal with
    | [ H: 0 = List.length _ |- _ ] => rewrite length_0 in H
  end; subst;
  autorewrite_equal; map_iff_solve intuition.
Qed.

Lemma compile_copy :
  forall {env} pcopy vfrom vto val,
  forall (precond postcond: _ -> Prop),
    Word2Spec env pcopy = Some (Axiomatic List_copy) ->
    cond_respects_MapEq postcond ->
    (forall state, precond state ->
                   postcond (StringMap.add vto (Facade.ADT (List val))
                                           (StringMap.add vfrom (Facade.ADT (List val)) state))) ->
    (forall state, precond state -> state[vfrom >> Facade.ADT (List val)]) ->
    refine (Pick (fun prog =>
                    forall init_state final_state : State FacadeADT,
                      precond init_state ->
                      RunsTo env prog init_state final_state ->
                      final_state[vto >> Facade.ADT (List val)] /\
                      postcond final_state))
           (ret (Call vto pcopy (vfrom :: nil))).
Proof.
  unfold refine, List_new, cond_respects_MapEq; intros; constructor; intros.
  inversion_by computes_to_inv; subst.

  eapply runsto_copy in H5; eauto.
  autorewrite_equal; map_iff_solve intuition.
Qed.

Transparent add_remove_many.
Lemma compile_cons :
  forall pcons tdummy thead ttail,
  forall env,
  forall (precond postcond: State _ -> Prop),
  forall head tail,
    tdummy <> ttail ->
    Word2Spec env pcons = Some (Axiomatic List_push) ->
    cond_respects_MapEq postcond ->
    cond_indep postcond ttail ->
    cond_indep postcond tdummy ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                final_state[ttail >> Facade.ADT (List (head :: tail))]
                                /\ postcond final_state))
           (Bind (Pick (fun phead => forall init_state inter_state,
                                       precond init_state ->
                                       RunsTo env phead init_state inter_state ->
                                       inter_state[thead >> Facade.SCA _ head] /\
                                       precond inter_state))
                 (fun phead =>
                    Bind
                      (Pick (fun ptail =>
                               forall inter_state final_state,
                                 precond inter_state /\
                                 inter_state[thead >> Facade.SCA _ head] ->
                                 RunsTo env ptail inter_state final_state ->
                                 final_state[ttail >> Facade.ADT (List tail)] /\
                                 final_state[thead >> Facade.SCA _ head] /\
                                 postcond final_state))
                      (fun ptail => ret (Seq phead
                                             (Seq ptail
                                                  (Call tdummy pcons (ttail :: thead :: nil))))))).
Proof. (* TODO: Prove runsto_cons. *)
  unfold refine, List_push, cond_respects_MapEq; intros; constructor; intros.
  inversion_by computes_to_inv; subst.
  inversion_clear' H4.
  inversion_clear' H14.
  inversion_clear' H15; simpl in *; [ | congruence ].
  autospecialize.

  autoinj; subst;
  eq_transitive; autoinj; subst; simpl in *; autodestruct; subst.

  unfold sel in *.

  destruct output as [ | h [ | h' tl ] ]; simpl in *; try congruence.

  autoinj.

  rewrite StringMapFacts.find_mapsto_iff in *;
    repeat (subst_find; simpl in *);
    rewrite <- StringMapFacts.find_mapsto_iff in *.

  repeat progress (autoinj'; autoinj).

  autorewrite_equal; map_iff_solve intuition.
Qed.

Definition empty_env ADTValue : Env ADTValue := {| Label2Word := fun _ => None; Word2Spec := fun _ => None |}.

Definition empty_state ADTValue : State ADTValue := StringMap.empty (Value ADTValue).

Definition basic_env := {| Label2Word := fun _ => None;
                           Word2Spec := fun w =>
                                          if Word.weqb w 0 then
                                            Some (Axiomatic List_empty)
                                          else if Word.weqb w 1 then
                                            Some (Axiomatic List_pop)
                                          else if Word.weqb w 2 then
                                            Some (Axiomatic List_new)
                                          else if (Word.weqb w 3) then
                                            Some (Axiomatic List_push)
                                          else if (Word.weqb w 4) then
                                            Some (Axiomatic List_copy)
                                          else
                                            None |}.

Definition start_compiling := fun ret_var av => @start_compiling' ret_var av (empty_env av) (empty_state av).

Definition start_compiling_sca :=
  fun ret_var => @start_compiling' ret_var _ (basic_env) (empty_state _).

Definition start_compiling_sca_with_precondition :=
  fun ret_var {init_state precond} precond_proof v => @start_compiling_with_precondition ret_var _ (basic_env) init_state precond W (Facade.SCA FacadeADT) v (@SCA_inj FacadeADT) precond_proof.

Definition start_compiling_adt_with_precondition :=
  fun ret_var {init_state precond} precond_proof v => @start_compiling_with_precondition ret_var _ (basic_env) init_state precond (list W) (fun x => Facade.ADT (List x)) v (List_inj) precond_proof.

Ltac spam :=
  solve [ unfold cond_respects_MapEq, Proper, respectful;
          first [
              solve [map_iff_solve ltac:(
                       intros; try match goal with
                                       [ H: StringMap.Equal _ _ |- _ ] =>
                                       rewrite H in *
                                   end;
                       intuition)]
            | intuition;
              first [
                  apply StringMap.add_2;
                  congruence
                | idtac ] ] ].

Tactic Notation "cleanup" :=
  first [ simplify with monad laws | spam ].

Tactic Notation "cleanup_adt" :=
  unfold cond_indep, LoopBodyOk, Fold; intros;
  try first [ simplify with monad laws
        | spam
        | discriminate
        | match goal with
            | [ |- Word2Spec ?env _ = _ ] => unfold env; simpl; intuition
          end
        ].

Goal forall w1 w2: W,
     exists x,
       refine (ret (if Word.weqb w1 w2 then (IL.natToW 3) else (IL.natToW 4))) x.
Proof.
  eexists.

  setoid_rewrite (start_compiling "$ret" (list W)).

  setoid_rewrite (compile_if "$cond"); cleanup.
  setoid_rewrite (compile_test IL.Eq "$cond" "$w1" "$w2"); cleanup.

  setoid_rewrite (compile_constant "$w1"); cleanup.
  setoid_rewrite (compile_constant "$w2"); cleanup.
  rewrite (compile_constant "$ret"); cleanup.
  rewrite (compile_constant "$ret"); cleanup.

  reflexivity.
Qed.

(*
setoid_rewrite (compile_constant "$ret" _ _ _ (fun s => Word.weqb w1 w2 = true /\ True /\ _ s)); cleanup.
setoid_rewrite (compile_constant "$ret" _ _ _ (fun s => Word.weqb w1 w2 = false /\ True /\ _ s)); cleanup.
*)

Goal exists x,
       refine (ret (Word.wmult
                      (Word.wplus  3 4)
                      (Word.wminus 5 6))) x.
Proof.
  eexists.

  setoid_rewrite (start_compiling "$ret" (list W)).
  setoid_rewrite (compile_binop IL.Times "$ret" "$t1" "$t2"); cleanup.

  setoid_rewrite (compile_binop IL.Plus  "$t1" "$t11" "$t12"); cleanup.
  setoid_rewrite (compile_constant "$t11"); cleanup.
  setoid_rewrite (compile_constant "$t12"); cleanup.

  setoid_rewrite (compile_binop IL.Minus "$t2" "$t21" "$t22"); cleanup.
  setoid_rewrite (compile_constant "$t21"); cleanup.
  setoid_rewrite (compile_constant "$t22"); cleanup.

  reflexivity.
Qed.

Definition ProgEquiv {av} p1 p2 :=
  forall env st1 st2,
    (@RunsTo av env p1 st1 st2 <-> RunsTo env p2 st1 st2).

Require Import Setoid.

Add Parametric Relation {av} : (Stmt) (@ProgEquiv av)
    reflexivity proved by _
    symmetry proved by _
    transitivity proved by _
      as prog_equiv.
Proof.
  firstorder.
  firstorder.
  unfold Transitive, ProgEquiv; intros; etransitivity; eauto.
Qed.

Show.

(* Uh? *)
unfold Transitive, ProgEquiv; intros; etransitivity; eauto.

Add Parametric Morphism {av: Type} :
  (@RunsTo av)
    with signature (eq ==> @ProgEquiv av ==> eq ==> eq ==> iff)
      as runsto_morphism.
Proof.
  unfold ProgEquiv; intros * prog_equiv ** ; apply prog_equiv; assumption.
Qed.

Add Parametric Morphism {av} :
  (Seq)
    with signature (@ProgEquiv av ==> @ProgEquiv av ==> @ProgEquiv av)
      as seq_morphism.
Proof.
  unfold ProgEquiv; intros.

  split; intro runs_to; inversion_clear' runs_to; econstructor; [
    rewrite <- H | rewrite <- H0 |
    rewrite -> H | rewrite -> H0 ];
  eauto; reflexivity.
Qed.

Lemma while_morph {av env} :
  forall while_p1,
  forall (st1 st2: State av),
    RunsTo env (while_p1) st1 st2 ->
    forall p1 p2 test,
      while_p1 = Facade.While test p1 ->
      @ProgEquiv av p1 p2 ->
      RunsTo env (Facade.While test p2) st1 st2.
Proof.
  unfold ProgEquiv; induction 1; intros ** equiv; subst; try discriminate; autoinj.

  econstructor; eauto; rewrite <- equiv; assumption.
  constructor; trivial.
Qed.

Add Parametric Morphism {av} :
  (Facade.While)
    with signature (eq ==> @ProgEquiv av ==> @ProgEquiv av)
      as while_morphism.
Proof.
  split; intros; eapply while_morph; eauto; symmetry; assumption.
Qed.

Add Parametric Morphism {av} :
  (Facade.If)
    with signature (eq ==> @ProgEquiv av ==> @ProgEquiv av ==> @ProgEquiv av)
      as if_morphism.
Proof.
  unfold ProgEquiv; intros * true_equiv * false_equiv ** .
  split; intro runs_to; inversion_clear' runs_to;
  [ constructor 3 | constructor 4 | constructor 3 | constructor 4];
  rewrite ?true_equiv, ?false_equiv in *; try assumption.
Qed.

Lemma Skip_Seq av :
  forall prog,
    @ProgEquiv av (Seq Skip prog) prog.
Proof.
  unfold ProgEquiv; split; intros.
  inversion_clear' H; inversion_clear' H2; eauto.
  repeat (econstructor; eauto).
Qed.

Lemma Seq_Skip av :
  forall prog,
    @ProgEquiv av (Seq prog Skip) prog.
Proof.
  unfold ProgEquiv; split; intros.
  inversion_clear' H; inversion_clear' H5; eauto.
  repeat (econstructor; eauto).
Qed.

Goal forall seq: list W,
     forall state,
       state["$list" >> Facade.ADT (List seq)] ->
       exists x,
         refine (ret (fold_left (fun (sum item: W) => Word.wplus item sum) seq 0)) x.
Proof.
  intros seq state state_precond; eexists.

  setoid_rewrite (start_compiling_sca_with_precondition "$ret" state_precond).
  setoid_rewrite (compile_fold_sca "$init" "$seq" "$head" "$is_empty" 1 0); cleanup_adt.
  setoid_rewrite (pull_forall (fun cond => cond_indep cond "$ret")); cleanup_adt.

  Focus 2.
  setoid_rewrite (compile_binop IL.Plus "$ret" "$head" "$ret"); cleanup_adt.
  rewrite no_op; try cleanup_adt.
  rewrite no_op; try cleanup_adt.
  reflexivity.

  setoid_rewrite compile_constant; cleanup_adt.
  setoid_rewrite (compile_copy 4 "$list"); cleanup_adt.

  repeat setoid_rewrite Skip_Seq.

  reflexivity.
Qed.

Goal forall seq: list W,
     forall state,
       state["$list" >> Facade.ADT (List seq)] ->
       exists x,
         refine
           (ret (fold_left
                   (fun (acc: list W) (item: W) =>
                      if IL.wltb 0 item then
                        Word.wmult item 2 :: acc
                      else
                        acc)
                   seq nil)) x.
Proof.
  intros * state_precond; eexists.

  (* Start compiling, copying the state_precond precondition to the resulting
     program's preconditions. Result is stored into [$ret] *)
  rewrite (start_compiling_adt_with_precondition "$ret" state_precond).

  (* Compile the fold, reading the initial value of the accumulator from
     [$init], the input data from [$seq], and storing temporary variables in
     [$head] and [$is_empty]. *)
  rewrite (compile_fold_adt "$init" "$list" "$head" "$is_empty" 1 0); cleanup_adt.

  (* Extract the quantifiers, and move the loop body to a second goal *)
  rewrite (pull_forall (fun cond => cond_indep cond "$ret")); cleanup_adt.

  (* The output list is allocated by calling List_new, whose axiomatic
     specification is stored at address 2 *)
  setoid_rewrite (compile_new 2); cleanup_adt.

  (* The input list is already stored in [$list] *)
  rewrite no_op; cleanup_adt.

  (* We're now ready to proceed with the loop's body! *)

  Focus 2.

  (* Compile the if test *)
  rewrite (compile_if "$cond" (fun x => Facade.ADT (List x))); cleanup_adt.

  (* Extract the comparison to use Facade's comparison operators, storing the
     operands in [$0] and [$head], and the result of the comparison in
     [$cond] *)
  rewrite (compile_test IL.Lt "$cond" "$0" "$head"); cleanup_adt.

  (* The two operands of [<] are easily refined *)
  rewrite (compile_constant); cleanup_adt.
  rewrite (no_op); cleanup_adt.

  (* Now for the true part of the if: append the value to the list *)

  (* Delegate the cons-ing to an ADT operation specified axiomatically; [3]
     points to [List_push] in the current environment; we pick [$new_head] as
     the place to temporarily store the new head *)
  rewrite (compile_cons 3 "$dummy" "$new_head"); cleanup_adt.

  (* The head needs to be multiplied by two before being pushed into the output
     list. *)
  setoid_rewrite (compile_binop IL.Times _ "$new_head" "$2"); cleanup_adt.
  rewrite (copy_word "$head"); cleanup_adt.
  rewrite (compile_constant); cleanup_adt.

  (* And the tail is readily available *)
  rewrite no_op; cleanup_adt.

  (* The false part is a lot simpler *)
  rewrite no_op; cleanup_adt.

  (* Ok, this loop body looks good :) *)
  reflexivity.

  repeat setoid_rewrite Skip_Seq.

  (* Yay, a program! *)
  reflexivity.
Qed.

Definition max seq :=
  fold_left
    (fun (max: W) (item: W) =>
       if (IL.wltb max item) then
         item
       else
         max) seq 0.

Definition min seq :=
  fold_left
    (fun (min: W) (item: W) =>
       if (IL.wltb item min) then
         item
       else
         min) seq 0.

Goal forall seq: list W,
     forall state,
       state["$list" >> Facade.ADT (List seq)] ->
       exists x,
         refine
           (ret (Word.wminus (max seq) (min seq))) x.
Proof.
  intros * state_precond; eexists.

  rewrite (start_compiling_sca_with_precondition "$ret" state_precond).
  unfold min, max;
    setoid_rewrite (compile_binop IL.Minus "$ret" "$max" "$min"); cleanup_adt.

  rewrite (compile_fold_sca "$init" "$seq" "$head" "$is_empty" 1 0); cleanup_adt.
  rewrite (pull_forall (fun cond => cond_indep cond "$max")); cleanup_adt.
  rewrite (compile_constant); cleanup_adt.
  rewrite (compile_copy 4 "$list"); cleanup_adt.

  rewrite (compile_fold_sca "$init" "$seq" "$head" "$is_empty" 1 0); cleanup_adt.
  rewrite (pull_forall (fun cond => cond_indep cond "$min")); cleanup_adt.
  rewrite (compile_constant); cleanup_adt.
  rewrite (compile_copy 4 "$list"); cleanup_adt.

  Focus 2.

  rewrite (compile_if "$cond").
  rewrite (compile_test IL.Lt "$cond" "$head" "$min"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (copy_word "$head"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  reflexivity.

  Focus 2.

  rewrite (compile_if "$cond").
  rewrite (compile_test IL.Lt "$cond" "$max" "$head"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  rewrite (copy_word "$head"); cleanup_adt.
  rewrite (no_op); cleanup_adt.
  reflexivity.

  repeat setoid_rewrite Skip_Seq.
  reflexivity.
Qed.

(* TODO: Multiple Facade ADTs vs single cito ADT *)

(* TODO: Sigma types *)

(* TODO: Coercions to get rid of explicit "'" operator. Look at constants being used *)

(* TODO: Use function names *)

  (*
  (* TODO: Cleanup should remove redundant clauses from expressions. Otherwise copying $ret to $ret doesn't work. *)
setoid_rewrite (copy_variable "$ret" "$ret"); cleanup_adt. (* TODO Replace by no-op *)
setoid_rewrite (copy_variable "$head" "$head"); cleanup_adt. (* TODO Replace by no-op *)
reflexivity.
   *)

(* TODO: Three different approaches:
         * <> precond and postcond, but forall x, precond x -> postcond (add blah x);
         * Same pre/post cond, with extra conditions (see compile_fold et al.)
         * <> precond and postcond, and postcond indep of modified var (see compile_cons) *)
(* TODO: Post-conditions should include the beginning state, too *)

(* TODO: Replace all instances of
       precond st1 /\ blah st1 -> RunsTo -> postcond st2 /\ bluh st2
   by
       precond st1 -> RunsTo -> postcond st2
   with additional constraints `precond st1 -> blah st1` and `postcond st2 -> bluh st2` *)

(* TODO: Tweak autorewrite_equal to make it faster *)
