Ltac rnm a b :=
  rename a into b.

Require Import Cito.facade.Facade.
Require Import AutoDB.

Unset Implicit Arguments.

Import StringMap.StringMap.

Lemma Some_inj : forall A (x y: A),
                   Some x = Some y -> x = y.
  intros ** H; injection H; trivial.
Qed.

Lemma MapsTo_unique :
  forall {A} map key (v1 v2: A),
    MapsTo key v1 map ->  
    MapsTo key v2 map ->  
    v1 = v2.
Proof.
  intros.
  rewrite StringMapFacts.find_mapsto_iff in *.
  apply Some_inj; rewrite <- H, <- H0; trivial.
Qed.

Lemma SCA_inj :
  forall av v v',
    SCA av v = SCA av v' -> v = v'.
Proof.
  intros ** H; injection H; trivial.
Qed.

Definition cond_respects_MapEq {elt} :=
  Proper (StringMapFacts.M.Equal (elt := elt) ==> iff).

Definition WZero := (Word.wzero 32).
Definition WOne  := (Word.wone  32).

Definition BoolToW (b: bool) := if b then WOne else WZero.

Definition WToBool (w: @Word.word 32) := negb (Word.weqb w WZero).

Lemma BoolToW_invert : forall b, WToBool (BoolToW b) = b.
Proof.
  destruct b; intuition.
Qed.

Definition empty_env ADTValue : Env ADTValue := {| Label2Word := fun _ => None; Word2Spec := fun _ => None |}.

Definition empty_state ADTValue : State ADTValue := StringMapFacts.M.empty (Value ADTValue).

Lemma eval_binop_inv :
  forall (test: bool),
    IL.wneb (eval_binop (inr IL.Eq) (if test then WOne else WZero) WZero)
            (Word.natToWord 32 0) = negb test.
Proof.
  intros; destruct test; simpl; reflexivity.
Qed.
Opaque WOne WZero.

Ltac autospecialize :=
  repeat match goal with 
           | [ H: forall a b, ?x a -> ?y a b -> _, H': ?x _, H'': ?y _ _ |- _ ] => specialize (H _ _ H' H'') 
           | [ H: forall a b, ?x a /\ ?x' a -> ?y a b -> _, H'1: ?x _, H'2: ?x' _, H'': ?y _ _ |- _ ] => specialize (H _ _ (conj H'1 H'2) H'')
         end.

Lemma compile_if :
  forall { av env } testvar retvar (test: bool) (precond postcond: _ -> Prop) truecase falsecase,
  refine (Pick (fun prog => forall init_state final_state,
                              precond init_state ->
                              RunsTo env prog init_state final_state ->
                              (MapsTo retvar (SCA av (if test then truecase else falsecase)) final_state 
                               /\ postcond final_state)))
         (Bind (Pick (fun progtest => forall init_state inter_state,
                                        precond init_state ->
                                        RunsTo env progtest init_state inter_state ->
                                        (MapsTo testvar (SCA av (BoolToW test)) inter_state /\
                                         precond inter_state)))
               (fun ptest => 
                  (Bind (Pick (fun prog1 => forall inter_state final_state,
                                              (test = true /\ 
                                               precond inter_state /\ 
                                               MapsTo testvar (SCA av (BoolToW test)) inter_state) ->
                                              RunsTo env prog1 inter_state final_state ->
                                              (MapsTo retvar (SCA av truecase) final_state /\
                                               postcond final_state)))
                        (fun p1 => 
                           Bind 
                             (Pick (fun prog2 => 
                                      forall inter_state final_state,
                                        (test = false /\ 
                                         precond inter_state /\ 
                                         MapsTo testvar (SCA av (BoolToW test)) inter_state) ->
                                        RunsTo env prog2 inter_state final_state ->
                                        (MapsTo retvar (SCA av falsecase) final_state /\
                                         postcond final_state)))
                             (fun p2 => ret (Seq ptest
                                                 (Facade.If (SyntaxExpr.TestE IL.Eq
                                                                              (SyntaxExpr.Var testvar) 
                                                                              (SyntaxExpr.Const WZero))
                                                            (p2)
                                                            (p1)))))))).                
Proof.
  unfold refine. 
  intros av env testvar retvar test precond postcond truecase falsecase ** .
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
    (destruct (find (elt:=Value av) testvar inter_state) as [ v | ] eqn:testvar_correct; try congruence);
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
    (forall x state, postcond state -> postcond (add retvar x state)) ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                (MapsTo retvar (SCA av ((IL.evalBinop op) w1 w2)) final_state 
                                 /\ postcond final_state)))
           (Bind (Pick (fun prog1 => forall init_state inter_state,
                                       precond init_state ->
                                       RunsTo env prog1 init_state inter_state ->
                                       (MapsTo temp1 (SCA av w1) inter_state
                                        /\ precond inter_state)))
                 (fun p1 => 
                    Bind 
                      (Pick (fun prog2 => 
                               forall inter_state final_state,
                                 precond inter_state /\ MapsTo temp1 (SCA av w1) inter_state ->
                                 RunsTo env prog2 inter_state final_state ->
                                 (MapsTo temp2 (SCA av w2) final_state 
                                  /\ MapsTo temp1 (SCA av w1) final_state
                                  /\ postcond final_state)))
                      (fun p2 => ret (Seq p1 
                                          (Seq p2 
                                               (Assign retvar 
                                                       (SyntaxExpr.Binop 
                                                          op
                                                          (SyntaxExpr.Var temp1) 
                                                          (SyntaxExpr.Var temp2)))))))).
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
  rewrite H0; clear H0.

  unfold eval in H; simpl in H;
  unfold eval_binop_m in H; simpl in H.

  set (find temp1 _) as r1 in H.
  set (find temp2 _) as r2 in H.
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

  apply StringMapFacts.M.add_1; reflexivity.
  apply postcond_indep_retvar; eauto.
Qed.

Lemma compile_test : (* Exactly the same proof as compile_binop *)
  forall op,
  forall retvar temp1 temp2,
  forall av env,
  forall (precond postcond: State _ -> Prop),
  forall w1 w2,
    cond_respects_MapEq postcond ->
    (forall x state, postcond state -> postcond (add retvar x state)) ->
    refine (Pick (fun prog => forall init_state final_state,
                                precond init_state ->
                                RunsTo env prog init_state final_state ->
                                (MapsTo retvar (SCA av (BoolToW ((IL.evalTest op) w1 w2))) final_state 
                                 /\ postcond final_state)))
           (Bind (Pick (fun prog1 => forall init_state inter_state,
                                       precond init_state ->
                                       RunsTo env prog1 init_state inter_state ->
                                       (MapsTo temp1 (SCA av w1) inter_state
                                        /\ precond inter_state)))
                 (fun p1 => 
                    Bind 
                      (Pick (fun prog2 => 
                               forall inter_state final_state,
                                 precond inter_state /\ MapsTo temp1 (SCA av w1) inter_state ->
                                 RunsTo env prog2 inter_state final_state ->
                                 (MapsTo temp2 (SCA av w2) final_state 
                                  /\ MapsTo temp1 (SCA av w1) final_state
                                  /\ postcond final_state)))
                      (fun p2 => ret (Seq p1 
                                          (Seq p2 
                                               (Assign retvar 
                                                       (SyntaxExpr.TestE 
                                                          op
                                                          (SyntaxExpr.Var temp1) 
                                                          (SyntaxExpr.Var temp2)))))))).
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
  rewrite H0; clear H0.

  unfold eval in H; simpl in H;
  unfold eval_binop_m in H; simpl in H.

  set (find temp1 _) as r1 in H.
  set (find temp2 _) as r2 in H.
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

  apply StringMapFacts.M.add_1; reflexivity.
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
                            MapsTo ret_var (SCA av v) final_state 
                            /\ (fun x => True) final_state))
                 (fun prog => 
                    Bind (Pick (fun final_state => RunsTo env prog init_state final_state))
                         (fun final_state => Pick (fun x => MapsTo ret_var (SCA av x) final_state)))).
  intros.
  unfold refine.
  intros.
  inversion_by computes_to_inv.
  apply eq_ret_compute.

  apply (H _ _ I) in H1.
  eapply SCA_inj.
  eapply MapsTo_unique; eauto.
Qed.

Definition start_compiling := fun ret_var av => @start_compiling' ret_var av (empty_env av) (empty_state av).

Ltac spam :=
  solve [ unfold cond_respects_MapEq, Proper, respectful; 
          first [
              setoid_rewrite StringMapFacts.find_mapsto_iff;
              intros; match goal with 
                          [ H: StringMapFacts.M.Equal _ _ |- _ ] => 
                          rewrite H in * 
                      end;
              intuition 
            | intuition; 
              first [
                  apply StringMapFacts.M.add_2; 
                  congruence
                | idtac ] ] ].

Lemma compile_constant :
  forall retvar av env,
  forall w1 (precond postcond: State av -> Prop), 
    cond_respects_MapEq postcond ->
    (forall x state, precond state -> 
                     postcond (add retvar x state)) ->
    refine (Pick (fun prog1 => forall init_state final_state,
                                 precond init_state ->
                                 RunsTo env prog1 init_state final_state ->
                                 MapsTo retvar (SCA av w1) final_state
                                 /\ postcond final_state))
           (ret (Assign retvar (SyntaxExpr.Const w1))).
Proof.
  unfold refine; intros; constructor; intros; inversion_by computes_to_inv; subst.
  inversion_clear H3.
  unfold eval in H1.
  apply Some_inj, SCA_inj in H1; subst.

  unfold cond_respects_MapEq in *.
  rewrite H4; clear H4.

  split.
  apply StringMapFacts.M.add_1; reflexivity.
  intuition.
Qed.

Tactic Notation "cleanup" :=
  first [ simplify with monad laws | spam ].

Import Memory.

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
                      (Word.wplus  (IL.natToW 3) (IL.natToW 4)) 
                      (Word.wminus (IL.natToW 5) (IL.natToW 6)))) x.
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

Require Import SyntaxExpr.

Notation "{{ x ; .. ; y }}" := (Seq x .. (Seq y Skip) ..).

Notation "y <= f [[ x1 .. xn ]]" := (Call (Some y) (Const f) (cons x1 .. (cons xn nil) ..)) (at level 70, no associativity).

Notation "' x" := (Var x) (at level 50, no associativity).

Notation "# x" := (Const x) (at level 50, no associativity).

Notation "x !== y" := (TestE IL.Ne x y) (at level 50, no associativity).

Notation "x === y" := (TestE IL.Eq x y) (at level 50, no associativity).

Notation "! x" := (TestE IL.Eq (Var x) (Const WZero)) (at level 50, no associativity).

Notation "x <- y" := (Assign x y) (at level 70).

Definition basic_env := {| Label2Word := fun _ => None; 
                           Word2Spec := fun w => 
                                          if Word.weqb w WZero then Some (Axiomatic List_empty)
                                          else if Word.weqb w WOne then Some (Axiomatic List_pop)
                                               else None |}.

Definition Fold (head acc is_empty seq: key) 
                _pop_ _empty_ loop_body := {{
    is_empty <= _empty_ [[seq]];
    While (!is_empty) {{
        head <= _pop_ [[seq]];
        loop_body head acc;
        is_empty <= _empty_ [[seq]]
    }}
}}.

Notation "table [ key >> value ]" := (MapsTo key value table) (at level 0).

Definition SCA {x: Type} := @Facade.SCA x.
Definition ADT {x: Type} := @Facade.ADT x.

Lemma length_0 : forall {A: Type} (l: list A),
                   0 = Datatypes.length l <-> l = [].
Proof.
  destruct l; intros; simpl in *; intuition congruence.
Qed.    

Ltac autoinj :=
  repeat (match goal with
            | [ H: ?f ?a = ?f ?b |- _ ] => injection H; intros; clear H
                                                              | [ H: ?f ?x ?a = ?f ?x ?b |- _ ] => injection H; intros; clear H
                                                                                                                      | [ H: ?f ?a1 ?b1 = ?f ?a2 ?b2 |- _ ] => injection H; intros; clear H
          end; try subst).

Lemma unchanged : 
  forall av (st: State av) arg val,
    StringMapFacts.M.find arg st = Some (Facade.ADT val) -> 
    StringMapFacts.M.Equal 
      st (add_remove_many (arg :: nil) (Facade.ADT val :: nil) (Some (Facade.ADT val) :: nil) st).
Proof.
  simpl; intros.
  red; intro arg'.
  destruct ( StringMapFacts.M.E.eq_dec arg arg'); subst.
  
  rewrite StringMapFacts.add_eq_o; trivial.
  rewrite StringMapFacts.add_neq_o; trivial.
Qed.    
Opaque add_remove_many.

Ltac expand :=
  repeat match goal with
           | [ H := _ |- _ ] => unfold H in *; clear H
         end.

Lemma Seq_Skip :
  forall {ADTValue} env prog (st st': State ADTValue),
    RunsTo env {{prog}} st st' <->
    RunsTo env prog st st'.
Proof.
  split; intros ** H.
  inversion_clear H;
    inversion H1; subst; clear H1;
    assumption.
  econstructor; eauto; constructor.
Qed.    

Ltac autorewrite_equal :=
  match goal with
    | [ H: StringMapFacts.M.Equal ?a _, H': context[?a] |- _ ] => rewrite H in H'
    | [ H: StringMapFacts.M.Equal ?a _ |- _ ] => rewrite H in *
    | [ H: StringMapFacts.M.Equal ?a _ |- _ ] => setoid_rewrite H
  end.

  Ltac autoinj' :=
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
    end.

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
  forall (x: A) state, cond state -> cond (add var x state). (* TODO Use more *)

Ltac subst_find :=
  match goal with 
    | [H : find _ _ = _, 
           H': context[match find _ _ with | Some _ => _ | None => _ end] |- _] =>
      setoid_rewrite H in H' (* Wonder why setoid is needed here *)
  end.

Ltac autodestruct :=
  repeat match goal with
           | [ H: exists x, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
         end.

Ltac inversion_clear' hyp :=
  inversion hyp; expand; subst; clear hyp.

Transparent add_remove_many.
(* TODO generalize this for is_empty as well *)
Lemma runsto_pop :
  forall hd tl (vseq thead: key) env (st st': State (list W)) ppop,
    vseq <> thead ->
    st [vseq >> Facade.ADT (hd :: tl)] ->
    Word2Spec env ppop  = Some (Axiomatic List_pop) ->
    RunsTo env (thead <= ppop [[vseq]]) st st' ->
    StringMapFacts.M.Equal st' (add thead (Facade.SCA _ hd) (add vseq (Facade.ADT tl) st)).
Proof.
  intros * vseq_thead vseq_init ppop_is_pop runs_to.

  inversion_clear' runs_to; simpl in *; autoinj;
  [ | congruence].

  rewrite ppop_is_pop in *; autoinj;
  unfold List_pop in *; clear ppop_is_pop; simpl in *;
  autodestruct; subst;
  rewrite StringMapFacts.find_mapsto_iff in * |-;
                                                unfold sel in *;
  subst_find; simpl in *; autoinj. (* TODO Make autoinj call simpl in * first *)

  destruct output; [congruence|].
  simpl in *; autoinj; simpl in *.
  repeat autorewrite_equal.

  reflexivity.
Qed.

Lemma add_noop :
  forall {A: Type} {k: key} {v: A} {map},
    find k map = Some v ->
    Equal (add k v map) map.
Proof.
  unfold Equal; intros ** k';
  destruct (StringMapFacts.M.E.eq_dec k k');
  subst;
  [ rewrite StringMapFacts.add_eq_o | rewrite StringMapFacts.add_neq_o ];
  auto.
Qed.    

(* TODO: refactor to share code with runsto_pop *)
Lemma runsto_is_empty :
  forall seq (vseq tis_empty: key) env (st st': State (list W)) pis_empty,
    vseq <> tis_empty ->
    st [vseq >> Facade.ADT seq] ->
    Word2Spec env pis_empty  = Some (Axiomatic List_empty) ->
    RunsTo env (tis_empty <= pis_empty [[vseq]]) st st' ->
    exists ret, 
      (ret <> SCAZero <-> seq = []) /\
      StringMapFacts.M.Equal st' (add tis_empty ret st).
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

Opaque add_remove_many.

Definition LoopBodyOk env (f: W -> W -> W) (sloop_body: key -> key -> Stmt) (vret thead: key) :=
  forall (acc: W) (head: W),
  forall (st1 st2: State (list W)),
    (st1) [vret >> Facade.SCA (list W) acc] /\
    (st1) [thead >> Facade.SCA (list W) head] ->
    RunsTo env (sloop_body thead vret) st1 st2 ->
    StringMapFacts.M.Equal st2 (add vret (SCA (f acc head)) st1).

Lemma compile_fold : 
  forall env,
  forall postcond: State _ -> Prop,
  forall vseq vret,
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
    LoopBodyOk env f sloop_body vret thead ->
    forall seq init, 
      refine (Pick (fun prog => forall init_state final_state,
                                  init_state[vseq >> ADT seq] /\ 
                                  init_state[vret >> SCA init] ->
                                  RunsTo env prog init_state final_state ->
                                  final_state[vret >> 
                                              SCA (List.fold_left f seq init)]
                                   /\ postcond final_state))
             (ret ((Fold thead vret tis_empty vseq ppop pempty sloop_body))).
Proof.
  intros * vret_vseq vret_tis_empty thead_vret thead_vseq tis_empty_vseq postcond_meaningful postcond_indep_vret postcond_indep_tis_empty postcond_indep_thead postcond_indep_vseq zero_to_empty one_to_pop loop_body_ok.

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

  rewrite Seq_Skip in H5.

  simpl;
  (inversion_clear' H5);
  match goal with
    | [ H: is_true _ _ |- _] => rnm H test
    | [ H: is_false _ _ |- _] => rnm H test
  end;
  unfold is_true, is_false, eval_bool, eval, eval_binop_m, eval_binop, IL.wneb, IL.evalTest, IL.weqb in test;
  autorewrite_equal;
  (rewrite StringMapFacts.add_eq_o in *; trivial);
  destruct ret; try discriminate;
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
  subst.

  admit.

  specialize (IHseq (f init a) (Fold thead vret tis_empty vseq ppop pempty sloop_body)).
  specialize (IHseq (eq_ret_compute _ _ _ (eq_refl))).
  inversion_by computes_to_inv.
  rnm H IHseq_vret.
  rnm H0 IHseq_postcond.

  unfold cond_respects_MapEq, cond_indep in *.

  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  simpl;
  (inversion_clear' H5);
  match goal with
    | [ H: is_true _ _ |- _] => rnm H test
    | [ H: is_false _ _ |- _] => rnm H test
  end;
  unfold is_true, is_false, eval_bool, eval, eval_binop_m, eval_binop, IL.wneb, IL.evalTest, IL.weqb in test;
  autorewrite_equal;
  (rewrite StringMapFacts.add_eq_o in *; trivial);
  destruct ret; try discriminate;
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
  subst.

  Focus 2. (* a :: x = [] *)
  
  destruct H1 as (H1, _).
  specialize (H1 H0).
  congruence.

  (* Vraie récurrence *)

  clear H1. (* False <-> False *)
  clear H3. (* NoDup singleton *)

  inversion_clear' H4. (* Start chomping at loop body *)
  
  Print State.
  
  Show.
  
  rewrite <- StringMapFacts.find_mapsto_iff in *.
  apply (runsto_pop a seq) in H1; [ 
    | solve [eauto] 
    | autorewrite_equal;
      StringMapFacts.map_iff; intuition
    | solve [eauto] ].
  
  (* Now the loop body *)

  (* Just because it feels nice: specialize the induction hypotheses *)
  inversion_clear' H5.

  Ltac autoseq_skip :=
    match goal with
      | [ H: _ |- _ ] => rewrite Seq_Skip in H
    end.

  autoseq_skip.
  rewrite <- Seq_Skip in H8.
  pose proof (RunsToSeq H6 H8) as new_loop.
  clear H6 H8.
  
  unfold Fold in IHseq_vret.
  specialize (fun pre => IHseq_vret _ _ pre new_loop).
  specialize (fun pre => IHseq_postcond _ _ pre new_loop).
  (* yay *)

  unfold LoopBodyOk in loop_body_ok.

  specialize (loop_body_ok init a st'1 st'2). 
  rewrite H13 in H1. (* Thus st1' = ... *)

  (* TODO find prettier way to do these asserts *)
  
  assert ((st'1) [vret >> Facade.SCA (list W) init]) 
    as h1 by (rewrite H1;
              StringMapFacts.map_iff;
              intuition).
  
  assert ((st'1) [thead >> Facade.SCA (list W) a])
    as h2 by (rewrite H1;
              StringMapFacts.map_iff;
              intuition).

  (*
  Lemma MapsTo_equal :
    forall {elt : Type} {x1 y1 : StringMapFacts.M.t elt},
      StringMapFacts.M.Equal x1 y1 -> 
      forall {x: key} {y:elt},
        (x1) [x >> y] -> (y1) [x >> y].
  Proof.
    intros * eq1 *.
    pose proof (@StringMapFacts.MapsTo_m elt x x eq_refl y y eq_refl x1 y1 eq1); intuition.
  Qed.    
   *)

  specialize (loop_body_ok (conj h1 h2) H2); clear h1 h2.
  rewrite H1 in loop_body_ok.

  assert ((st'2) [vseq >> ADT seq])
    as h1 by (rewrite loop_body_ok;
              StringMapFacts.map_iff;
              intuition).

  assert ((st'2) [vret >> SCA (f init a)])
    as h2 by (rewrite loop_body_ok;
              StringMapFacts.map_iff;
              intuition).
              
  intuition.
Qed.
