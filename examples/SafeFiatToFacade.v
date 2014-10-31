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
Notation "∅" := (StringMap.empty _).

(* Facade notations and coercions *)

Definition nat_as_word n : Word.word 32 := Word.natToWord 32 n.
Coercion nat_as_word : nat >-> Word.word.

Definition string_as_var str : Expr := Var str.
Coercion string_as_var : string >-> Expr.

Definition word_as_constant w : Expr := Const w.
Coercion word_as_constant : W >-> Expr.

Definition nat_as_constant n : Expr := Const (Word.natToWord 32 n).
Coercion nat_as_constant : nat >-> Expr.

Notation "[ k >sca> v ] :: m" :=
  (StringMap.add k (Facade.SCA _ v) m) (at level 22, right associativity) : map_scope.
Notation "[ k >adt> v ] :: m" :=
  (StringMap.add k (Facade.ADT v) m) (at level 22, right associativity) : map_scope.

Delimit Scope map_scope with map.
Open Scope map_scope.

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

(* General tactics & lemmas *)

Lemma or_left_imp: forall {P Q R},
                     (P \/ Q -> R) -> (P -> R).
  tauto.
Qed.

Lemma or_right_imp: forall {P Q R},
                      (P \/ Q -> R) -> (Q -> R).
  tauto.
Qed.

Ltac autoinj :=
  intros; repeat (match goal with
                    | [ H: ?f ?a = ?f ?b |- _ ] => 
                      (injection H; intros; clear H)
                    | [ H: ?f ?x ?a = ?f ?x ?b |- _ ] => 
                      (injection H; intros; clear H)
                    | [ H: ?f ?a1 ?b1 = ?f ?a2 ?b2 |- _ ] => 
                      (injection H; intros; clear H)
                  end; try subst); try solve [intuition].

Ltac autoinj' := (* TODO: Needed? *)
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

Ltac autospecialize := (* TODO: Needed? *)
  repeat match goal with 
           | [ H: forall a b, ?x a -> ?y a b -> _, H': ?x _, H'': ?y _ _ |- _ ] 
             => specialize (H _ _ H' H'') 
           | [ H: forall a b, ?x a /\ ?x' a -> ?y a b -> _, H'1: ?x _, H'2: ?x' _, H'': ?y _ _ |- _ ] 
             => specialize (H _ _ (conj H'1 H'2) H'')
           | [ H: forall a b, ?x a /\ ?x' a /\ ?x'' a -> ?y a b -> _, H'1: ?x _, H'2: ?x' _, H'3: ?x'' _, H'': ?y _ _ |- _ ] 
             => specialize (H _ _ (conj H'1 (conj H'2 H'3)) H'')
         end.

Ltac expand := (* TODO: Needed? *)
  repeat match goal with
           | [ H := _ |- _ ] => unfold H in *; clear H
         end.

Ltac autorewrite_equal := (* TODO: Needed? *)
  match goal with
    | [ H: StringMap.Equal ?a _, H': context[?a] |- _ ] => rewrite H in H'
    | [ H: StringMap.Equal ?a _ |- _ ] => rewrite H in *
    | [ H: StringMap.Equal ?a _ |- _ ] => setoid_rewrite H
  end.

Ltac autodestruct := (* TODO: Needed? There's already destruct_pairs *)
  repeat match goal with
           | [ H: exists x, _ |- _ ] => destruct H
           | [ H: _ /\ _ |- _ ] => destruct H
         end.

Ltac inversion_clear' hyp :=  (* TODO: Needed? *)
  inversion hyp; expand; subst; clear hyp.

Ltac eq_transitive :=
  match goal with
    | [ H: ?a = ?b, H': ?a = ?c |- _ ] => 
      let H'' := fresh in
      assert (b = c) as H'' by (rewrite <- H, <- H'; reflexivity)
  end. (* TODO: Use more. Extend to cover a single map mapping the same key to two variables *)

Lemma and_eq_refl :
  forall {A} P (a: A), P /\ a = a <-> P.
Proof.
  firstorder.
Qed.

Ltac and_eq_refl :=
  repeat match goal with
           | [ H: context [ ?a = ?a ] |- _ ] => setoid_rewrite and_eq_refl in H
         end.

(* Map lemmas and tactics *)

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

Lemma not_in_remove_eq :
  forall {elt} k m,
    ~ @StringMap.In elt k m ->
    StringMap.Equal 
      m (StringMap.remove k m).
Proof.
  unfold StringMap.Equal; intros ** k'.
  destruct (StringMap.E.eq_dec k k'); subst.

  rewrite StringMapFacts.not_in_find, StringMapFacts.remove_eq_o by trivial;
    reflexivity.

  rewrite StringMapFacts.remove_neq_o by trivial;
    reflexivity.
Qed.

Lemma not_in_empty :
  forall {elt} k,
    ~ @StringMap.In elt k ∅ .
Proof.
  intros ** _in; rewrite <- StringMapFacts.empty_in_iff; eassumption.
Qed.

Definition cond_respects_MapEq {elt} := (* TODO: Needed? *)
  Proper (StringMap.Equal (elt := elt) ==> iff).

Ltac remove_not_in :=
  match goal with
    | [ H: ~ StringMap.In ?k ?m, H': context[StringMap.remove ?k ?m] |- _] =>
      setoid_rewrite <- (not_in_remove_eq k m H) in H'
  end.

Ltac subst_find :=
  match goal with 
    | [H: StringMap.find ?a ?b = _, 
       H': context[match StringMap.find ?a ?b with
                     | Some _ => _
                     | None => _ end] |- _] =>
      setoid_rewrite H in H' (* Wonder why setoid is needed here *)
    | [H: StringMap.find ?a ?b = _
       |- context[match StringMap.find ?a ?b with
                    | Some _ => _
                    | None => _ end]] =>
      setoid_rewrite H
    | [H: StringMap.MapsTo ?k ?v ?m, 
       H': context[match StringMap.find ?k ?m with
                     | Some _ => _
                     | None => _ end] |- _] =>
      rewrite StringMapFacts.find_mapsto_iff in H;
        setoid_rewrite H in H';
        rewrite <- StringMapFacts.find_mapsto_iff in H
    | [H : StringMap.MapsTo ?k ?v ?m
       |- context[match StringMap.find ?k ?m with
                    | Some _ => _
                    | None => _ end]] =>
      rewrite StringMapFacts.find_mapsto_iff in H;
        setoid_rewrite H;
        rewrite <- StringMapFacts.find_mapsto_iff in H
  end. (* TODO: use instead of calling StringMapFacts.find_mapsto_iff everywhere. *)

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

Ltac auto_mapsto_unique :=
  repeat progress match goal with
                    | [H: StringMap.MapsTo ?k ?v ?st, H': StringMap.MapsTo ?k ?v' ?st |- _] =>
                      let h := fresh in
                      pose proof (MapsTo_unique st k v v' H H') as h;
                        injection h; clear H
                  end. (* TODO: Use more *)

(* Pre and post-conditions *)

Definition SomeSCAs {av} (state : State av) bindings :=
  forall k v, StringMap.MapsTo k (Facade.SCA av v) bindings -> StringMap.MapsTo k (Facade.SCA av v) state.

Definition AllADTs {av} (state: State av) bindings  :=
  forall k v, StringMap.MapsTo k (Facade.ADT v) bindings <-> StringMap.MapsTo k (Facade.ADT v) state.

Definition Prog {av env} initial_knowledge initial_scas final_scas initial_adts final_adts :=
  {prog | forall initial_state,
            initial_knowledge /\
            SomeSCAs initial_state initial_scas /\
            AllADTs initial_state initial_adts  ->
            Safe env prog initial_state /\
            forall final_state,
              @RunsTo av env prog initial_state final_state ->
              SomeSCAs final_state final_scas /\
              AllADTs final_state final_adts}%comp.

(* Facade lemmas and tactics *)

Ltac unfold_coercions :=
  unfold string_as_var, nat_as_constant, nat_as_word, word_as_constant in *.

Definition BoolToW (b: bool) := if b then WOne else WZero.

Definition WToBool (w: @Word.word 32) := negb (Word.weqb w WZero).

Lemma BoolToW_invert : forall b, WToBool (BoolToW b) = b.
Proof.
  destruct b; intuition.
Qed.

Lemma BoolToW_eval :
  forall {av} state var b1 b2,
    b1 = negb b2 ->
    state[var >> SCA av (BoolToW b1)] ->
    eval_bool state (var = 0)%facade = Some b2.
Proof.
  unfold_coercions; unfold BoolToW, WOne, WZero, eval_bool, eval, eval_binop_m;
  intros; subst_find; destruct b2; subst; reflexivity.
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

Lemma eval_binop_inv :
  forall (test: bool),
    IL.wneb (eval_binop (inr IL.Eq) (if test then WOne else WZero) WZero)
            (Word.natToWord 32 0) = negb test.
Proof.
  intros; destruct test; simpl; reflexivity.
Qed.

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

(* Pre/post conditions lemmas *)

Lemma SomeSCAs_mapsto :
  forall {av} {state: State av} {k v map},
    SomeSCAs state ([k >sca> v]::map) ->
    state[k >> SCA _ v].
Proof.
  unfold SomeSCAs; intros * add.
  apply add; map_iff_solve intuition.
Qed.

Lemma SomeSCAs_remove :
  forall {av} {state: State av} {k v map},
    SomeSCAs state ([k >sca> v]::map) ->
    SomeSCAs state (StringMap.remove k map).
Proof.
  unfold SomeSCAs; intros.
  apply H. rewrite StringMapFacts.remove_mapsto_iff in *.
  destruct_pairs; map_iff_solve assumption.
Qed.

Lemma SomeSCAs_swap :
  forall {av} {state: State av} {k1 k2 v map},
    k1 <> k2 ->
    SomeSCAs state (StringMap.remove k1 ([k2 >sca> v]::map)) ->
    SomeSCAs state ([k2 >sca> v]::(StringMap.remove k1 map)).
Proof.
  unfold SomeSCAs; intros.
  apply H0. map_iff_solve idtac.
  
  destruct (StringMap.E.eq_dec k k1); subst.
  rewrite StringMapFacts.add_neq_mapsto_iff in * by congruence.
  rewrite StringMapFacts.remove_mapsto_iff in *; destruct_pairs; assumption.
  congruence.

  destruct (StringMap.E.eq_dec k k2); subst; map_iff_solve idtac;
  rewrite StringMapFacts.add_mapsto_iff in *;
  rewrite StringMapFacts.remove_mapsto_iff in *;
  intuition.
Qed.

Lemma AllADTs_not_in :
  forall {av} {var map state},
    @AllADTs av state map ->
    ~ StringMap.In (elt:=Value av) var map ->
    (exists v, StringMap.find var state = Some (SCA _ v)) \/ ~ StringMapFacts.M.In var state.
Proof.
  unfold AllADTs; intros.
  destruct (StringMap.find var state) eqn:eq0.

  destruct v.
  left; eexists; reflexivity.
  rewrite <- StringMapFacts.find_mapsto_iff, <- H in eq0.
  apply StringMapFacts.MapsTo_In in eq0.
  congruence.

  rewrite StringMapFacts.not_find_in_iff; right; assumption.
Qed.

Lemma SomeSCAs_empty :
  forall {av} state,
    @SomeSCAs av state ∅.
Proof.
  unfold SomeSCAs; intros; rewrite StringMapFacts.empty_mapsto_iff in *; exfalso; assumption.
Qed.

Lemma not_in_adts_not_mapsto_adt :
  forall {av} var state map,
    @AllADTs av state map ->
    ~ StringMap.In var map ->
    not_mapsto_adt var state = true.
Proof.
  unfold not_mapsto_adt, is_mapsto_adt, is_some_p;
  intros * h h'.
  destruct (AllADTs_not_in h h') as [ [ v sbst ] | ];
    [ rewrite sbst; trivial  | ].
  
  rewrite StringMapFacts.not_in_find; trivial.
Qed.

Add Parametric Morphism {av} :
  (@SomeSCAs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SomeSCAs_morphism.
Proof.
  unfold SomeSCAs;  intros * eq * eq'; split; intros.
  rewrite <- ?eq, <- ?eq' in *; intuition.
  rewrite ?eq, ?eq' in *; intuition.
Qed.

Add Parametric Morphism {av} :
  (@AllADTs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SomeADTs_morphism.
Proof.
  unfold AllADTs;  intros * eq * eq'; split; intros H ** .
  rewrite <- ?eq, <- ?eq' in *; intuition; apply H; assumption.
  rewrite ?eq, ?eq' in *; intuition; apply H; assumption.
Qed.

Lemma SomeSCAs_chomp :
  forall {av} (state: State av) k v scas,
    SomeSCAs state scas ->
    SomeSCAs ([k >sca> v]::state) ([k >sca> v]::scas).
Proof.
  unfold SomeSCAs; intros * h ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k');
    subst; rewrite StringMapFacts.add_mapsto_iff in *;
    intuition.
Qed.

Lemma add_adts_pop_sca :
  forall {av} k v map (state: State av),
    ~ StringMap.In k map ->
    AllADTs state map ->
    AllADTs ([k >sca> v]::state) map.
Proof.
  unfold AllADTs; intros ** k' v'.
  destruct (StringMap.E.eq_dec k k'); subst;
  split; intros H';
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac.

  apply StringMapFacts.MapsTo_In in H'; congruence.
  intuition; discriminate.

  rewrite H0 in *; intuition.
  rewrite H0 in *; intuition.
Qed.

(* Specialized tactics *)

Ltac BoolToW_eval_helper :=
  try match goal with
        | [ |- true = negb ?a ] => unify a false; reflexivity
        | [ |- false = negb ?a ] => unify a true; reflexivity
      end.

Ltac inversion_facade :=
  match goal with
    | [ H: RunsTo _ ?p _ _ |- _ ] =>
      match p with
        | Skip => idtac 
        | Seq _ _ => idtac 
        | Facade.If _ _ _ => idtac
        | Facade.While _ _ => idtac
        | Call _ _ _ => idtac
        | Label _ _ => idtac
        | Assign _ _ => idtac
        | _ => fail 1
      end; inversion_clear' H
  end.

Ltac specialize_initial_state :=
  repeat match goal with
           | [ H: (forall initial_state : State _,
                     ?init_knowledge /\
                     SomeSCAs initial_state ?init_scas /\
                     AllADTs initial_state ?init_adts -> _),
               Hknowledge: ?init_knowledge,
               Hscas: SomeSCAs ?initial_state ?init_scas,
               Hadts: AllADTs ?initial_state ?init_adts                   
               |- _] => specialize (H _ (conj Hknowledge (conj Hscas Hadts)))
         end.

Ltac specialize_final_state :=
  repeat match goal with
           | [ H: (forall final_state : State _,
                     RunsTo ?env ?prog ?initial_state final_state -> _),
               Hruns: RunsTo ?env ?prog ?initial_state ?final_state
               |- _ ] => specialize (H _ Hruns)
         end.

Ltac specialize_states :=
  repeat (specialize_initial_state;
          specialize_final_state).

Ltac safe_seq :=
  constructor;
  split; [ specialize_states; assumption | ].

Ltac some_scas_mapsto :=
  repeat match goal with
           | [ H: SomeSCAs ?state ([?k >sca> ?v]::?map) |- _ ] =>
             progress (let maps_to := fresh "maps_to" in
                       let some_scas := fresh "some_scas" in
                       pose proof (SomeSCAs_mapsto H) as maps_to;
                       pose proof (SomeSCAs_remove H) as some_scas;
                       try (apply SomeSCAs_swap in some_scas; [ | solve [auto] ]);
                       clear_dups)
         end.

Ltac rewrite_Eq_in_goal :=
  match goal with
    | [ H: StringMap.Equal _ _ |- SomeSCAs _ _ ] =>
      rewrite H
    | [ H: StringMap.Equal _ _ |- AllADTs _ _ ] =>
      rewrite H
  end.

Opaque Word.natToWord.

(* Compilation lemmas *)

Lemma compile_if_sca :
  forall {av env}
         (vtest: StringMap.key) {vret}
         (test: bool)
         init_knowledge
         init_scas init_adts post_test_adts final_adts
         truecase falsecase,
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> if test then truecase
                                         else falsecase] :: init_scas)
                  init_adts final_adts)
           (ptest  <- (@Prog av env init_knowledge
                             init_scas ([vtest >sca> BoolToW test] :: init_scas)
                             init_adts post_test_adts);
            ptrue  <- (@Prog av env (init_knowledge /\ test = true)
                             ([vtest >sca> BoolToW test] :: init_scas) ([vret >sca>  truecase] :: init_scas)
                             post_test_adts final_adts);
            pfalse <- (@Prog av env (init_knowledge /\ test = false)
                            ([vtest >sca> BoolToW test] :: init_scas) ([vret >sca> falsecase] :: init_scas)
                            post_test_adts final_adts);
            ret (ptest; If vtest = 0 then pfalse else ptrue)%facade)%comp.
Proof.
  unfold refine, Prog; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)
  constructor;
  split;
    [ solve [intuition] |
      intros;
        destruct test;
        and_eq_refl; (* Clean up 'true = true' style conditions *) 
        [ apply SafeIfFalse | apply SafeIfTrue ];
        specialize_states;
        some_scas_mapsto; (* Extract value of vtest *)
        first [ assumption | eapply BoolToW_eval; trivial] ].
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    unfold is_true, is_false in *;
    destruct test;
    and_eq_refl;
    specialize_states;
    some_scas_mapsto;
    eapply BoolToW_eval in maps_to;
    BoolToW_eval_helper; try (eq_transitive; congruence);
    split; assumption.
Qed.

Lemma compile_binop :
  forall {av env},
  forall op vret tw1 tw2,
  forall w1 w2,
  forall init_knowledge init_scas init_adts post_w1_adts final_adts,
    tw1 <> tw2 ->
    ~ StringMap.In tw1 init_scas ->
    ~ StringMap.In tw2 init_scas ->
    ~ StringMap.In vret final_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> IL.evalBinop op w1 w2] :: init_scas)
                  init_adts final_adts)
           (pw1  <- (@Prog av env init_knowledge
                           init_scas ([tw1 >sca> w1] :: init_scas)
                           init_adts post_w1_adts);
            pw2  <- (@Prog av env init_knowledge
                           ([tw1 >sca> w1] :: init_scas)
                           ([tw2 >sca> w2] :: [tw1 >sca> w1] :: init_scas)
                           post_w1_adts final_adts);
            ret (pw1; pw2; Assign vret (Binop op tw1 tw2))%facade)%comp.
Proof.
  unfold refine, Prog; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  some_scas_mapsto.

  (*TODO: Prettier way of doing this? *)
  assert (forall k : string,
            List.In k (AllVariables (Binop op (Var tw1) (Var tw2))) ->
            exists v : W, (st'0) [k >> SCA av v])
    as temp
    by (unfold AllVariables; simpl; intros; intuition; eexists; subst; eassumption).
  destruct (eval_expr_some_sca (Binop op (Var tw1) (Var tw2)) st'0 temp).

  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  
  intros;
    repeat inversion_facade;
    specialize_states;
    some_scas_mapsto;
    unfold eval, eval_binop_m in *;
    repeat (subst_find; simpl in *);
    autoinj.

  split;
    rewrite_Eq_in_goal;
    [ repeat remove_not_in;
      apply SomeSCAs_chomp
    | apply add_adts_pop_sca ];
    assumption.
Qed.  

Lemma compile_test :
  forall {av env},
  forall op vret tw1 tw2,
  forall w1 w2,
  forall init_knowledge init_scas init_adts post_w1_adts final_adts,
    tw1 <> tw2 ->
    ~ StringMap.In tw1 init_scas ->
    ~ StringMap.In tw2 init_scas ->
    ~ StringMap.In vret final_adts ->
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> BoolToW ((IL.evalTest op) w1 w2)] :: init_scas)
                  init_adts final_adts)
           (pw1  <- (@Prog av env init_knowledge
                           init_scas ([tw1 >sca> w1] :: init_scas)
                           init_adts post_w1_adts);
            pw2  <- (@Prog av env init_knowledge
                           ([tw1 >sca> w1] :: init_scas)
                           ([tw2 >sca> w2] :: [tw1 >sca> w1] :: init_scas)
                           post_w1_adts final_adts);
            ret (pw1; pw2; Assign vret (TestE op tw1 tw2))%facade)%comp.
Proof. (* Same proof as compile_binop *)
  unfold refine, Prog; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  some_scas_mapsto.

  (*TODO: Prettier way of doing this? *)
  assert (forall k : string,
            List.In k (AllVariables (TestE op (Var tw1) (Var tw2))) ->
            exists v : W, (st'0) [k >> SCA av v])
    as temp
    by (unfold AllVariables; simpl; intros; intuition; eexists; subst; eassumption).
  destruct (eval_expr_some_sca (TestE op (Var tw1) (Var tw2)) st'0 temp).

  econstructor; try eassumption.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  
  intros;
    repeat inversion_facade;
    specialize_states;
    some_scas_mapsto;
    unfold eval, eval_binop_m in *;
    repeat (subst_find; simpl in *);
    autoinj.

  split;
    rewrite_Eq_in_goal;
    [ repeat remove_not_in;
      apply SomeSCAs_chomp
    | apply add_adts_pop_sca ];
    assumption.
Qed.  

(* 
Lemma weaken_preconditions :
  forall av env (old_precond new_precond postcond: State av -> Prop), 
    (forall s, old_precond s -> new_precond s) ->
    refine
      Prog
      (Pick (fun prog =>
               (forall init_state,
                  new_precond init_state ->
                  Safe env prog init_state) /\
               (forall init_state final_state,
                  new_precond init_state ->
                  RunsTo env prog init_state final_state -> 
                  postcond final_state))).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  constructor; firstorder. 
Qed.

Lemma drop_preconditions :
  forall av env (precond postcond: State av -> Prop), 
    refine 
      (Pick (fun prog => 
               (forall init_state,
                  precond init_state ->
                  Safe env prog init_state) /\
               (forall init_state final_state,
                  precond init_state ->
                  RunsTo env prog init_state final_state -> 
                  postcond final_state)))
      (Pick (fun prog =>
               (forall init_state,
                  (fun _ => True) init_state ->
                  Safe env prog init_state) /\
               (forall init_state final_state,
                  (fun _ => True) init_state ->
                  RunsTo env prog init_state final_state -> 
                  postcond final_state))).
Proof.
  eauto using weaken_preconditions.
Qed.

Lemma strengthen_postconditions :
  forall av env (precond old_postcond new_postcond: State av -> Prop), 
    (forall s, new_postcond s -> old_postcond s) ->
    refine
      (Pick (fun prog =>
               (forall init_state,
                  precond init_state ->
                  Safe env prog init_state) /\
               (forall init_state final_state,
                  precond init_state ->
                  RunsTo env prog init_state final_state -> 
                  old_postcond final_state)))
      (Pick (fun prog =>
               (forall init_state,
                  precond init_state ->
                  Safe env prog init_state) /\
               (forall init_state final_state,
                  precond init_state ->
                  RunsTo env prog init_state final_state -> 
                  new_postcond final_state))).
Proof.
  unfold refine; intros; inversion_by computes_to_inv.
  constructor; firstorder.
Qed.
 *)

Lemma start_compiling' : 
  forall {av env} init_state vret v,
    AllADTs init_state (StringMap.empty _) ->
    refine (ret v) 
           (prog <- (@Prog av env True
                           ∅ ([vret >sca> v]::∅)
                           ∅ ∅);
            final_state <- {final_state | RunsTo env prog init_state final_state};
            {x | final_state[vret >> SCA av x]})%comp.
Proof.
  unfold refine, Prog; intros.
  inversion_by computes_to_inv.
  apply eq_ret_compute.

  pose proof I.
  pose proof (SomeSCAs_empty init_state).
  specialize_states.
  some_scas_mapsto.
  auto_mapsto_unique;
    autoinj.
Qed.

Lemma compile_constant :
  forall {av env} (vret: StringMap.key),
  forall (w: W) init_knowledge init_scas init_adts,
    ~ StringMap.In vret init_adts -> 
    refine (@Prog av env init_knowledge
                  init_scas ([vret >sca> w]::init_scas)
                  init_adts init_adts)
           (ret (Assign vret w)).
Proof.
  unfold Prog, refine; unfold_coercions; intros;
  inversion_by computes_to_inv;
  constructor; intros;
  subst;
  destruct_pairs;
  split.

  (* Safe *)
  econstructor.
  compute; reflexivity.
  eapply not_in_adts_not_mapsto_adt; eauto.

  (* RunsTo *)
  intros; inversion_facade.
  split; rewrite_Eq_in_goal.
  
  match goal with
    | [ H: eval _ (Const _) = Some _ |- _ ] => injection H; intros; subst
  end; apply SomeSCAs_chomp; assumption.

  apply add_adts_pop_sca; assumption.
Qed.

Definition empty_env ADTValue : Env ADTValue :=
  {| Label2Word := fun _ => None;
     Word2Spec := fun _ => None |}.

Definition empty_state ADTValue : State ADTValue := ∅. 

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

Definition start_compiling_sca :=
  fun av => @start_compiling' av (empty_env av) (empty_state av).

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
  intros;
  try first [ simplify with monad laws 
        | spam 
        | discriminate
        | match goal with 
            | [ |- Word2Spec ?env _ = _ ] => unfold env; simpl; intuition
          end
        ].

Lemma drop_sca :
  forall {av env} k v
         init_knowledge
         init_scas final_scas
         init_adts final_adts,
    ~ StringMap.In k init_scas ->
    refine (@Prog av env init_knowledge
                  ([k >sca> v]::init_scas) final_scas
                  init_adts final_adts)
           (@Prog av env init_knowledge
                  init_scas final_scas
                  init_adts final_adts).
Proof.
  unfold Prog, refine; intros.
  inversion_by computes_to_inv.
  constructor; intros.
  destruct_pairs;
    match goal with
      | [ H: SomeSCAs _ _ |- _ ] =>
        apply SomeSCAs_remove in H;
          rewrite <- not_in_remove_eq in H by assumption
    end; specialize_states; split.

  (* Safe *)
  assumption.

  (* RunsTo *)
  intros; specialize_states; split; assumption.
Qed.

Ltac vacuum := (* TODO: How can I force failures of discriminate  *)
  match goal with
    | [ |- ?a <> ?b ] => 
      first [ is_evar a | is_evar b | discriminate ]
    | [ |- ~ StringMap.In ?k ∅ ] =>
      solve [apply not_in_empty]
    | [ |- ~ StringMap.In ?k ?s ] =>
      first [ is_evar s | solve [map_iff_solve ltac:(intuition discriminate)] ]
    | [ |- AllADTs ?m ?s ] =>
      solve [unfold AllADTs; intros; map_iff_solve intuition]
    | [ |- refine _ _ ] =>
      try simplify with monad laws
  end.

Goal forall w1 w2: W, 
     exists x, 
       refine (ret (if Word.weqb w1 w2 then (IL.natToW 3) else (IL.natToW 4))) x.
Proof.
  eexists.

  setoid_rewrite (start_compiling_sca (list W) "$ret"); vacuum.
  
  setoid_rewrite (compile_if_sca "$cond"); vacuum.
  setoid_rewrite (compile_test IL.Eq "$cond" "$w1" "$w2"); vacuum.

  setoid_rewrite (compile_constant "$w1"); vacuum.
  setoid_rewrite (compile_constant "$w2"); vacuum.

  rewrite drop_sca; vacuum.
  rewrite (compile_constant "$ret"); vacuum.

  rewrite drop_sca; vacuum.
  rewrite (compile_constant "$ret"); vacuum.

  reflexivity.
  vacuum.
Qed.

(* <TODO> *)
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
  forall (x: A) state, cond state -> cond (StringMap.add var x state).

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
(* </TODO> *)

Goal exists x, 
       refine (ret (Word.wmult 
                      (Word.wplus  3 4)
                      (Word.wminus 5 6))) x.
Proof.
  eexists.
  
  setoid_rewrite (start_compiling_sca False "$ret"); vacuum.
  setoid_rewrite (compile_binop IL.Times "$ret" "$t1" "$t2"); vacuum.
  
  setoid_rewrite (compile_binop IL.Plus  "$t1" "$t11" "$t12"); vacuum.
  setoid_rewrite (compile_constant "$t11"); vacuum.
  setoid_rewrite (compile_constant "$t12"); vacuum. 
  
  setoid_rewrite (compile_binop IL.Minus "$t2" "$t21" "$t22"); vacuum.
  
  setoid_rewrite (compile_constant "$t21"); vacuum.
  setoid_rewrite (compile_constant "$t22"); vacuum.
  
  reflexivity.
  vacuum.
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
