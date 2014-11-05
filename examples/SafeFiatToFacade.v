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
Notation "[ k >> v ] :: m" :=
  (StringMap.add k v m) (at level 22, right associativity) : map_scope.

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

Lemma or_left_imp: forall {P Q R},
                     (P \/ Q -> R) -> (P -> R).
  tauto.
Qed.

Lemma or_right_imp: forall {P Q R},
                      (P \/ Q -> R) -> (Q -> R).
  tauto.
Qed.

Lemma not_or :
  forall P Q,
    ~ (P \/ Q) <-> (~ P /\ ~ Q).
  intuition.
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
       H': context[StringMap.find ?a ?b] |- _] =>
      setoid_rewrite H in H'
    | [H: StringMap.find ?a ?b = _
       |- context[StringMap.find ?a ?b]] =>
      setoid_rewrite H
    | [H: StringMap.MapsTo ?k ?v ?m, 
       H': context[StringMap.find ?k ?m] |- _] =>
      rewrite StringMapFacts.find_mapsto_iff in H;
        setoid_rewrite H in H';
        rewrite <- StringMapFacts.find_mapsto_iff in H
    | [H : StringMap.MapsTo ?k ?v ?m
       |- context[StringMap.find ?k ?m]] =>
      rewrite StringMapFacts.find_mapsto_iff in H;
        setoid_rewrite H;
        rewrite <- StringMapFacts.find_mapsto_iff in H
  end. (* TODO: use instead of calling StringMapFacts.find_mapsto_iff everywhere. *)

Ltac map_iff_solve' fallback :=
  repeat setoid_rewrite not_or;
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
  try rewrite <- StringMapFacts.find_mapsto_iff in *;
  repeat progress match goal with
                    | [H: StringMap.MapsTo ?k ?v ?st, H': StringMap.MapsTo ?k ?v' ?st |- _] =>
                      let h := fresh in
                      pose proof (MapsTo_unique st k v v' H H') as h;
                        first [discriminate | injection h; clear H]
                  end.

Ltac simpl_find_add_remove :=
  match goal with
    | [ |- context[StringMap.find ?k (StringMap.remove ?k ?m)] ] =>
      rewrite (@StringMapFacts.remove_eq_o _ m k k) by reflexivity
    | [ H: ?k <> ?k' |- context[StringMap.find ?k (StringMap.remove ?k' ?m)] ] =>
      rewrite (@StringMapFacts.remove_neq_o _ m k' k) by congruence
    | [ H: ?k' <> ?k |- context[StringMap.find ?k (StringMap.remove ?k' ?m)] ] =>
      rewrite (@StringMapFacts.remove_neq_o _ m k' k) by congruence
    | [ |- context[StringMap.find ?k (StringMap.add ?k ?v ?m)] ] =>
      rewrite (@StringMapFacts.add_eq_o _ m k k v (eq_refl _)) by reflexivity
    | [ H: ?k' <> ?k |- context[StringMap.find ?k (StringMap.add ?k' ?v ?m)] ] =>
      rewrite (@StringMapFacts.add_neq_o _ m k' k v) by congruence
    | [ H: ?k <> ?k' |- context[StringMap.find ?k (StringMap.add ?k' ?v ?m)] ] =>
      rewrite (@StringMapFacts.add_neq_o _ m k' k v) by congruence
    | [ |- context[StringMap.find ?k (StringMap.empty _)] ] =>
      rewrite (StringMapFacts.empty_o _ k)
  end.

Lemma StringMap_remove_add_neq :
  forall {elt} {k1 k2 v} (map: StringMap.t elt),
    k1 <> k2 ->
    StringMap.Equal (StringMap.remove k2 (StringMap.add k1 v map)) (StringMap.add k1 v (StringMap.remove k2 map)).
Proof.
  unfold StringMap.Equal; intros ** k'.
  destruct (StringMap.E.eq_dec k' k1), (StringMap.E.eq_dec k' k2);
    subst; repeat simpl_find_add_remove; congruence.
Qed.

Lemma StringMap_remove_add_eq :
  forall {elt} {k1 k2 v} (map: StringMap.t elt),
    k1 = k2 ->
    StringMap.Equal (StringMap.remove k2 (StringMap.add k1 v map)) (StringMap.remove k2 map).
Proof.
  unfold StringMap.Equal; intros ** k'.
  destruct (StringMap.E.eq_dec k' k1), (StringMap.E.eq_dec k' k2);
    subst; repeat simpl_find_add_remove; congruence.
Qed.

Lemma StringMap_remove_empty :
  forall {elt : Type} (k : StringMap.key),
    StringMap.Equal (StringMap.remove (elt:=elt) k ∅) ∅ .
Proof.
  unfold StringMap.Equal; intros ** k'.
  destruct (StringMap.E.eq_dec k' k);
    subst; repeat simpl_find_add_remove; congruence.
Qed.

(* Pre and post-conditions *)

Definition Subset
           {elt wrapped_elt}
           (state bindings: StringMap.t wrapped_elt)
           (wrapper: elt -> wrapped_elt) :=
  forall k v, StringMap.MapsTo k (wrapper v) bindings -> StringMap.MapsTo k (wrapper v) state.

Definition SomeSCAs {av} (state : State av) bindings :=
  Subset state bindings (Facade.SCA av).

Definition AllADTs {av} (state: State av) bindings  :=
  Subset state bindings (@Facade.ADT av) /\
  Subset bindings state (@Facade.ADT av).
  
Definition ProgOk {av env} prog initial_knowledge initial_scas final_scas initial_adts final_adts :=
  forall initial_state,
    initial_knowledge /\
    SomeSCAs initial_state initial_scas /\
    AllADTs initial_state initial_adts  ->
    Safe env prog initial_state /\
    forall final_state,
      @RunsTo av env prog initial_state final_state ->
      SomeSCAs final_state final_scas /\
      AllADTs final_state final_adts.

Definition Prog {av env} initial_knowledge initial_scas final_scas initial_adts final_adts :=
  {prog | @ProgOk av env prog initial_knowledge initial_scas final_scas initial_adts final_adts }%comp.

(* Facade lemmas and tactics *)

Ltac unfold_coercions :=
  unfold string_as_var, nat_as_constant, nat_as_word, word_as_constant in *.

Definition BoolToW (b: bool) := if b then WOne else WZero.

Definition WToBool (w: @Word.word 32) := negb (Word.weqb w WZero).

Lemma BoolToW_invert : forall b, WToBool (BoolToW b) = b.
Proof.
  destruct b; intuition.
Qed.

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
  unfold_coercions; unfold BoolToW, WOne, WZero, eval_bool, eval, eval_binop_m;
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

Lemma Subset_mapsto :
  forall {elt welt} {k v state map} wrapper,
    @Subset elt welt state ([k >> wrapper v]::map) wrapper ->
    state[k >> wrapper v].
Proof.
  unfold Subset; intros * add.
  apply add; map_iff_solve intuition.
Qed.

Lemma SomeSCAs_mapsto :
  forall {av} {state: State av} {k v map},
    SomeSCAs state ([k >sca> v]::map) ->
    state[k >> SCA _ v].
Proof.
  intros *; apply Subset_mapsto.
Qed.

Lemma AllADTs_mapsto :
  forall {av} {state: State av} {k v map},
    AllADTs state ([k >adt> v]::map) ->
    state[k >> Facade.ADT v].
Proof.
  unfold AllADTs; intros * (? & ?); eapply Subset_mapsto; eauto.
Qed.

Lemma Subset_remove :
  forall {elt welt} {k v state map} wrapper,
    @Subset elt welt state ([k >> wrapper v]::map) wrapper ->
    @Subset elt welt state (StringMap.remove k map) wrapper.
Proof.
  unfold Subset; intros.
  apply H. rewrite StringMapFacts.remove_mapsto_iff in *.
  destruct_pairs; map_iff_solve assumption.
Qed.

Lemma SomeSCAs_remove :
  forall {av} {state: State av} {k v map},
    SomeSCAs state ([k >sca> v]::map) ->
    SomeSCAs state (StringMap.remove k map).
Proof.
  intros *; apply Subset_remove.
Qed.

Lemma AllADTs_remove :
  forall {av} {state: State av} {k v map},
    AllADTs state ([k >adt> v]::map) ->
    Subset state (StringMap.remove k map) (@Facade.ADT _).
Proof.
  unfold AllADTs; intros * (? & ?); eapply Subset_remove; eauto.
Qed.

Lemma Subset_swap_remove :
  forall {elt welt} {k1 k2 v state map} wrapper,
    k1 <> k2 ->
    @Subset elt welt state (StringMap.remove k1 ([k2 >> wrapper v]::map)) wrapper ->
    @Subset elt welt state ([k2 >> wrapper v]::(StringMap.remove k1 map)) wrapper.
Proof.
  unfold Subset; intros.
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

Lemma SomeSCAs_swap_remove :
  forall {av} {state: State av} {k1 k2 v map},
    k1 <> k2 ->
    SomeSCAs state (StringMap.remove k1 ([k2 >sca> v]::map)) ->
    SomeSCAs state ([k2 >sca> v]::(StringMap.remove k1 map)).
Proof.
  intros *; apply Subset_swap_remove.
Qed.

Lemma AllADTs_swap_remove :
  forall {av} {state: State av} {k1 k2 v map},
    k1 <> k2 ->
    AllADTs state (StringMap.remove k1 ([k2 >adt> v]::map)) ->
    Subset state ([k2 >> Facade.ADT v]::(StringMap.remove k1 map)) (@Facade.ADT _).
Proof.
  unfold AllADTs; intros * ? (? & ?); eapply Subset_swap_remove; eauto.
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
  destruct_pairs.
  rewrite <- StringMapFacts.find_mapsto_iff in eq0.
  apply H1 in eq0.
  apply StringMapFacts.MapsTo_In in eq0.
  congruence.

  rewrite StringMapFacts.not_find_in_iff; right; assumption.
Qed.

Lemma Subset_empty :
  forall {elt welt} state wrapper,
    @Subset elt welt state ∅ wrapper.
Proof.
  unfold Subset; intros; rewrite StringMapFacts.empty_mapsto_iff in *; exfalso; assumption.
Qed.
  
Lemma SomeSCAs_empty :
  forall {av} state,
    @SomeSCAs av state ∅ .
Proof.
  intros; apply Subset_empty.
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

Ltac rewrite_Eq_in_all :=
  repeat match goal with
           | [ H: StringMap.Equal _ _, H': _ |- _ ] =>
             progress (try setoid_rewrite H in H';
                       try setoid_rewrite H)
           | [ H: pointwise_relation _ _ _ _, H': _ |- _ ] =>
             progress (try setoid_rewrite H in H';
                       try setoid_rewrite H)
           | [ H: _ _ _, H': _ |- _ ] =>
             progress (try setoid_rewrite H in H';
                       try setoid_rewrite H)
         end.

Add Parametric Morphism elt welt :
  (@Subset elt welt)
    with signature (StringMap.Equal ==> StringMap.Equal ==> pointwise_relation _ (@eq _) ==> iff)
      as Subset_morphism.
  unfold Subset; intros; rewrite_Eq_in_all; reflexivity.
Qed. 
  
Add Parametric Morphism {av} :
  (@SomeSCAs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SomeSCAs_morphism.
Proof.
  unfold SomeSCAs; intros; apply Subset_morphism; intuition.
Qed.

Add Parametric Morphism {av} :
  (@AllADTs av)
    with signature (StringMap.Equal ==> StringMap.Equal ==> iff)
      as SomeADTs_morphism.
Proof.
  unfold AllADTs; intros * eq1 * eq2.
  split; intros (? & ?); split;
  rewrite !eq1, !eq2 in *; assumption.
Qed.

Lemma Subset_reflexive :
  forall {elt welt} st wrapper,
    @Subset elt welt st st wrapper.
Proof.
  firstorder.
Qed.

Lemma SomeSCAs_reflexive :
  forall {av} st,
    @SomeSCAs av st st.
Proof.
  firstorder.
Qed.

Lemma Subset_transitive :
  forall {elt welt} s1 s2 s3 wrapper,
    @Subset elt welt s1 s2 wrapper ->
    @Subset elt welt s2 s3 wrapper ->
    @Subset elt welt s1 s3 wrapper.
Proof.
  firstorder.
Qed.

Lemma SomeSCAs_transitive :
  forall {av} s1 s2 s3,
    @SomeSCAs av s1 s2 ->
    @SomeSCAs av s2 s3 ->
    @SomeSCAs av s1 s3.
Proof.
  firstorder.
Qed.

Lemma Subset_chomp :
  forall {elt welt} {k v state map} wrapper,
    @Subset elt welt state map wrapper ->
    @Subset elt welt ([k >> wrapper v]::state) ([k >> wrapper v]::map) wrapper.
Proof.
  unfold Subset; intros * h ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k');
    subst; rewrite StringMapFacts.add_mapsto_iff in *;
    intuition.
Qed.

Lemma SomeSCAs_chomp :
  forall {av} (state: State av) k v scas,
    SomeSCAs state scas ->
    SomeSCAs ([k >sca> v]::state) ([k >sca> v]::scas).
Proof.
  intros *; apply Subset_chomp.
Qed.

Lemma AllADTs_chomp :
  forall {av} (state: State av) k v adts,
    AllADTs state adts ->
    AllADTs ([k >adt> v]::state) ([k >adt> v]::adts).
Proof.
  unfold AllADTs; split; apply Subset_chomp; tauto.
Qed.

Lemma Subset_chomp_remove :
  forall {elt welt} {k v state map} wrapper,
    @Subset elt welt (StringMap.remove k state) (StringMap.remove k map) wrapper ->
    @Subset elt welt ([k >> wrapper v]::state) ([k >> wrapper v]::map) wrapper.
Proof.
  unfold Subset; intros * h ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k');
    subst; rewrite StringMapFacts.add_mapsto_iff in *;
    setoid_rewrite StringMapFacts.remove_mapsto_iff in h;
    intuition.
Qed.

Lemma SomeSCAs_chomp_remove :
  forall {av} (state: State av) k v scas,
    SomeSCAs (StringMap.remove k state) (StringMap.remove k scas) ->
    SomeSCAs ([k >sca> v]::state) ([k >sca> v]::scas).
Proof.
  intros *; apply Subset_chomp_remove.
Qed.

Lemma AllADTs_chomp_remove :
  forall {av} (state: State av) k v adts,
    AllADTs (StringMap.remove k state) (StringMap.remove k adts) ->
    AllADTs ([k >adt> v]::state) ([k >adt> v]::adts).
Proof.
  unfold AllADTs; split; apply Subset_chomp_remove; tauto.
Qed.

Lemma AllADTs_equiv :
  forall {av} (state bindings: State av),
    AllADTs state bindings <->
    (forall k v, StringMap.MapsTo k (Facade.ADT v) bindings <-> StringMap.MapsTo k (Facade.ADT v) state).
Proof.
  firstorder.
Qed.

Lemma add_adts_pop_sca :
  forall {av} k v map (state: State av),
    ~ StringMap.In k map ->
    AllADTs state map ->
    AllADTs ([k >sca> v]::state) map.
Proof.
  setoid_rewrite AllADTs_equiv.
  intros ** k' v'.
  destruct (StringMap.E.eq_dec k k'); subst;
  split; intros H';
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac.

  apply StringMapFacts.MapsTo_In in H'; congruence.
  intuition; discriminate.

  rewrite H0 in *; intuition.
  rewrite H0 in *; intuition.
Qed.

Lemma add_sca_pop_adts :
  forall {av} k v map (state: State av),
    ~ StringMap.In k map ->
    SomeSCAs state map ->
    SomeSCAs ([k >adt> v]::state) map.
Proof.
  intros ** k' v'.
  destruct (StringMap.E.eq_dec k k'); subst;
  intros H';
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac.

  apply StringMapFacts.MapsTo_In in H'; congruence.
  intuition; discriminate.
Qed.

Lemma Subset_swap_left :
  forall {elt welt} {k1 k2 v1 v2 state map} wrapper,
    k1 <> k2 ->
    @Subset elt welt ([k1 >> v1]::[k2 >> v2]::state) map wrapper ->
    @Subset elt welt ([k2 >> v2]::[k1 >> v1]::state) map wrapper.
Proof.
  unfold Subset; intros ** k v mp.
  destruct (StringMap.E.eq_dec k k1), (StringMap.E.eq_dec k k2);
    subst; map_iff_solve idtac; try discriminates;
    specialize (H0 _ _ mp);
    repeat setoid_rewrite StringMapFacts.add_mapsto_iff in H0;
    intuition.
Qed.

Lemma MapsTo_swap :
  forall {elt} {k1 k2 v1 v2} {map: StringMap.t elt},
    k1 <> k2 ->
    forall k v,
      ([k1 >> v1]::[k2 >> v2]::map)[k >> v] <->
      ([k2 >> v2]::[k1 >> v1]::map)[k >> v].
Proof.
  intros; StringMapFacts.map_iff.
  destruct (StringMap.E.eq_dec k k1) as [ eq0 | neq0 ];
    destruct (StringMap.E.eq_dec k k2) as [ eq1 | neq1 ];
    try rewrite !eq0 in *;
    try rewrite !eq1 in *;
    split; intros;
    map_iff_solve' idtac;
    intuition.
Qed.

Lemma Subset_swap_right :
  forall {elt welt} {k1 k2 v1 v2 state map} wrapper,
    k1 <> k2 ->
    @Subset elt welt map ([k1 >> v1]::[k2 >> v2]::state) wrapper ->
    @Subset elt welt map ([k2 >> v2]::[k1 >> v1]::state) wrapper.
Proof.
  unfold Subset; intros ** k v mp.
  destruct (StringMap.E.eq_dec k k1), (StringMap.E.eq_dec k k2);
    subst; map_iff_solve idtac; try discriminates;
    rewrite MapsTo_swap in mp by auto; specialize (H0 _ _ mp);
    repeat setoid_rewrite StringMapFacts.add_mapsto_iff in H0;
    intuition.
Qed.

Lemma AllADTs_swap :
  forall {av} {state: State av} {k1 k2 v1 v2 map},
    k1 <> k2 ->
    @AllADTs av ([k1 >> v1]::[k2 >> v2]::state) map ->
    @AllADTs av ([k2 >> v2]::[k1 >> v1]::state) map.
Proof.
  unfold AllADTs; intros; split; destruct_pairs.
  apply Subset_swap_left; trivial.
  apply Subset_swap_right; trivial.
Qed.

Lemma mapM_MapsTo_1 :
  forall av st k v,
    st [k >> v] ->
    mapM (@sel av st) (k :: nil) = Some (v :: nil).
Proof.
  unfold sel; intros; simpl.
  subst_find; reflexivity.
Qed.

Lemma Subset_mapsto' :
  forall {elt welt} k v st map wrapper,
    @Subset elt welt st map wrapper ->
    map[k >> wrapper v] ->
    st[k >> wrapper v].
Proof.
  unfold Subset; intros * h ** maps_to.
  apply (h _ _ maps_to).
Qed.

Lemma AllADTs_mapsto' :
  forall {av} k v st adts,
    @AllADTs av st adts ->
    adts[k >> Facade.ADT v] ->
    st[k >> Facade.ADT v].
Proof.
  intros * (h & _) **. eauto using Subset_mapsto'. 
Qed.

Lemma SomeSCAs_mapsto' :
  forall {av} k v st scas,
    @SomeSCAs av st scas ->
    scas[k >> Facade.SCA _ v] ->
    st[k >> Facade.SCA _ v].
Proof.
  eauto using Subset_mapsto'.
Qed.

Lemma Subset_add_in_left :
  forall {elt welt} st bindings k v wrapper,
    bindings[k >> wrapper v] ->
    @Subset elt welt st bindings wrapper ->
    Subset ([k >> wrapper v]::st) bindings wrapper.
Proof.
  unfold Subset; intros ** k' v' ? .
  destruct (StringMap.E.eq_dec k k'); subst;
  try match goal with (* TODO fix mapsto_unique *) 
        | H:(?st) [?k >> ?v], H':(?st) [?k >> ?v'] |- _ =>
          let h := fresh in
          pose proof (MapsTo_unique st k v v' H H') as h;
            rewrite !h in *; clear H
      end; map_iff_solve intuition.
Qed.

Lemma Subset_add_in_right :
  forall {elt welt} st bindings k v wrapper,
    st[k >> wrapper v] ->
    @Subset elt welt st bindings wrapper ->
    Subset st ([k >> wrapper v]::bindings) wrapper.
Proof.
  unfold Subset; intros ** k' v' ? .
  destruct (StringMap.E.eq_dec k k'); subst;
  try match goal with (* TODO fix mapsto_unique *) 
        | H:(?st) [?k >> ?v], H':(?st) [?k >> ?v'] |- _ =>
          let h := fresh in
          pose proof (MapsTo_unique st k v v' H H') as h;
            rewrite !h in *; clear H
      end;
  map_iff_solve intuition;
  rewrite StringMapFacts.add_mapsto_iff in *; intuition;
  match goal with
    | H: wrapper _ = wrapper _ |- _ => rewrite H in *
  end; intuition.
Qed.

Lemma AllADTs_add_in :
  forall {av} st bindings k v,
    bindings[k >> @Facade.ADT av v] ->
    AllADTs st bindings ->
    AllADTs ([k >> Facade.ADT v]::st) bindings.
Proof.
  unfold AllADTs; split; intros;
  destruct_pairs; eauto using Subset_add_in_left, Subset_add_in_right.
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

Ltac subsets_mapsto H mapsto remove swap_remove :=
  progress (let maps_to := fresh "maps_to" in
            let superset := fresh "superset" in
            pose proof mapsto as maps_to;
            pose proof remove as superset;
            try (apply swap_remove in superset; [ | solve [auto] ]);
            clear_dups).

Ltac scas_adts_mapsto :=
  repeat match goal with
           | [ H: SomeSCAs ?state ([?k >sca> ?v]::?map) |- _ ] =>
             subsets_mapsto H (SomeSCAs_mapsto H) (SomeSCAs_remove H) @SomeSCAs_swap_remove
           | [ H: AllADTs ?state ([?k >adt> ?v]::?map) |- _ ] =>
             subsets_mapsto H (AllADTs_mapsto H) (AllADTs_remove H) @Subset_swap_remove
           | [ H: Subset ?state ([?k >> ?wrapper ?v]::?map) ?wrapper |- _ ] =>
             subsets_mapsto H (Subset_mapsto _ H) (Subset_remove _ H) @Subset_swap_remove
           | [ H: ?adts[?k >> ?v], H': AllADTs ?state ?adts |- _ ] =>
             progress (pose proof (AllADTs_mapsto' _ _ _ _ H' H); clear_dups)
           | [ H: ?scas[?k >> ?v], H': SomeSCAs ?state ?adts |- _ ] =>
             progress (pose proof (SomeSCAs_mapsto' _ _ _ _ H' H); clear_dups)
           | [ H: ?scas[?k >> ?v], H': SomeSCAs ?state ?adts |- _ ] =>
             progress (pose proof (Subset_mapsto' _ _ _ _ H' H); clear_dups)
         end.

Ltac rewrite_Eq_in_goal :=
  match goal with
    | [ H: StringMap.Equal _ _ |- SomeSCAs _ _ ] =>
      rewrite H
    | [ H: StringMap.Equal _ _ |- AllADTs _ _ ] =>
      rewrite H
    | [ H: StringMap.Equal _ _ |- StringMap.MapsTo _ _ _ ] =>
      rewrite H              
  end.

(* Additional morphisms *)

Add Parametric Morphism av env :
  (@Prog av env)
    with signature (iff ==> StringMap.Equal ==> StringMap.Equal ==> StringMap.Equal ==> StringMap.Equal ==> refine)
      as Prog_morphism.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  constructor; intros; destruct_pairs.
  
  rewrite_Eq_in_all; split; intros;
  specialize_states; intuition.
Qed.

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
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
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
        scas_adts_mapsto; (* Extract value of vtest *)
        first [ assumption | eapply BoolToW_eval; trivial] ].
  
  (* RunsTo *)
  intros;
    repeat inversion_facade;
    unfold is_true, is_false in *;
    destruct test;
    and_eq_refl;
    specialize_states;
    scas_adts_mapsto;
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
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  scas_adts_mapsto.

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
    scas_adts_mapsto;
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
  unfold refine, Prog, ProgOk; unfold_coercions; intros.
  inversion_by computes_to_inv; constructor;
  split; subst; destruct_pairs.

  (* Safe *)

  repeat (safe_seq; intros).
  specialize_states.
  scas_adts_mapsto.

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
    scas_adts_mapsto;
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
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  apply eq_ret_compute.

  pose proof I.
  pose proof (SomeSCAs_empty init_state).
  specialize_states.
  scas_adts_mapsto.
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
  unfold Prog, ProgOk, refine; unfold_coercions; intros;
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
  unfold Prog, ProgOk, refine; intros.
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
      solve [unfold AllADTs, Subset; intros; map_iff_solve intuition]
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

  rewrite drop_sca; vacuum. (* NOTE: Could also generalize compile_constant *)
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
      ((ret = SCAZero /\ seq <> nil) \/ (ret = SCAOne /\ seq = nil)) /\
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

Definition SCALoopBodyProgCondition env loop compiled_loop knowledge scas adts (vseq vret thead tis_empty: StringMap.key) (acc head: W) (seq: list W) :=
  @ProgOk _ env compiled_loop knowledge
          ([thead >sca> head]::[tis_empty >sca> 0]::[vret >sca> acc]::scas) ([vret >sca> loop acc head]::scas)
          ([vseq >adt> List seq]::adts) ([vseq >adt> List seq]::adts).
          
Definition SCALoopBodyOk env loop compiled_loop knowledge scas adts (vseq vret thead tis_empty: StringMap.key) :=
  forall (acc: W) (head: W) (seq: list W),
    SCALoopBodyProgCondition env loop compiled_loop knowledge scas adts vseq
                             vret thead tis_empty acc head seq.
    
Lemma safe_call_1 :
  forall {av} env state adts pointer spec varg arg vout,
    state[varg >> arg] ->
    Word2Spec env pointer = Some (Axiomatic spec) ->
    AllADTs state adts -> 
    ~ StringMap.In (elt:=Value av) vout adts ->
    PreCond spec (arg :: nil) ->
    @Safe av env (Call vout (Const pointer) (varg :: nil)) state.
Proof.
  intros.
  econstructor.

  repeat constructor; intuition. (* NoDup *)
  reflexivity.
  eassumption.
  unfold sel; simpl; subst_find; reflexivity.
  eapply not_in_adts_not_mapsto_adt; eassumption.
  assumption.
Qed.

Lemma weqb_false :
  forall w1 w2,
    w1 <> w2 ->
    IL.weqb w1 w2 = false.
Proof.
  setoid_rewrite <- weqb_false_iff.
  intros; assumption.
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

Ltac compile_fold_induction_is_empty_call :=
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H;
        try eassumption;
        [ let H1 := fresh in
          destruct H as [ ? ([ (H & H1) | (H & H1) ] & ?) ];
            try solve [exfalso; apply H1; reflexivity]; subst
        | intuition .. ]
  end.

Lemma weqb_refl :
  forall sz w,
    @Word.weqb sz w w = true.
Proof.
  induction w.
  
  reflexivity.
  destruct b; simpl; rewrite IHw; reflexivity.
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
  
Lemma mapsto_eq_add :
  forall {elt} m k (v: elt) m',
    StringMap.Equal m ([k >> v]::m') ->
    m[k >> v].
Proof.
  intros; rewrite_Eq_in_goal; map_iff_solve intuition.
Qed.

Ltac mapsto_eq_add :=
  match goal with
    | [ H: StringMap.Equal _ _ |- _ ] =>
      let H' := fresh in
      pose proof H as H';
        apply mapsto_eq_add in H'
  end.
  
Lemma Subset_replace_right :
  forall {elt welt} k v v' state map wrapper,
    @Subset elt welt state ([k >> v]::map) wrapper ->
    @Subset elt welt ([k >> v']::state) ([k >> v']::map) wrapper.
Proof.
  unfold Subset; intros ** k'' v'' maps_to.
  destruct (StringMap.E.eq_dec k k''); subst;
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac; [ | apply H ];
  map_iff_solve intuition.
Qed.

Lemma Subset_replace_left :
  forall {elt welt} k v v' state map wrapper,
    @Subset elt welt ([k >> v]::state) map wrapper ->
    @Subset elt welt ([k >> v']::state) ([k >> v']::map) wrapper.
Proof.
  unfold Subset; intros ** k'' v'' maps_to.
  destruct (StringMap.E.eq_dec k k''); subst;
  rewrite StringMapFacts.add_mapsto_iff in *;
  map_iff_solve idtac; intuition.
  specialize (H _ _ H2);
    rewrite StringMapFacts.add_mapsto_iff in *;
    intuition.
Qed.

Lemma AllADTs_replace :
  forall {av} k v v' state map,
    @AllADTs av state ([k >> v]::map) ->
    @AllADTs av ([k >> v']::state) ([k >> v']::map).
Proof.
  unfold AllADTs; split; intros;
  [ eapply Subset_replace_right
  | eapply Subset_replace_left ];
  intuition eassumption.
Qed.

Add Parametric Morphism {av k v} :
  (StringMap.add k v)
    with signature (@AllADTs av ==> @AllADTs av)
      as StringMap_add_AllADTs.
Proof.
  unfold AllADTs, Subset; intros; split; intros;
  generalize H0; StringMapFacts.map_iff; intuition.
Qed.

Ltac trickle_deletion :=
  repeat match goal with
           | [ |- context[StringMap.remove ?k (StringMap.add ?k' ?v ?m)] ] =>
             first [rewrite (@StringMap_remove_add_eq _ k' k) by congruence |
                    rewrite (@StringMap_remove_add_neq _ k' k) by congruence ]
           | [ |- context[StringMap.remove _ ∅] ] => rewrite StringMap_remove_empty
         end.

Lemma AllADTs_swap_iff :
  forall (av : Type) (state : State av) (k1 k2 : StringMap.key)
         (v1 v2 : Value av) (map : StringMap.t (Value av)),
    k1 <> k2 ->
    (AllADTs ([k1 >> v1]::[k2 >> v2]::state) map <->
     AllADTs ([k2 >> v2]::[k1 >> v1]::state) map).
Proof.
  split; eauto using AllADTs_swap.
Qed.
  
Add Parametric Relation {av} : (State av) (@AllADTs av)
    reflexivity proved by _
    symmetry proved by _
    transitivity proved by _
      as all_adts. 
Proof.
  firstorder.
  firstorder.
  firstorder.
Qed.

Lemma AllADTs_swap_left_iff :
  forall (av : Type) (state : State av) (k1 k2 : StringMap.key)
         (v1 v2 : Value av) (map : StringMap.t (Value av)),
    k1 <> k2 ->
    (AllADTs map ([k1 >> v1]::[k2 >> v2]::state) <->
     AllADTs map ([k2 >> v2]::[k1 >> v1]::state)).
Proof.
  split; intros; symmetry; apply AllADTs_swap; try symmetry; try congruence.
Qed.

Add Parametric Morphism av :
  (@AllADTs av)
    with signature (@AllADTs av ==> @AllADTs av ==> iff)
      as AllADTs_AllADTs_morphism.
  firstorder.
Qed.

Ltac loop_body_prereqs :=
  split; [assumption|split];
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_pop in H; try eauto;
      rewrite_Eq_in_goal;
      try map_iff_solve ltac:(intuition eassumption)
  end;
  rewrite_Eq_in_goal;
  [ apply Subset_swap_left; auto;
    apply add_sca_pop_adts; map_iff_solve idtac; auto;
    repeat apply SomeSCAs_chomp;
    eassumption
  | apply add_adts_pop_sca; try assumption;
    map_iff_solve intuition;
    apply AllADTs_swap; auto;
    apply add_adts_pop_sca; auto;
    map_iff_solve intuition;
    first [ eapply AllADTs_replace;
            eassumption
          | match goal with
              | [ H: AllADTs ?state ?adts |- AllADTs _ _ ] =>
                rewrite H, AllADTs_swap_left_iff by congruence;
                  apply AllADTs_chomp_remove;
                  trickle_deletion;
                  apply AllADTs_chomp;
                  reflexivity
            end ]
  ].
  
Lemma SafeEnv_inv :
  forall {av env} {a b : Stmt} {st st' : State av},
    RunsTo env a st st' ->
    Safe env (Seq a b) st ->
    Safe env b st'.
Proof.    
  intros * h' h; inversion h. intuition.
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

Definition compile_fold_base_sca :
  forall {env},
  forall {vseq vret: StringMap.key},
  forall {thead tis_empty: StringMap.key},
  forall {ppop pempty},
  forall {loop compiled_loop},
  forall {knowledge scas adts},
    SCALoopBodyOk env loop compiled_loop knowledge scas adts vseq vret thead tis_empty ->
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    forall seq init, 
      refine (@Prog _ env knowledge
                    ([vret >sca> init]::scas) ([tis_empty >sca> 1]::[vret >sca> List.fold_left loop seq init]::scas)
                    ([vseq >adt> List seq]::adts) ([vseq >adt> List nil]::adts))
             (ret (Fold thead tis_empty vseq ppop pempty compiled_loop)).
Proof.
  unfold SCALoopBodyOk, SCALoopBodyProgCondition, Prog, ProgOk, refine; unfold_coercions;
  induction seq as [ | a seq ]; intros;
  [ | specialize (fun init => IHseq init _ (eq_ret_compute _ _ _ (eq_refl))) ];
  constructor; intros; destruct_pairs;
  split;
  inversion_by computes_to_inv;
  subst;
  scas_adts_mapsto.
 
  (** Safe **)
  constructor.
  split; intros.

  (* Call is safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* (Non-running) loop is safe *)

  compile_fold_induction_is_empty_call.
  eapply SafeWhileFalse.
  eapply BoolToW_eval;
    [ reflexivity | rewrite_Eq_in_goal; map_iff_solve intuition ].

  (** RunsTo **)
  unfold Fold; intros; do 2 inversion_facade;
  try compile_fold_induction_is_empty_call;
  simpl;
  scas_adts_mapsto;
  mapsto_eq_add;
  try (match goal with
         | [ H: is_true _ _ |- _ ] => apply is_true_eq in H
       end; auto_mapsto_unique).

  split; rewrite_Eq_in_goal; map_iff_solve idtac.
  apply SomeSCAs_chomp; assumption.
  apply add_adts_pop_sca; [ map_iff_solve intuition | assumption ].

  (** Induction's safety **)
  constructor; split.

  (* Call safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* Loop safe *)
  intros.
  compile_fold_induction_is_empty_call; try discriminate.
  mapsto_eq_add.
  
  constructor;
    [ unfold_coercions;
      rewrite is_true_eq;
      assumption | | ].
  
  constructor; split.

  (* Pop safe *)
  assert (st' [vseq >> Facade.ADT (List (a :: seq))]) 
    by (rewrite_Eq_in_goal; map_iff_solve intuition).

  eapply safe_call_1.
  eassumption.
  eassumption.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca;
    [ | eassumption | .. ];
    map_iff_solve intuition.
  map_iff_solve intuition.
  simpl. eexists. eexists. reflexivity.

  intros.
  constructor.

  (* Loop body + next statement safe *)

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _))
               |- context[RunsTo _ ?compiled_loop ?initial _] ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.
  
  (* Loop body *)
  split.
  eauto.

  (* next statement *)
  intros.
  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  scas_adts_mapsto.
  eapply safe_call_1; try eassumption.
  map_iff_solve congruence.
  simpl; eexists; reflexivity.

  (* Actual loop induction *)
  intros.

  do 2 inversion_facade.

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  match goal with
    | [ H: RunsTo _ _ _ ?st |- Safe env _ ?st ] => apply (SafeEnv_inv H)
  end.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.
  match goal with
    | [ H: context[Fold] |- _ ] => unfold Fold in H; apply H
  end.

  tauto.

  (* Induction case for the loop *)
  simpl; intros.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.

  (* initial_state is at the very beginning of the loop.  We need to unfold one
     iteration first, and then deduce the new states *)

  unfold Fold in *.
  inversion_facade.

  (* TODO: This is a dupe of part of the loop_body_prereqs code *)
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H; eauto;
      destruct H as [ret (ret_val & state_eq)];
      destruct ret_val; destruct_pairs; try discriminate (* Remove the list empty case *)
  end.

  assert (is_true st' (tis_empty = 0)%facade) by
      (unfold_coercions; rewrite is_true_eq;
       rewrite_Eq_in_goal;
       map_iff_solve intuition). (* TODO this should be a lemma *)

  inversion_facade; try (exfalso; eapply true_and_false; eassumption).
  
  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  repeat match goal with
           | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] =>
             inversion_clear' H
         end.

  (* Copied from earlier *)
  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H'); pose H
         end.
  (* </Copied> *)

  (* Stick together the last statement and the body of the loop *)
  match goal with
    | [ Hlast: RunsTo _ _ ?initial_state ?st, Hloop: RunsTo _ (Facade.While _ _) ?st ?final_state |- _ ] =>
      pose proof (RunsToSeq Hlast Hloop)
  end.
  specialize_states.
  split; intuition.
Qed.

Definition ADTLoopBodyProgCondition env {acc_type} loop compiled_loop knowledge scas adts (vseq vret thead tis_empty: StringMap.key) (acc: acc_type) wrapper (head: W) (seq: list W) :=
  @ProgOk _ env compiled_loop knowledge
          ([thead >sca> head]::[tis_empty >sca> 0]::scas) (scas)
          ([vret >adt> wrapper acc]::[vseq >adt> List seq]::adts) ([vret >adt> wrapper (loop acc head)]::[vseq >adt> List seq]::adts).

Definition ADTLoopBodyOk env {acc_type} loop compiled_loop knowledge scas adts (vseq vret thead tis_empty: StringMap.key) wrapper :=
  forall acc (head: W) (seq: list W),
    @ADTLoopBodyProgCondition env acc_type loop compiled_loop knowledge scas adts vseq
                              vret thead tis_empty acc wrapper head seq.

Definition compile_fold_base_adt :
  forall {env},
  forall {acc_type wrapper},
  forall {vseq vret: StringMap.key},
  forall {thead tis_empty: StringMap.key},
  forall {ppop pempty},
  forall {loop compiled_loop},
  forall {knowledge scas adts},
    @ADTLoopBodyOk env acc_type loop compiled_loop knowledge scas adts vseq vret thead tis_empty wrapper ->
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    forall seq (init: acc_type), 
      refine (@Prog _ env knowledge
                    (scas) ([tis_empty >sca> 1]::scas)
                    ([vret >adt> wrapper init]::[vseq >adt> List seq]::adts) ([vret >adt> wrapper (List.fold_left loop seq init)]::[vseq >adt> List nil]::adts))
             (ret (Fold thead tis_empty vseq ppop pempty compiled_loop)).
Proof.
  unfold ADTLoopBodyOk, ADTLoopBodyProgCondition, Prog, ProgOk, refine; unfold_coercions;
  induction seq as [ | a seq ]; intros;
  [ | specialize (fun init => IHseq init _ (eq_ret_compute _ _ _ (eq_refl))) ];
  constructor; intros; destruct_pairs;
  split;
  inversion_by computes_to_inv;
  subst;
  scas_adts_mapsto.
  
  (** Safe **)
  constructor.
  split; intros.

  (* Call is safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].
  
  (* (Non-running) loop is safe *)

  compile_fold_induction_is_empty_call.
  eapply SafeWhileFalse.
  eapply BoolToW_eval;
    [ reflexivity | rewrite_Eq_in_goal; map_iff_solve intuition ].

  (** RunsTo **)
  unfold Fold; intros; do 2 inversion_facade;
  try compile_fold_induction_is_empty_call;
  simpl;
  scas_adts_mapsto;
  mapsto_eq_add;
  try (match goal with
         | [ H: is_true _ _ |- _ ] => apply is_true_eq in H
       end; auto_mapsto_unique).

  split; rewrite_Eq_in_goal; map_iff_solve idtac.
  apply SomeSCAs_chomp; assumption.
  apply add_adts_pop_sca; [ map_iff_solve intuition | assumption ].

  (** Induction's safety **)
  constructor; split.

  (* Call safe *)
  eapply safe_call_1;
    first [ eassumption
          | symmetry; eassumption
          | simpl; eexists; reflexivity
          | map_iff_solve intuition ].

  (* Loop safe *)
  intros.
  compile_fold_induction_is_empty_call; try discriminate.
  mapsto_eq_add.
  
  constructor;
    [ unfold_coercions;
      rewrite is_true_eq;
      assumption | | ].
  
  constructor; split.

  (* Pop safe *)
  assert (st' [vseq >> Facade.ADT (List (a :: seq))]) 
    by (rewrite_Eq_in_goal; map_iff_solve intuition).

  eapply safe_call_1.
  eassumption.
  eassumption.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca;
    [ | eassumption | .. ];
    map_iff_solve intuition.
  map_iff_solve intuition.
  simpl. eexists. eexists. reflexivity.

  intros.
  constructor.

  (* Loop body + next statement safe *)

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _))
               |- context[RunsTo _ ?compiled_loop ?initial _] ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.
  
  (* Loop body *)
  split.
  eauto.

  (* next statement *)
  intros.
  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  scas_adts_mapsto.
  eapply safe_call_1; try eassumption.
  map_iff_solve congruence.
  simpl; eexists; reflexivity.

  (* Actual loop induction *)
  intros.

  do 2 inversion_facade.

  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H')
         end.

  match goal with
    | [ H: RunsTo _ _ _ ?st |- Safe env _ ?st ] => apply (SafeEnv_inv H)
  end.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.
  match goal with
    | [ H: context[Fold] |- _ ] => unfold Fold in H; apply H
  end.

  tauto.

  (* Induction case for the loop *)
  simpl; intros.
  specialize (IHseq (loop init a)); inversion_by computes_to_inv.

  (* initial_state is at the very beginning of the loop.  We need to unfold one
     iteration first, and then deduce the new states *)

  unfold Fold in *.
  inversion_facade.

  (* TODO: This is a dupe of part of the loop_body_prereqs code *)
  match goal with
    | [ H: RunsTo _ (Call _ _ _) _ _ |- _ ] =>
      eapply runsto_is_empty in H; eauto;
      destruct H as [ret (ret_val & state_eq)];
      destruct ret_val; destruct_pairs; try discriminate (* Remove the list empty case *)
  end.

  assert (is_true st' (tis_empty = 0)%facade) by
      (unfold_coercions; rewrite is_true_eq;
       rewrite_Eq_in_goal;
       map_iff_solve intuition). (* TODO this should be a lemma *)

  inversion_facade; try (exfalso; eapply true_and_false; eassumption).
  
  (* Unfold one loop iteration, but keep the last statement, and merge it back at the beginning of the while, to recreate the induction condition. *)

  repeat match goal with
           | [ H: RunsTo _ (Seq _ _) _ _ |- _ ] =>
             inversion_clear' H
         end.

  (* Copied from earlier *)
  repeat match goal with
           | [ H: (forall acc head seq initial_state,
                     _ -> (forall final_state, RunsTo _ ?compiled_loop _ _ -> _)),
               H': RunsTo _ ?compiled_loop ?initial _ |- _ ] =>
             specialize (fun p final => H init a seq initial p final);
               match type of H with
                 | ?cond -> _ => try pose cond as prereq
               end
         end.

  assert (prereq) as prereqs; unfold prereq in *; clear prereq.
  loop_body_prereqs.

  repeat match goal with
           | [ H: _ -> (forall final_state, _ -> _),
               H': RunsTo _ compiled_loop _ _ |- _ ] => specialize (H prereqs _ H'); pose H
         end.
  (* </Copied> *)

  (* Stick together the last statement and the body of the loop *)
  match goal with
    | [ Hlast: RunsTo _ _ ?initial_state ?st, Hloop: RunsTo _ (Facade.While _ _) ?st ?final_state |- _ ] =>
      pose proof (RunsToSeq Hlast Hloop)
  end.
  specialize_states.
  split; intuition.
Qed.

Lemma PickComputes_inv: forall {A} (x: A) P,
                          computes_to (Pick (fun x => P x)) x -> P x.
Proof.
  intros; inversion_by computes_to_inv; assumption.
Qed.

Lemma map_add_remove_swap :
  forall {elt} k1 k2 v m,
    k1 <> k2 ->
    @StringMap.Equal elt
                     ([k1 >> v]::(StringMap.remove k2 m))
                     (StringMap.remove k2 ([k1 >> v]::m)).
Proof.
  intros; red; intros k3.
  map_iff_solve idtac.

  repeat (rewrite ?StringMapFacts.add_o;
          rewrite ?StringMapFacts.remove_o).
  destruct (StringMap.E.eq_dec k1 k3), (StringMap.E.eq_dec k2 k3);
    subst; congruence.
Qed.

Lemma compile_fold_sca :
  forall env,
  forall vseq vret: StringMap.key,
  forall thead tis_empty: StringMap.key,
  forall ppop pempty,
  forall loop,
  forall knowledge scas adts,
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    ~ StringMap.In tis_empty scas ->
    forall seq init, 
      refine (@Prog _ env knowledge
                    (scas) ([vret >sca> List.fold_left loop seq init]::scas)
                    ([vseq >adt> List seq]::adts) ([vseq >adt> List nil]::adts))
             (cloop <- { cloop | SCALoopBodyOk env loop cloop knowledge
                                               scas adts vseq vret thead tis_empty };
              pinit <- (@Prog _ env knowledge
                              scas ([vret >sca> init]::scas)
                              ([vseq >adt> List seq]::adts) ([vseq >adt> List seq]::adts));
              ret (pinit; Fold thead tis_empty vseq ppop pempty cloop)%facade)%comp.
Proof.
  unfold refine; intros.
  inversion_by computes_to_inv;
    subst;
    constructor;
    match goal with
      | [ H: _ |- _ ] => apply PickComputes_inv in H; unfold ProgOk in H
    end; unfold ProgOk in * ;
    intros; destruct_pairs;
    specialize_states;
    destruct_pairs.

  match goal with
    | [ H: context[SCALoopBodyOk], H': context[Word2Spec], H'': context[Word2Spec] |- _ ] =>
      pose proof (compile_fold_base_sca H H' H'')
  end.
  
  (* TODO: Tactic for this? *)
  repeat match goal with
           | [ H: ?a -> _, H': ?a |- _ ] =>
             match (type of a) with
               | Prop => specialize (H H')
             end
         end.

  unfold refine, Prog, ProgOk in *.

  match goal with
    | [ H: _ -> _ -> _ |- _ ] => specialize (H seq init _ (eq_ret_compute _ _ _ (eq_refl)))
  end.
  inversion_by computes_to_inv.
  
  split.

  (* Safe *)
  constructor; split; intuition.

  (* RunsTo *)
  intros; destruct_pairs.
  inversion_facade.
  specialize_states.
  split; [ | intuition ].
  
  (* Tricks to get rid of is_empty *)
  rewrite (not_in_remove_eq tis_empty scas); eauto.
  rewrite map_add_remove_swap; eauto.
  eapply SomeSCAs_remove; eauto.
Qed.

Lemma compile_fold_adt :
  forall env,
  forall acc_type wrapper,
  forall vseq vret: StringMap.key,
  forall thead tis_empty: StringMap.key,
  forall ppop pempty,
  forall loop,
  forall knowledge scas adts,
    (Word2Spec env pempty = Some (Axiomatic List_empty)) ->
    (Word2Spec env ppop  = Some (Axiomatic List_pop)) ->
    vret <> vseq ->
    vret <> tis_empty ->
    thead <> vret ->
    thead <> vseq ->
    tis_empty <> vseq ->
    ~ StringMap.In thead adts ->
    ~ StringMap.In tis_empty adts ->
    ~ StringMap.In vseq scas ->
    ~ StringMap.In tis_empty scas ->
    forall seq init, 
      refine (@Prog _ env knowledge
                    (scas) (scas)
                    ([vseq >adt> List seq]::adts) ([vret >adt> wrapper (List.fold_left loop seq init)]
                                                     ::[vseq >adt> List nil]::adts))
             (cloop <- { cloop | @ADTLoopBodyOk env acc_type loop cloop knowledge
                                                scas adts vseq vret thead tis_empty wrapper };
              pinit <- (@Prog _ env knowledge
                              scas scas
                              ([vseq >adt> List seq]::adts) ([vret >adt> wrapper init]::[vseq >adt> List seq]::adts));
              ret (pinit; Fold thead tis_empty vseq ppop pempty cloop)%facade)%comp.
Proof.
  unfold refine; intros.
  inversion_by computes_to_inv;
    subst;
    constructor;
    match goal with
      | [ H: _ |- _ ] => apply PickComputes_inv in H; unfold ProgOk in H
    end; unfold ProgOk in * ;
    intros; destruct_pairs;
    specialize_states;
    destruct_pairs.

  match goal with
    | [ H: context[ADTLoopBodyOk], H': context[Word2Spec], H'': context[Word2Spec] |- _ ] =>
      pose proof (compile_fold_base_adt H H' H'')
  end.
  
  (* TODO: Tactic for this? *)
  repeat match goal with
           | [ H: ?a -> _, H': ?a |- _ ] =>
             match (type of a) with
               | Prop => specialize (H H')
             end
         end.

  unfold refine, Prog, ProgOk in *.

  match goal with
    | [ H: _ -> _ -> _ |- _ ] => specialize (H seq init _ (eq_ret_compute _ _ _ (eq_refl)))
  end.
  inversion_by computes_to_inv.
  
  split.

  (* Safe *)
  constructor; split; intuition.

  (* RunsTo *)
  intros; destruct_pairs.
  inversion_facade.
  specialize_states.
  split; [ | intuition ].
  
  (* Tricks to get rid of is_empty *)
  rewrite (not_in_remove_eq tis_empty scas); eauto.
  (* REMOVED rewrite map_add_remove_swap; eauto. *)
  eapply SomeSCAs_remove; eauto.
Qed.

Lemma mapsto_eval :
  forall {av} scas k w,
    (scas) [k >> SCA av w] ->
    eval scas k = Some (SCA av w).
Proof.
  intros; simpl.
  subst_find; reflexivity.
Qed.

Lemma assign_safe :
  forall {av} state scas adts k w,
    @SomeSCAs av state scas ->
    @AllADTs av state adts ->
    scas[k >> SCA _ w] ->
    forall k' env,
      ~ StringMap.In k' adts ->
      Safe env (Assign k' k) state.
Proof.      
  intros. specialize (H _ _ H1).
  econstructor; unfold_coercions.
  + eauto using mapsto_eval.
  + eauto using not_in_adts_not_mapsto_adt.
Qed.

Lemma copy_word :
  forall {av env},
  forall k1 {k2} w adts scas knowledge,
    scas[k1 >> SCA _ w] ->
    ~ StringMap.In k2 adts ->
    refine (@Prog av env knowledge
                  scas ([k2 >sca> w]::scas)
                  adts adts)
           (ret (Assign k2 k1)).
Proof.
  unfold refine, Prog, ProgOk; intros; constructor; intros.
  inversion_by computes_to_inv; subst.

  split.

  (* Safe *)
  eauto using assign_safe.

  (* RunsTo *) (* TODO: extract to lemma *)
  intros; inversion_facade; split;
  rewrite_Eq_in_goal; pose proof (H2 _ _ H). (* TODO: Put in scas_adts_mapsto *)
  erewrite mapsto_eval in H7 by eauto; autoinj.
  eauto using SomeSCAs_chomp.
  eauto using add_adts_pop_sca.
Qed.

Lemma no_op :
  forall {av env},
  forall adts scas knowledge,
    refine (@Prog av env knowledge
                  scas scas
                  adts adts)
           (ret Skip).
Proof.
  unfold refine, Prog, ProgOk; constructor; intros.
  inversion_by computes_to_inv; subst.
  split; [ constructor | intros; inversion_facade; intuition ].
Qed.

Lemma pull_forall :
  forall {A B C D} (f: D -> A -> B -> C -> Prop) b,
    (forall (x1: A) (x2: B) (x3: C),
       refine { p | f p x1 x2 x3 }%facade
              b) ->
    refine { p | forall x1 x2 x3,
                       f p x1 x2 x3 }%facade
           b.
Proof.
  unfold refine; intros; econstructor; intros.
  generalize (H x1 x2 x3 _ H0); intros.
  inversion_by computes_to_inv.
  assumption.
Qed.

Lemma pull_forall_loop_sca :
  forall env b loop knowledge
         scas adts vseq vret thead tis_empty,
    (forall head acc seq,
       refine  { cloop | SCALoopBodyProgCondition env loop cloop knowledge
                                                  scas adts vseq vret thead tis_empty
                                                  head acc seq } b) ->
    refine { cloop | SCALoopBodyOk env loop cloop knowledge
                                   scas adts vseq vret thead tis_empty }%facade b.
Proof.
  eauto using pull_forall.
Qed.

Lemma pull_forall_loop_adt :
  forall  acc_type wrapper env b loop knowledge
         scas adts vseq vret thead tis_empty,
    (forall head acc seq,
       refine  { cloop | @ADTLoopBodyProgCondition env acc_type loop cloop knowledge
                                                   scas adts vseq vret thead tis_empty
                                                   head wrapper acc seq } b) ->
    refine { cloop | @ADTLoopBodyOk env acc_type loop cloop knowledge
                                    scas adts vseq vret thead tis_empty wrapper }%facade b.
Proof.
  eauto using pull_forall.
Qed.

Lemma start_compiling_sca_with_precondition : (* TODO: Supersedes start_compiling *) 
  forall {av env} init_state scas adts vret v,
    SomeSCAs init_state scas ->
    AllADTs init_state adts ->
    refine (ret v) 
           (prog <- (@Prog av env True
                           scas ([vret >sca> v]::∅)
                           adts ∅);
            final_state <- {final_state | RunsTo env prog init_state final_state};
            {x | final_state[vret >> SCA av x]})%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  pose proof I.
  specialize_states;
  scas_adts_mapsto;
  auto_mapsto_unique;
  autoinj.
Qed.

Lemma start_compiling_adt_with_precondition : (* TODO: Supersedes start_compiling *) 
  forall {av env} init_state scas adts vret ret_type (v: ret_type) wrapper,
    (forall x y, wrapper x = wrapper y -> x = y) ->
    SomeSCAs init_state scas ->
    AllADTs init_state adts ->
    refine (ret v) 
           (prog <- (@Prog av env True
                           scas (∅)
                           adts ([vret >adt> wrapper v]::∅));
            final_state <- {final_state | RunsTo env prog init_state final_state};
            {x | final_state[vret >> Facade.ADT (wrapper x)]})%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  pose proof I.
  specialize_states;
  scas_adts_mapsto;
  auto_mapsto_unique;
  autoinj;
  eauto using eq_ret_compute.
Qed.

Lemma SomeSCAs_mapsto_inv:
  forall {av} state scas k v,
    state[k >> SCA av v] ->
    SomeSCAs state scas ->
    SomeSCAs state ([k >sca> v]::scas).
Proof.
  unfold SomeSCAs, Subset; intros * ? * some_scas ** k' v' maps_to.
  destruct (StringMap.E.eq_dec k k'); rewrite StringMapFacts.add_mapsto_iff in *;
  subst; intuition; autoinj.
Qed.

Lemma add_scas_in_postcond :
  forall {av env} scas adts adts' vret v,
    refine (@Prog av env True
                  scas ([vret >sca> v]::∅)
                  adts adts')
           (@Prog av env True
                  scas ([vret >sca> v]::scas)
                  adts adts').
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv.
  constructor; intros; destruct_pairs;
  split; intros; specialize_states.
  + intuition.
  + split; scas_adts_mapsto;
    eauto using SomeSCAs_mapsto_inv, SomeSCAs_empty.
Qed.


(*
Definition AllKnown {elt1 elt2} vars scas adts :=
  forall k, List.In k vars -> @StringMap.In elt1 k scas \/
                              @StringMap.In elt2 k adts.

Lemma AllKnown_find :
  forall {av} state scas adts,
    SomeSCAs state scas ->
    AllADTs state adts ->
    forall k,
    (StringMap.In (elt:=Value av) k scas \/
     StringMap.In (elt:=Value av) k adts) ->
    StringMapFacts.M.In (elt:=Value av) k state.
Proof.
  intros.
  destruct k.

 *)
(*
Lemma AllKnown_find :
  forall {av} state scas adts vars,
    SomeSCAs state scas ->
    AllADTs state adts ->
    AllKnown vars scas adts ->
    forall k,
      List.In k vars ->
      exists (v: Value av), StringMap.find k state = Some v.
Proof.
  induction vars; intros.
  exfalso; eauto using in_nil.
  apply in_inv in H2; destruct H2.
  + subst. specialize (H1 k (in_eq _ _)). 
    setoid_rewrite <- StringMapFacts.find_mapsto_iff.
    apply StringMapFacts.In_MapsTo.
  
Lemma AllKnown_mapM :
  forall {av} state scas adts args,
    SomeSCAs state scas ->
    AllADTs state adts ->
    AllKnown args scas adts ->
    exists args',
      mapM (@sel av state) args = Some args'.
Proof.
  induction args; intros ** all_known; simpl.
  + eexists; reflexivity.
  + unfold sel; specialize (all_known a (in_eq _ _)).
  induction 
 *)

(*
Lemma RunsToCallByName :
  forall {av env},
  forall scas adts knowledge,
  forall vret vpointer label args args' v w spec,
    Label2Word env label = Some w ->
    Word2Spec env w = Some (Axiomatic spec) ->
    ~ StringMap.In vpointer adts ->
    ~ StringMap.In vret adts ->
    (forall st,
       SomeSCAs (st) ([vpointer >sca> w]::scas) ->
       AllADTs st adts ->
       mapM (sel st) args = Some args') ->
    PreCond spec args' ->
    NoDup args ->
    refine (@Prog av env knowledge
                  scas ([vret >sca> v]::scas)
                  adts adts)
           (ret (Label vpointer label;
                 Call vret (Var vpointer) args)%facade).
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  (* Safe *)
  + repeat (constructor; intros).
    - econstructor; eauto using not_in_adts_not_mapsto_adt.
    - inversion_facade; mapsto_eq_add;
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.
      apply H3; rewrite_Eq_in_goal; eauto using SomeSCAs_chomp, add_adts_pop_sca.
      eapply not_in_adts_not_mapsto_adt; try eassumption.
      rewrite_Eq_in_goal; apply add_adts_pop_sca; eauto.

  (* RunsTo *)
  + repeat inversion_facade.
*)

Lemma RunsTo_label :
  forall av env st1 st2 vpointer label w,
    Label2Word env label = Some w ->
    @RunsTo av env (Label vpointer label) st1 st2 ->
    StringMap.Equal st2 ([vpointer >sca> w]::st1).
Proof.
  intros.
  inversion_facade.
  eq_transitive; autoinj.
Qed.

Lemma runsto_new :
  forall env st1 st2 w vpointer vret,
    Word2Spec env w = Some (Axiomatic List_new) ->
    st1[vpointer >> SCA _ w] ->
    RunsTo env (Call vret (Var vpointer) nil) st1 st2 ->
    StringMap.Equal st2 ([vret >adt> List nil]::st1).
Proof.
  intros;
  inversion_facade;
  simpl in *;
  autoinj; rewrite <- StringMapFacts.find_mapsto_iff in *;  (* TODO: Extend auto_mapsto_unique *)
  auto_mapsto_unique; intros;
  autoinj; eq_transitive; autoinj; simpl in *;
  match goal with
    | [ H: 0 = List.length _ |- _ ] => rewrite length_0 in H
  end; destruct_pairs; subst;
  [assumption|discriminate].
Qed.                       

Lemma runsto_copy_var :
  forall seq (vseq vcopy: StringMap.key) env (st st': State FacadeADT) pcopy vpointer,
    st[vpointer >> SCA _ pcopy] ->
    st[vseq >> Facade.ADT (List seq)] ->
    Word2Spec env pcopy  = Some (Axiomatic List_copy) ->
    RunsTo env (Call vcopy (Var vpointer) (vseq :: nil)) st st' ->
    StringMap.Equal st' ([vcopy >adt> List seq]::[vseq >adt> List seq]::st).
Proof.
  intros;
  inversion_facade;
  simpl in *;
  autoinj; rewrite <- StringMapFacts.find_mapsto_iff in *;  (* TODO: Extend auto_mapsto_unique *)
    auto_mapsto_unique; intros; autoinj; eq_transitive; autoinj; simpl in *.

  autodestruct; subst. simpl in *.
  destruct output; try discriminate.
  destruct output; try discriminate.
  autoinj.

  unfold sel in *.
  simpl in H16.
  
  subst_find; simpl in *. autoinj.
  discriminate.
Qed.

Lemma compile_new :
  forall {env},
  forall scas adts knowledge,
  forall vret vpointer label w,
    Label2Word env label = Some w ->
    Word2Spec env w = Some (Axiomatic List_new) ->
    ~ StringMap.In vpointer adts ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vret scas ->
    vpointer <> vret ->
    refine (@Prog _ env knowledge
                  scas ([vpointer >sca> w]::scas)
                  adts ([vret >adt> List nil]::adts))
           (ret (Label vpointer label;
                 Call vret (Var vpointer) nil)%facade).
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  (* Safe *)
  + repeat (constructor; intros).
    - econstructor; eauto using not_in_adts_not_mapsto_adt.
    - inversion_facade; mapsto_eq_add; (* TODO *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.
      constructor. reflexivity.
      eapply not_in_adts_not_mapsto_adt.
      rewrite_Eq_in_goal; eauto using add_adts_pop_sca.
      assumption.
      reflexivity.

  (* RunsTo *)
  + inversion_facade.
    eapply RunsTo_label in H11; eauto.

    mapsto_eq_add.
    eapply runsto_new in H14; eauto.
    split; repeat rewrite_Eq_in_goal.
    
    apply add_sca_pop_adts, SomeSCAs_chomp; trivial;
    rewrite StringMapFacts.F.add_neq_in_iff; assumption.

    apply AllADTs_chomp, add_adts_pop_sca; trivial;
    rewrite StringMapFacts.F.add_neq_in_iff; assumption.
Qed.

(*

Lemma compile_load_pointer :
  forall {av env}
         vpointer w label
         knowledge init_scas final_scas init_adts final_adts,
    Label2Word env label = Some w ->
    ~ StringMap.In vpointer init_adts ->
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts final_adts)
           (p <- (@Prog _ env knowledge
                        ([vpointer >sca> w]::init_scas) ([vpointer >sca> w]::final_scas)
                        (init_adts) (final_adts));
            ret (Label vpointer label; p)%facade)%comp.
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  + repeat (constructor; intros).
    - econstructor; eauto using not_in_adts_not_mapsto_adt.
    - eapply RunsTo_label in H7; eauto.
      setoid_rewrite H7.
      specialize_states. inversion_facade; mapsto_eq_add; (* TODO *)
*)

Definition LabelAndCall vpointer vret label args := (Label vpointer label;
                                                     Call vret (Var vpointer) args)%facade.

(* TODO: Replace mapsto_eq_add *)
Ltac mapsto_eq_add' :=
  repeat match goal with
           | H:StringMap.Equal _ _ |- _ =>
             let H' := fresh in
             progress (pose proof H as H'; apply mapsto_eq_add in H'; clear_dups)
         end.

Lemma mapM_not_in_args :
  forall {av} (st st': State av) args input k w,
    ~ List.In k args ->
    StringMap.Equal st' ([k >sca> w]::st) ->
    mapM (sel st) args = Some input ->
    mapM (sel st') args = Some input.
Proof.
  induction args; simpl in *; intros.
  + congruence.
  + destruct (sel st a) eqn:eq1;
    destruct (mapM (sel st) args) eqn:eq2;
    try discriminate.
    erewrite IHargs; eauto.
    replace (sel st' a) with (sel st a).
    rewrite eq1; assumption.

    unfold sel; rewrite H0.
    symmetry; apply StringMapFacts.add_neq_o; intuition.
Qed.

Lemma add_add_add :
  forall {elt} st k v,
    @StringMap.Equal elt
                     ([k >> v]::[k >> v]::st)
                     ([k >> v]::st).
Proof.
  intros; unfold StringMap.Equal;
  intros k'; destruct (StringMap.E.eq_dec k k'); subst.
  repeat rewrite StringMapFacts.add_eq_o; reflexivity.
  repeat rewrite StringMapFacts.add_neq_o; congruence.
Qed.

(*
Lemma RunsToLabelAndCall :
  forall ADTValue env,
  forall (vpointer vret : StringMap.key) (lbl : GLabel.glabel)
         st st' adts,
  forall (f : Expr)
         (args : list StringMap.key)
         (spec : AxiomaticSpec ADTValue)
         (input : list (Value ADTValue))
         (output : list (option ADTValue)) 
         (ret : Value ADTValue) (f_w : W),
    ~ List.In vpointer args ->
    Label2Word env lbl = Some f_w ->
    not_mapsto_adt vpointer st = true ->
    StringMapFacts.M.Equal st' ([vpointer >> SCA ADTValue f_w]::st) ->
    NoDup args ->
    eval st f = Some (SCA ADTValue f_w) ->
    Word2Spec env f_w = Some (Axiomatic spec) ->
    mapM (sel st) args = Some input ->
    AllADTs st adts ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vpointer adts ->
    PreCond spec input ->
    Datatypes.length input = Datatypes.length output ->
    PostCond spec (combine input output) ret ->
    let st' :=
        add_remove_many args input (wrap_output output) st in
    let st'0 := [vret >> ret]::st' in
    forall st'' : StringMapFacts.M.t (Value ADTValue),
      StringMapFacts.M.Equal st'' st'0 ->
      RunsTo env (LabelAndCall vpointer vret lbl args) st st''.
Proof.
  intros.
  unfold LabelAndCall; econstructor;
  expand; mapsto_eq_add'.
  econstructor; eauto.
  econstructor; eauto using mapsto_eval, mapM_not_in_args. 
  eapply not_in_adts_not_mapsto_adt; eauto.
  rewrite_Eq_in_goal.
  apply add_adts_pop_sca; eauto.

  Transparent add_remove_many.

    Lemma add_remove_many_eq :
    forall {av} (st st': State av) k v args input output,
      ~ List.In k args ->
      StringMapFacts.M.Equal st' ([k >> v]::st) ->
      StringMap.Equal
        ([k >> v]::add_remove_many args input (wrap_output output) st)
        ([k >> v]::add_remove_many args input (wrap_output output) st').
  Proof.
    induction args; simpl; intros.
    rewrite H0; symmetry; apply add_add_add.
    destruct input; [rewrite H0; symmetry; apply add_add_add | ].
  
  unfold not_mapsto_adt, is_mapsto_adt in *.
  rewrite 
 *)
 
Lemma compile_copy :
  forall {env},
  forall scas adts knowledge seq,
  forall vret vfrom vpointer label w,
    Label2Word env label = Some w ->
    Word2Spec env w = Some (Axiomatic List_copy) ->
    ~ StringMap.In vpointer adts ->
    ~ StringMap.In vret adts ->
    ~ StringMap.In vret scas ->
    ~ StringMap.In vfrom scas ->
    vpointer <> vret ->
    vpointer <> vfrom ->
    adts[vfrom >> Facade.ADT (List seq)] ->
    refine (@Prog _ env knowledge
                  scas ([vpointer >sca> w]::scas)
                  adts ([vret >adt> List seq]::adts))
           (ret (Label vpointer label;
                 Call vret (Var vpointer) (vfrom :: nil))%facade).
Proof.
  unfold refine, Prog, ProgOk; intros;
  inversion_by computes_to_inv;
  subst; constructor; split; intros;
  destruct_pairs.

  (* Safe *)
  + repeat (constructor; intros).
    - econstructor; eauto using not_in_adts_not_mapsto_adt.
    - inversion_facade; mapsto_eq_add; (* TODO *)
      eq_transitive; autoinj;
      econstructor; eauto 2 using mapsto_eval.
      repeat (constructor; eauto).

      scas_adts_mapsto.
      
      apply mapM_MapsTo_1; eauto.
      rewrite_Eq_in_goal.
      map_iff_solve idtac.      
      eassumption.

      eapply not_in_adts_not_mapsto_adt.
      rewrite_Eq_in_goal; eauto using add_adts_pop_sca.
      assumption.
      simpl; eexists; reflexivity.      
      
  (* RunsTo *)
  + inversion_facade.
    eapply RunsTo_label in H14; eauto.

    mapsto_eq_add.

    eapply runsto_copy_var in H17; eauto.
    split; repeat rewrite_Eq_in_goal.
    
    repeat (apply add_sca_pop_adts; [rewrite StringMapFacts.F.add_neq_in_iff; eassumption | ]).
    apply SomeSCAs_chomp; trivial.
    
    apply AllADTs_chomp, AllADTs_swap, add_adts_pop_sca; trivial.
    apply AllADTs_add_in; assumption.
    rewrite_Eq_in_goal; map_iff_solve idtac.
    scas_adts_mapsto; assumption.
Qed.

(*
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
    repeat (subst_find; simpl in;
    rewrite <- StringMapFacts.find_mapsto_iff in *.

  repeat progress (autoinj'; autoinj).

  autorewrite_equal; map_iff_solve intuition.
Qed.
*)
(*
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
*)
  
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

Lemma compile_add_intermediate_adts :
  forall av env knowledge init_scas final_scas init_adts inter_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas final_scas
                        init_adts inter_adts);
            q <- (@Prog av env knowledge
                        final_scas final_scas
                        inter_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.

Lemma compile_add_intermediate_adts_with_ret :
  forall av env knowledge k v init_scas final_scas init_adts inter_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts ([k >adt> v]::final_adts))
           (p <- (@Prog av env knowledge
                        init_scas final_scas
                        init_adts ([k >adt> v]::inter_adts));
            q <- (@Prog av env knowledge
                        final_scas final_scas
                        ([k >adt> v]::inter_adts) ([k >adt> v]::final_adts));
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; assumption.

  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.

Lemma compile_add_intermediate_scas_with_ret :
  forall av env knowledge k v init_scas inter_scas final_scas init_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas ([k >sca> v]::final_scas)
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas ([k >sca> v]::inter_scas)
                        init_adts final_adts);
            q <- (@Prog av env knowledge
                        ([k >sca> v]::inter_scas) ([k >sca> v]::final_scas)
                        final_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; try assumption.
  
  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.

Lemma compile_add_intermediate_scas :
  forall av env knowledge init_scas inter_scas final_scas init_adts final_adts,
    refine (@Prog av env knowledge
                  init_scas final_scas
                  init_adts final_adts)
           (p <- (@Prog av env knowledge
                        init_scas inter_scas
                        init_adts final_adts);
            q <- (@Prog av env knowledge
                        inter_scas final_scas
                        final_adts final_adts);
            ret (Seq p q))%comp.
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  split; intros.

  (* Safe *)
  constructor; split; intros; specialize_states; try assumption.
  
  (* RunsTo *)
  inversion_facade; specialize_states; intuition.
Qed.

Transparent Word.natToWord.

Lemma drop_scas_from_precond : (* TODO: Convert this to a morphism *)
  forall {av env} scas scas' scas'' adts adts',
    SomeSCAs scas scas'' ->
    refine (@Prog av env True
                  scas scas'
                  adts adts')
           (@Prog av env True
                  scas'' scas'
                  adts adts').
Proof.
  unfold refine, Prog, ProgOk; intros.
  inversion_by computes_to_inv; subst.
  constructor; intros; destruct_pairs.

  assert (SomeSCAs initial_state scas'') by
      eauto using SomeSCAs_transitive.

  split; intros; specialize_states; intuition.
Qed.

Lemma drop_second_sca_from_precond :
  forall {av env} scas scas' adts adts' k v k' v',
    refine (@Prog av env True
                  ([k >sca> v]::[k' >sca> v']::scas) scas'
                  adts adts')
           (@Prog av env True
                  ([k >sca> v]::(StringMap.remove k' scas)) scas'
                  adts adts').
Proof.
  intros;
  eauto using drop_scas_from_precond, SomeSCAs_chomp, SomeSCAs_remove, SomeSCAs_reflexive.
Qed.

(* TODO rename Subset to Superset *)

Ltac map_iff_solve_evar' fallback :=
  repeat setoid_rewrite not_or;
  match goal with
    | |- ?A /\ ?B => split; map_iff_solve_evar' fallback
    | |- ?a = ?ev /\ ?b = ?b \/ ?a <> ?ev /\ _ =>
      is_evar ev; left; split; [ apply eq_refl | reflexivity ]
    | |- ?a = ?a /\ _ \/ ?a <> ?a /\ _ =>
      left; split; [ apply eq_refl | map_iff_solve_evar' fallback ]
    | |- ?a = ?b /\ _ \/ ?a <> ?b /\ _ =>
      right; split; [ | map_iff_solve_evar' fallback ]; congruence
    | _ => fallback
  end.

Ltac map_iff_solve_evar fallback :=
  StringMapFacts.map_iff; map_iff_solve_evar' fallback.

(* TODO extend vacuum *)
Ltac vacuum' :=
  first [
      progress (unfold SCALoopBodyProgCondition; intros) |
      match goal with
        | [ |- ?m[?k >> ?v] ] => solve [map_iff_solve_evar intuition]
        | [ |- SomeSCAs _ ∅ ] => apply SomeSCAs_empty
        | [ |- SomeSCAs _ _ ] => eassumption
        | [ |- AllADTs _ _ ] => eassumption
        | [ |- Word2Spec ?env _ = Some (Axiomatic _) ] => reflexivity
        | _ => vacuum
      end ].

Definition start_sca state vret adts :=
  (@start_compiling_sca_with_precondition _ basic_env state ∅ adts vret).

Goal forall seq: list W, 
     forall state,
       AllADTs state (["$list" >adt> List seq]::∅) ->
       exists x, 
         refine (ret (fold_left (fun (sum item: W) => Word.wplus item sum) seq 0)) x.
Proof.
  intros; eexists.
  setoid_rewrite (start_sca state "$ret"); vacuum'.

  setoid_rewrite compile_add_intermediate_adts; vacuum'.
  setoid_rewrite (compile_fold_sca basic_env "$list" "$ret" "$head" "$is_empty" 1 0); vacuum'.
  setoid_rewrite (pull_forall_loop_sca); try vacuum'. 

  Focus 2.
  setoid_rewrite compile_add_intermediate_scas_with_ret.
  setoid_rewrite (compile_binop IL.Plus "$ret" "$head'" "$ret'"); vacuum'.
  rewrite copy_word; vacuum'.
  rewrite copy_word; vacuum'.

  rewrite drop_second_sca_from_precond; trickle_deletion.
  rewrite drop_second_sca_from_precond; trickle_deletion.
  rewrite drop_second_sca_from_precond; trickle_deletion.
  rewrite no_op; vacuum.
  reflexivity.

  rewrite compile_constant; vacuum.
Admitted.

Definition start_adt state vret {ret_type v} wrapper wrapper_inj adts :=
  (@start_compiling_adt_with_precondition _ basic_env state ∅ adts vret ret_type v wrapper wrapper_inj).

Lemma List_inj' : forall x y : list W, List x = List y -> x = y.
  intros * _eq; injection _eq; intros; assumption.
Qed.

Goal forall seq: list W, 
     forall state,
       AllADTs state (["$list" >adt> List seq]::∅) ->
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
  intros; eexists.
  
  (* Start compiling, copying the state_precond precondition to the resulting
     program's preconditions. Result is stored into [$ret] *)
  rewrite (start_adt state "$ret" List List_inj'); vacuum'.

  (* Compile the fold, reading the initial value of the accumulator from
     [$init], the input data from [$seq], and storing temporary variables in
     [$head] and [$is_empty]. *)
  setoid_rewrite compile_add_intermediate_adts_with_ret; vacuum'.
  setoid_rewrite (compile_fold_adt _ _ _ "$list" "$ret" "$head" "$is_empty" 1 0); try vacuum'.

  (* Extract the quantifiers, and move the loop body to a second goal *)
  rewrite (pull_forall_loop_adt); vacuum'.
  
  (* The output list is allocated by calling List_new, whose axiomatic
     specification is stored at address 2 *)
  setoid_rewrite compile_add_intermediate_scas; vacuum'.
  setoid_rewrite (compile_new _ _ _ "$ret" "jj" ("??", "List_new")); try vacuum'.
  rewrite drop_scas_from_precond; try vacuum'.
  rewrite no_op; try vacuum'.

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
