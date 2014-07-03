Require Export BagsOfTuples Bool.
Require Export ListImplementation.
Require Export ConstraintChecksRefinements.
Require Export Bags AdditionalLemmas AdditionalRefinementLemmas AdditionalMorphisms Bool tupleAgree.
Require Export QueryStructureNotations.

Import AdditionalLemmas.

Global Opaque binsert benumerate bfind bcount.


Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- string_dec_bool_true_iff;
  setoid_rewrite and_True;
  repeat progress (
           try setoid_rewrite <- andb_true_iff;
           try setoid_rewrite not_true_iff_false;
           try setoid_rewrite <- negb_true_iff);
  rewrite bool_equiv_true;
  reflexivity.

Hint Extern 100 (DecideableEnsemble _) => prove_decidability_for_functional_dependencies : typeclass_instances.

Notation "heading / attr_index" := ((fun x : Attributes heading => x) 
                                       {| bindex := attr_index; indexb := _ |}) 
                                      (at level 40, left associativity).

Ltac lmap A f seq :=
  let rec aux seq :=
      match seq with
        | nil => constr:(@nil A)
        | ?h :: ?t =>
          let h' := f h in
          let t' := aux t in
          constr:(h' :: t')
      end 
  in aux seq.

Ltac makeIndex sc table columns :=
  set (heading := GetHeading sc table);
  mkIndex heading ltac:(lmap (Attributes heading)%type ltac:(fun x => constr:(heading/x)) columns).

Notation "QSSchema # rel_key" := (TupleDef QSSchema rel_key) (at level 100, no associativity).

Notation "?[ A ]" := (if A then true else false) (at level 50).

(** * Tactics galore! *)

Ltac evarForType T k :=
  match T with
  | (?A * ?B)%type =>
    evarForType A ltac:(fun Av =>
                          evarForType B ltac:(fun Bv => k (Av, Bv)))
  | _ => let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y
  end.

Hint Extern 1 (_ ≃ _) => apply bempty_correct_DB : StartOfMethod.

Ltac splitPick :=
  match goal with
  | [ |- refine (@Pick ?T _) _ ] => evarForType T ltac:(fun Tv =>
      rewrite (refine_pick_val' Tv) by (unfold fst, snd; intuition auto with StartOfMethod))
  end.

Ltac startMethod AbsR :=
  unfold AbsR in *; split_and; simplify with monad laws.

Ltac finishMethod := subst_body; higher_order_1_reflexivity.

Ltac initializer :=
  match goal with
    | [ |- refine (or' <- _; Pick (fun nr' => ?AbsR or' nr')) _ ] =>
      startMethod AbsR; try splitPick; finishMethod
  end.

(* We need to avoid bad "simplification" of [bfind_matcher] calls,
 * which hide the right structure for type-class resolution.
 * [simp] defined here is a [simpl] version that prevents such reductions. *)

Ltac hide_bfind_matcher :=
  repeat match goal with
         | [ |- appcontext[@bfind_matcher ?a ?b ?c ?d] ] =>
           remember (@bfind_matcher a b c d)
         end.

Ltac reveal_bfind_matcher :=
  repeat match goal with
         | [ _ : ?x = @bfind_matcher _ _ _ _ |- _ ] => subst x
         end.

Ltac simp := hide_bfind_matcher; simpl; reveal_bfind_matcher.

Ltac concretize1 :=
  (rewrite refine_List_Query_In by eassumption)
    || (rewrite refine_Join_List_Query_In by eassumption)
    || (rewrite refine_List_Query_In_Where; instantiate (1 := _))
    || rewrite refine_List_For_Query_In_Return_Permutation.

Ltac concretize := repeat concretize1; simpl.

(* Now some tactics that operate while the query is still allowed to vary by permutation. *)

Ltac equate X Y := let H := fresh in assert (H : X = Y) by reflexivity; clear H.

Ltac getFst F k :=
  match type of F with
  | ?A * ?B -> ?C =>
    let G := fresh "G" in let p := fresh "p" in let H := fresh "H" in
    evar (G : A -> C); assert (H : forall p, F p = G (fst p)) by (subst G; intro p;
      pattern (fst p);
      match goal with
      | [ |- (fun t => @?f t = @?g t) _ ] => equate g f; reflexivity
      end); clear H;
    let G' := eval unfold G in G in clear G; k G'
  end.

Ltac getSnd F k :=
  match type of F with
  | ?A * ?B -> ?C =>
    let G := fresh "G" in let p := fresh "p" in let H := fresh "H" in
    evar (G : B -> C); assert (H : forall p, F p = G (snd p)) by (subst G; intro p;
      pattern (snd p);
      match goal with
      | [ |- (fun t => @?f t = @?g t) _ ] => equate g f; reflexivity
      end); clear H;
    let G' := eval unfold G in G in clear G; k G'
  end.

Theorem map_ident : forall A ls, map (fun x : A => x) ls = ls.
Proof.
  induction ls; simpl; intuition congruence.
Qed.

Ltac asPerm_indep :=
  match goal with
    | _ => setoid_rewrite map_ident
    | _ => setoid_rewrite map_flat_map; simp
    | _ => setoid_rewrite map_map; simp
    | _ => setoid_rewrite (bfind_correct _)
    | [ |- context[filter ?F _] ] =>
      getFst F ltac:(fun f => rewrite (filter_join_fst f))
                      || getSnd F ltac:(fun f => rewrite (filter_join_snd f))
    | [ |- context[filter _ (Join_Lists ?ls1 (filter ?f ?ls2))] ] =>
      (* The check below prevent this rule from creating an infinite loop
         when asPerm_indep is called repeatedly *)
      match ls1 with (filter _ _) => fail end;
      (* If ls1 is not a filter, though, it's probably best to swap the two 
         lists before calling rewrite filter_join_lists, since filter_join
         _lists produces code that loops on the ls1 first *)
      setoid_rewrite (swap_joins ls1 (filter f ls2)); trickle_swap; simp
    | _ => setoid_rewrite filter_join_lists; simp
  end.

Ltac fields storage :=
  match eval cbv delta [storage] in storage with
  | let src := ?X in _ => X
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac createTerm SC f fd X tail fs k :=
  match fs with
  | nil =>
    k tail
  | ?s :: ?fs' =>
    createTerm SC f fd X tail fs' ltac:(fun rest =>
      (let H := fresh in assert (H : bindex s = fd) by reflexivity; clear H;
       k (Some X, rest))
        || k (@None (f s), rest))
  end.

Ltac makeTerm storage fs SC fd X tail k :=
  match eval hnf in SC with
    | Build_Heading ?f =>
      createTerm SC f fd X tail fs k
  end.

Ltac findGoodTerm SC F k :=
  match F with
  | fun a => ?[@?f a] =>
    match type of f with
    | forall a, {?X = _!?fd} + {_} => k fd X (@nil (TSearchTermMatcher SC))
    | forall a, {_!?fd = ?X} + {_} => k fd X (@nil (TSearchTermMatcher SC))
    | forall a, {?X = _``?fd} + {_} => k fd X (@nil (TSearchTermMatcher SC))
    | forall a, {_``?fd = ?X} + {_} => k fd X (@nil (TSearchTermMatcher SC))
    end
  | fun a => (@?f a) && (@?g a) =>
    findGoodTerm SC f ltac:(fun fd X tail => k fd X (g :: tail))
    || findGoodTerm SC g ltac:(fun fd X tail => k fd X (f :: tail))
  end.

Ltac useIndex storage :=
  match goal with
    | [ |- context[@filter Tuple ?F _ ] ] =>
      let fs := fields storage in
      match type of fs with
        | list (Attributes ?SC) =>
          findGoodTerm SC F ltac:(fun fd X tail => makeTerm storage fs SC fd X tail
            ltac:(fun tm => rewrite filter over storage using search term tm))
      end
  end.

Ltac find_usage F k :=
  match F with
    | fun x => map ?G (@?F' x) =>
      let T := type of G in
      find_usage F' k
    | fun x => filter ?G (@?F' x) =>
      let T := type of G in
      find_usage F' k
    | fun x => map (fun y => @?G x y) (@?F' x) =>
      k G
    | fun x => filter (fun y => @?G x y) (@?F' x) =>
      k G
  end.

Ltac findGoodTerm_dep F k :=
  match F with
    | fun a b => ?[@?f a b] =>
      match type of f with
        | forall a b, {a!?fd = _} + {_} => k fd
        | forall a, {_ = a!?fd} + {_} => k fd
      end
  end.

Ltac createTerm_dep dom SC f fd fs k :=
  match fs with
  | nil =>
    k (fun x : dom => @nil (TSearchTermMatcher SC))
  | ?s :: ?fs' =>
    createTerm_dep dom SC f fd fs' ltac:(fun rest =>
      (let H := fresh in assert (H : bindex s = fd) by reflexivity; clear H;
       k (fun x : dom => (Some (x!fd), rest x))
        || k (fun x : dom => (@None (f s), rest x))))
  end.

Ltac makeTerm_dep storage dom fd k :=
  let fs := fields storage in
  match type of fs with
    | list (Attributes ?SC) =>
      match eval hnf in SC with
        | Build_Heading ?f =>
          createTerm_dep dom SC f fd fs k
      end
  end.

Ltac useIndex_dep storage :=
  match goal with
    | [ |- context[fun x : ?dom => @?F x] ] => find_usage F ltac:(fun G =>
        findGoodTerm_dep G ltac:(fun fd =>
          makeTerm_dep storage dom fd ltac:(fun tm =>
            rewrite dependent filter G over storage
                    using dependent search term tm)))
  end.

Ltac asPerm_dep' storage := useIndex storage || useIndex_dep storage.
Ltac asPerm_dep storages :=
  asPerm_dep' storages
          || match storages with
             | (?s1, ?s2) => asPerm_dep s1 || asPerm_dep s2
             end.

Ltac asPerm' storages := asPerm_indep || asPerm_dep storages.
Ltac asPerm storages := repeat (asPerm' storages).

(* A final cleanup phase, applying a few helpful rewrites *)

Ltac cleanup := repeat (setoid_rewrite length_flat_map
                     || setoid_rewrite map_length
                     || setoid_rewrite bcount_correct).

(* After doing all the optimizations we want in permutation land, we commit to a list. *)

Lemma refine_count : forall A B C a (f : A -> B) (g : B -> Comp C),
                       refine (x <- (l <- ret a; ret (f l)); g x) (x <- ret (f a); g x).
Proof.
  intros; simplify with monad laws; do 2 intro.
  apply computes_to_inv in H; firstorder.
  apply computes_to_inv in H; firstorder congruence.
Qed.

Ltac commit := repeat (setoid_rewrite refine_Permutation_Reflexivity
                    || setoid_rewrite refine_Count);
              try (etransitivity; [ apply refine_count | ]);
              cleanup; try simplify with monad laws.

(* Next, a trivial step to choose the new database to be just the old one. *)

Ltac choose_db AbsR := unfold AbsR; rewrite refine_pick_val by eauto; [ simplify with monad laws ].

(* Final wrapper tactic for observers *)

Ltac storageOf T :=
  match eval hnf in T with
    | (?T1 * ?T2)%type =>
      let s1 := storageOf T1 in
      let s2 := storageOf T2 in
      constr:(s1, s2)
    | _ =>
      match eval unfold T in T with
        | BagType ?s => s
      end
  end.

Ltac observer' AbsR storages :=
  startMethod AbsR; concretize; asPerm storages;
  commit; choose_db AbsR; finish honing.

Ltac observer :=
  match goal with
    | [ _ : ?AbsR _ _ |- _ ] =>
      match type of AbsR with
        | UnConstrQueryStructure _ -> ?T -> Prop =>
          let storages := storageOf T in observer' AbsR storages
    end
  end.

(* Tactics for implementing constraint checks in mutators *)

Theorem key_symmetry : forall A H (f : _ -> _ -> Comp A) (P : _ -> Prop) sc1 sc2 n,
  refine (x1 <- Pick (fun b : bool => decides b (forall tup' : @IndexedTuple H,
                                                    P tup'
                                                    -> tupleAgree n tup' sc1
                                                    -> tupleAgree n tup' sc2));
          x2 <- Pick (fun b : bool => decides b (forall tup' : @IndexedTuple H,
                                                    P tup'
                                                    -> tupleAgree tup' n sc1
                                                    -> tupleAgree tup' n sc2));
          f x1 x2)
         (x1 <- Pick (fun b : bool => decides b (forall tup' : @IndexedTuple H,
                                                   P tup'
                                                   -> tupleAgree n tup' sc1
                                                   -> tupleAgree n tup' sc2));
          f x1 x1).
Proof.
  unfold refine; intros.
  apply computes_to_inv in H0; firstorder.
  apply computes_to_inv in H0; firstorder.
  econstructor.
  eauto.
  econstructor.
  econstructor.
  instantiate (1 := x).
  eapply decide_eq_iff_iff_morphism; eauto.
  unfold tupleAgree; intuition auto using sym_eq.
  assumption.
Qed.


Ltac pruneDuplicates :=
  repeat ((setoid_rewrite refine_trivial_if_then_else || setoid_rewrite key_symmetry || setoid_rewrite refine_tupleAgree_refl_True); try simplify with monad laws).

Ltac pickIndex :=
  rewrite refine_pick_val by eauto using EnsembleIndexedListEquivalence_pick_new_index;
  simplify with monad laws.

Ltac foreignToQuery :=
  match goal with
    | [ |- context[Pick (fun b' => decides b' (exists tup2 : @IndexedTuple ?H, _ /\ ?r ``?s = _ ))] ] =>
      match goal with
        | [ |- appcontext[@benumerate _ (@Tuple ?H')] ] =>
          equate H H'; let T' := constr:(@Tuple H') in
            rewrite (refine_foreign_key_check_into_query (fun t : T' => r!s = t!s))
              by eauto with typeclass_instances;
              simplify with monad laws; cbv beta; simpl
      end
  end.

Ltac dec_tauto := clear; intuition eauto;
                  eapply Tuple_Agree_eq_dec;
                  match goal with
                    | [ |- ?E = true ] => case_eq E; intuition idtac; [ exfalso ]
                  end;
                  match goal with
                    | [ H : _ |- _ ] => apply Tuple_Agree_eq_dec' in H; solve [ eauto ]
                  end.

Ltac fundepToQuery :=
  match goal with
    | [ |- context[Pick (fun b => decides b (forall tup', _ -> tupleAgree ?n _ _ -> tupleAgree ?n _ _))] ] =>
      rewrite (refine_functional_dependency_check_into_query n);
        [ | prove_decidability_for_functional_dependencies | dec_tauto ]
    | [ |- context[Pick (fun b => decides b (forall tup', _ -> tupleAgree _ ?n _ -> tupleAgree _ ?n _))] ] =>
      rewrite (refine_functional_dependency_check_into_query n);
        [ | prove_decidability_for_functional_dependencies | dec_tauto ]
  end; try simplify with monad laws.

Ltac checksSucceeded :=
  match goal with
    | [ |- context[ret (_, true)] ] =>
      refineEquiv_pick_pair_benumerate; simplify with monad laws;
      repeat (rewrite refine_pick_val by (refine_list_insert_in_other_table || binsert_correct_DB);
              simplify with monad laws);
      reflexivity
  end.

Ltac checksFailed :=
  match goal with
    | [ |- context[ret (_, false)] ] =>
      rewrite refine_pick_val by eauto; simplify with monad laws; reflexivity
  end.

Ltac mutator' AbsR storages :=
  startMethod AbsR; pruneDuplicates; pickIndex;
  repeat ((foreignToQuery || fundepToQuery);
          concretize; asPerm storages; commit);
  Split Constraint Checks; checksSucceeded || checksFailed.

Ltac mutator :=
  match goal with
    | [ |- context[tupleIndex _ <> _] ] =>
      match goal with
        | [ |- context[nr' <- Pick (fun nr' => ?AbsR _ nr'); ret (nr', _)] ] =>
          match type of AbsR with
            | UnConstrQueryStructure _ -> ?T -> Prop =>
              let storages := storageOf T in mutator' AbsR storages
          end
      end
  end.

(* Now, one tactic to combine all method types. *)

Ltac method :=
  match goal with
    | [ |- refine (x <- ret _; Pick _) _ ] => initializer
    | [ |- refine (x <- _; y <- Pick _; ret _) _ ] => observer
    | _ => mutator
  end.

Ltac honeOne :=
  match goal with
    | [ |- context[@Build_consDef _ (Build_consSig ?id _) _] ] =>
      hone constructor id; [ method | ]
    | [ |- context[@Build_methDef _ (Build_methSig ?id _ _) _] ] =>
      hone method id; [ method | ]
  end.

(* Finally, implement a whole ADT. *)

Ltac unfolder E k :=
  (let E' := eval unfold E in E in k E')
    || k E.

Ltac hone_representation AbsR' :=
  eapply SharpenStep;
  [eapply refineADT_BuildADT_Rep_default with (AbsR := AbsR') |
   compute [imap absConsDef absMethDef]; simpl ].

Ltac plan AbsR :=
  match goal with
    | [ |- Sharpened ?spec ] =>
      unfolder spec ltac:(fun spec' => change spec with spec')
  end; start_honing_QueryStructure; hone_representation AbsR;
  repeat honeOne.
