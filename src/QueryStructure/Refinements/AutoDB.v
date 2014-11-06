Require Export ADTSynthesis.QueryStructure.Refinements.Bags.BagsOfTuples Coq.Bool.Bool.
Require Export ADTSynthesis.QueryStructure.Refinements.ListImplementation.
Require Export ADTSynthesis.QueryStructure.Refinements.ConstraintChecksRefinements ADTSynthesis.Common.DecideableEnsembles.
Require Export ADTSynthesis.QueryStructure.Refinements.Bags.Bags ADTSynthesis.QueryStructure.AdditionalLemmas ADTSynthesis.QueryStructure.Refinements.AdditionalFlatMapLemmas ADTSynthesis.QueryStructure.Refinements.AdditionalRefinementLemmas ADTSynthesis.QueryStructure.Refinements.AdditionalMorphisms Coq.Bool.Bool ADTSynthesis.QueryStructure.tupleAgree ADTSynthesis.QueryStructure.IndexedEnsembles.
Require Export ADTSynthesis.QueryStructure.QueryStructureNotations ADTSynthesis.QueryStructure.Refinements.OperationRefinements.
Require Export ADTSynthesis.Common.IterateBoundedIndex.

Import AdditionalLemmas.

Global Opaque binsert benumerate bfind bcount.


Ltac prove_decidability_for_functional_dependencies :=
  simpl; econstructor; intros;
  try setoid_rewrite <- eq_nat_dec_bool_true_iff;
  try setoid_rewrite <- eq_N_dec_bool_true_iff;
  try setoid_rewrite <- eq_Z_dec_bool_true_iff;
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

Ltac startMethod AbsR :=
  unfold AbsR in *; split_and; simplify with monad laws.

Ltac finishMethod := subst_body; higher_order_1_reflexivity.

(* These tactics implement initializing the empty database. *)
Hint Extern 1 (_ ≃ _) => eapply bemptyPlus_correct_DB : StartOfMethod.

Ltac splitPick :=
  match goal with
  | [ |- refine (@Pick ?T _) _ ] => evarForType T ltac:(fun Tv =>
      rewrite (refine_pick_val' Tv) by (unfold fst, snd; intuition auto with StartOfMethod))
  end.

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

Ltac EquivalentBagIsEquivalentIndexedList :=
  match goal with
    | [ H: EnsembleBagEquivalence _ ?ens _ |-
        EnsembleIndexedListEquivalence ?ens _ ] =>
      solve [apply H]
  end.

Ltac concretize1 :=
  (rewrite refine_List_Query_In by EquivalentBagIsEquivalentIndexedList)
    || (rewrite refine_Join_List_Query_In by EquivalentBagIsEquivalentIndexedList)
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
      match ls1 with (filter _ _) => fail 1 | _ => idtac end;
      (* If ls1 is not a filter, though, it's probably best to swap the two
         lists before calling rewrite filter_join_lists, since filter_join
         _lists produces code that loops on the ls1 first *)
      setoid_rewrite (swap_joins ls1 (filter f ls2)); trickle_swap; simp
    | _ => setoid_rewrite filter_join_lists; simp
    | _ => setoid_rewrite <- filter_and
  end.

Ltac fields storage :=
  match eval cbv delta [storage] in storage with
  | let src := ?X in _ => X
  end.

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac findMatchingTerm fds s k :=
  match fds with
    | (?fd, ?X) =>
      let H := fresh in assert (H : bindex s = fd) by reflexivity; clear H;
        k X
    | (?fds1, ?fds2) => findMatchingTerm fds1 s k || findMatchingTerm fds2 s k
  end.

Ltac createTerm f fds tail fs k :=
  match fs with
  | nil =>
    k tail
  | ?s :: ?fs' =>
    createTerm f fds tail fs' ltac:(fun rest =>
      findMatchingTerm fds s ltac:(fun X =>
        k (Some X, rest))
      || k (@None (f s), rest))
  end.

(* Get the heading of SC, then *)
Ltac makeTerm storage fs SC fds tail k :=
  match eval hnf in SC with
  | Build_Heading ?f =>
    createTerm f fds tail fs k
  end.

(* Given a storage schema [SC], a filter [F], and a
   tactic [k] which processes filters, convert [F] into
   a search term (a list of boolean functions over the tuples in
   [SC]. *)
Ltac findGoodTerm SC F k :=
  match F with
  | fun a => ?[@?f a] =>
    match type of f with
    | forall a, {?X = _!?fd} + {_} => k (fd, X) (@nil (TSearchTermMatcher SC))
    | forall a, {_!?fd = ?X} + {_} => k (fd, X) (@nil (TSearchTermMatcher SC))
    | forall a, {?X = _``?fd} + {_} => k (fd, X) (@nil (TSearchTermMatcher SC))
    | forall a, {_``?fd = ?X} + {_} => k (fd, X) (@nil (TSearchTermMatcher SC))
    end
  | fun a => (@?f a) && (@?g a) =>
    findGoodTerm SC f ltac:(fun fds1 tail1 =>
      findGoodTerm SC g ltac:(fun fds2 tail2 =>
        k (fds1, fds2) (tail1 ++ tail2)%list))
  | _ => k tt (F :: nil)
  end.

Ltac useIndex storage :=
  match goal with
    (* If we've already filtered, don't do it again*)
    | [ |- context[@filter Tuple (@bfind_matcher _ _ _ _ _ _) _ ] ] => fail 1
    | [ |- context[@filter Tuple ?F _ ] ] =>
      let fs := fields storage in
      match type of fs with
        | list (Attributes ?SC) =>
          findGoodTerm SC F ltac:(fun fds tail =>
            let tail := eval simpl in tail in
              makeTerm storage fs SC fds tail
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

Ltac findGoodTerm_dep SC F k :=
  match F with
  | fun (a : ?T) b => ?[@?f a b] =>
    match type of f with
    | forall a b, {@?X a = _!?fd} + {_} => k (fd, X) (fun _ : T => @nil (TSearchTermMatcher SC))
    | forall a b, {_!?fd = @?X a} + {_} => k (fd, X) (fun _ : T => @nil (TSearchTermMatcher SC))
    | forall a b, {@?X a = _``?fd} + {_} => k (fd, X) (fun _ : T => @nil (TSearchTermMatcher SC))
    | forall a b, {_``?fd = @?X a} + {_} => k (fd, X) (fun _ : T => @nil (TSearchTermMatcher SC))
    end
  | fun (a : ?T) b => (@?f a b) && (@?g a b) =>
    findGoodTerm_dep SC f ltac:(fun fds1 tail1 =>
      findGoodTerm_dep SC g ltac:(fun fds2 tail2 =>
        k (fds1, fds2) (fun x : T => tail1 x ++ tail2 x)%list))
  | _ => k tt (fun x => F x :: nil)
  end.

Ltac createTerm_dep dom SC f fds fs k :=
  match fs with
  | nil =>
    k (fun x : dom => @nil (TSearchTermMatcher SC))
  | ?s :: ?fs' =>
    createTerm_dep dom SC f fds fs' ltac:(fun rest =>
      findMatchingTerm fds s ltac:(fun X =>
        k (fun x : dom => (Some (X x), rest x)))
      || k (fun x : dom => (@None (f s), rest x)))
  end.

Ltac makeTerm_dep SC storage dom fds k :=
  let fs := fields storage in
  match eval hnf in SC with
    | Build_Heading ?f =>
      createTerm_dep dom SC f fds fs k
  end.

Ltac useIndex_dep storage :=
  let fs := fields storage in
  match type of fs with
    | list (Attributes ?SC) =>
      match goal with
        | [ |- context[fun x : ?dom => @?F x] ] => find_usage F ltac:(fun G =>
          findGoodTerm_dep SC G ltac:(fun fds rest =>
            let rest := eval simpl in rest in
            makeTerm_dep SC storage dom fds ltac:(fun tm =>
              let tm := eval simpl in tm in
                rewrite dependent filter G over storage
                        using dependent search term tm)))
      end
  end.

Ltac useDeleteIndex :=
  match goal with
      [ H : EnsembleBagEquivalence ?bag_plus (@GetUnConstrRelation ?qsSchema ?qs ?Ridx) ?bag
        |- context[Pick (QSDeletedTuples ?qs ?Ridx ?DeletedTuples)] ] =>
      let dec := constr:(@dec _ DeletedTuples _) in
      let storage := bag_plus in
      let fs := fields storage in
      match type of fs with
        | list (Attributes ?SC) =>
          findGoodTerm SC dec ltac:(fun fds tail =>
            let tail := eval simpl in tail in
              makeTerm storage fs SC fds tail
              ltac:(fun tm =>
                      rewrite (@bdelete_correct_DB_fst
                                 qsSchema qs Ridx bag_plus
                                 bag H DeletedTuples _ tm) by prove_extensional_eq))
      end
    end; rewrite refineEquiv_bind_unit; simpl.

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
                    || setoid_rewrite refine_Count
                    || setoid_rewrite refine_MaxN
                    || setoid_rewrite refine_SumN
                    || setoid_rewrite refine_MaxZ
                    || setoid_rewrite refine_SumZ
                    || setoid_rewrite refine_Max
                    || setoid_rewrite refine_Sum);
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
        | ?s => s
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
                                                   -> tupleAgree n (indexedElement tup') sc1
                                                   -> tupleAgree n (indexedElement tup') sc2));
          x2 <- Pick (fun b : bool => decides b (forall tup' : @IndexedTuple H,
                                                    P tup'
                                                    -> tupleAgree (indexedElement tup') n sc1
                                                    -> tupleAgree (indexedElement tup') n sc2));
          f x1 x2)
         (x1 <- Pick (fun b : bool => decides b (forall tup' : @IndexedTuple H,
                                                   P tup'
                                                   -> tupleAgree n (indexedElement tup') sc1
                                                   -> tupleAgree n (indexedElement tup') sc2));
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

(* Pick a new logical index using [EnsembleBagEquivalence_pick_new_index] *)
Ltac pickIndex :=
    match goal with
        [H : EnsembleBagEquivalence ?storage ?R ?bag
         |- context[Pick (fun bound => UnConstrFreshIdx ?R bound) ] ] =>
        let bound := fresh in
        let ValidBound := fresh in
        destruct (@EnsembleBagEquivalence_pick_new_index _ storage R bag H)
          as [bound ValidBound];
          rewrite refine_pick_val by eauto using ValidBound;
          simplify with monad laws end.

Ltac revealSchema :=
  repeat match goal with
         | [ x : ?T |- _ ] =>
           match T with
           | _#_ => fail 1
           | _ => red in x; match type of x with
                            | _#_ => idtac
                            end
           end
         end.

Ltac foreignToQuery :=
  revealSchema;
  match goal with
    | [ _ : ?SC#_ |- context[Pick
                               (fun b' =>
                                  decides
                                    b'
                                    (ForeignKey_P ?attr ?attr'
                                                  ?tupmap ?tup
                                                  (_!?R)%QueryImpl))]]
      =>  let T' := constr:(@Tuple (schemaHeading
                                      (relSchema
                                         (@nth_Bounded NamedSchema string relName (qschemaSchemas SC) ``R)))) in
      let temp := fresh in
      pose (refine_foreign_key_check_into_query (fun t : T' => tup attr = tupmap (t attr'))) as temp; unfold ForeignKey_P;
      rewrite temp by eauto with typeclass_instances;
        simplify with monad laws; cbv beta; simpl; clear temp
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
      setoid_rewrite refineEquiv_pick_pair;
        (* Because our equivalence relation on Bags hides the application of ,
           benumerate, we can now simply call [refineEquiv_pick_pair]
           instead of  [refineEquiv_pick_pair_benumerate]  here.  *)
        simplify with monad laws;
      repeat (rewrite refine_pick_val by
                 (refine_bag_update_other_table
                    || binsert_correct_DB);
              simplify with monad laws);
      reflexivity
  end.

Ltac bdeleteZeta :=
  simpl;
  match goal with
    | [ |- refine (ret ?p) ?B ] =>
      match goal with
          [ |- context[@bdelete ?bag ?item ?TSearchTerm ?UpdateTerm
                           ?bag_proof ?r_n ?search_term] ] =>
          let b :=
              (eval pattern (@bdelete bag item TSearchTerm UpdateTerm bag_proof r_n search_term)
                in p) in
          match b with
              | ?g ?x => change p with (let y := x in g y);
                         cbv beta
          end
      end
  end.

Ltac deleteChecksSucceeded :=
  useDeleteIndex;
  match goal with
    | [ |- context[ret (_, fst (bdelete ?r_n ?search_term)) ] ] =>
      setoid_rewrite refineEquiv_pick_pair;
        simplify with monad laws;
        repeat (rewrite refine_pick_val
                by (simpl; (refine_bag_update_other_table
                              || snd_bdelete_correct search_term));
                simplify with monad laws);
        bdeleteZeta
  end.

Ltac checksFailed :=
  match goal with
    | [ |- context[ret (_, false)] ] =>
      rewrite refine_pick_val by eauto; simplify with monad laws; reflexivity
  end.

Ltac deleteChecksFailed :=
  match goal with
    | [ |- context[ret (_, [])] ] =>
      simplify with monad laws;
        rewrite refine_pick_val by eauto; simplify with monad laws;
        simpl; reflexivity
  end.

Ltac mutator' AbsR storages :=
  startMethod AbsR; pruneDuplicates; pickIndex;
  repeat ((foreignToQuery || fundepToQuery);
          concretize; asPerm storages; commit);
  Split Constraint Checks; checksSucceeded || checksFailed.

Ltac mutator :=
  match goal with
    | [ |- context[UnConstrFreshIdx _ _] ] =>
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

Ltac delete_preserves_primary_keys :=
    match goal with
        [ |- context [{b |
            ((forall tup tup',
                GetUnConstrRelation ?or ?Ridx tup
                -> GetUnConstrRelation ?or ?Ridx tup' ->
                FunctionalDependency_P ?attr1 ?attr2 _ _)
             -> decides b (DeletePreservesSchemaConstraints
                     (GetUnConstrRelation ?or ?Ridx) ?DeletedTuples
                     ?P)) }]] =>
        rewrite (@DeletePrimaryKeysOK _ or Ridx DeletedTuples
                   attr1 attr2); simplify with monad laws
    end.

Ltac delete_foreign_key_check_to_Query storage :=
    match goal with
        [ |- context [
                 {b'|
                           ?P ->
                           decides b'
                             (DeletePreservesCrossConstraints
                                (GetUnConstrRelation ?qs ?Ridx)
                                (GetUnConstrRelation ?qs ?Ridx')
                                ?DeletedTuples
                                (ForeignKey_P ?attr1 ?attr2 ?tupmap))} ]
        ] => rewrite (@DeleteForeignKeysCheck _ qs Ridx Ridx'
                                                 DeletedTuples)
    end;
      [simplify with monad laws;
        concretize;
        asPerm storage;
        commit
      | auto with typeclass_instances
      | unfold tupleAgree; clear; simpl;
        let H' := fresh in intros; rewrite <- H'; eauto
      | auto with typeclass_instances
      | unfold Iterate_Ensemble_BoundedIndex_filter; simpl; intuition
      | simpl; auto
      ].
