Require Import
        CertifiedExtraction.Extraction.QueryStructures.Basics
        CertifiedExtraction.Extraction.QueryStructures.TupleToListW
        CertifiedExtraction.Extraction.QueryStructures.EnsemblesOfTuplesAndListW
        CertifiedExtraction.Extraction.QueryStructures.CallRules.CallRules.

Require Import CertifiedExtraction.Extraction.QueryStructures.Wrappers.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Require Import Bedrock.Platform.Facade.CompileUnit2.

Require Export
        CertifiedExtraction.ADT2CompileUnit
        CertifiedExtraction.Extraction.Extraction
        CertifiedExtraction.Extraction.QueryStructures.Decompose.

Require Import
        Bedrock.Memory
        Bedrock.Platform.Facade.DFModule
        Bedrock.Platform.Facade.CompileUnit2.

Transparent CallBagMethod.
Arguments CallBagMethod : simpl never.
Arguments wrap : simpl never.
Arguments ListWToTuple: simpl never.

Definition BagSanityConditions {N} tbl :=
  TuplesF.functional (IndexedEnsemble_TupleToListW (N := N) tbl)
  /\ exists idx, TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW tbl) idx.

Lemma Lift_Ensemble :
  forall n r idx (el: FiatWTuple n),
    Ensembles.In _ r
                 {| IndexedEnsembles.elementIndex := idx;
                    IndexedEnsembles.indexedElement := el |} <->
    Ensembles.In _ (IndexedEnsemble_TupleToListW r)
                 {| TuplesF.elementIndex := idx;
                    TuplesF.indexedElement := TupleToListW el |}.
Proof.
  split; intros.
  - econstructor; intuition eauto.
    unfold RelatedIndexedTupleAndListW; split; simpl; eauto.
  - destruct H;  unfold RelatedIndexedTupleAndListW in *; intuition.
    simpl in *; subst.
    destruct x; simpl in *; subst.
    unfold TupleToListW in H2.
    apply ilist2ToListW_inj in H2; subst; eauto.
Qed.

Lemma BagSanityConditions_Add:
  forall n (r : FiatWBag n) el,
    TuplesF.functional (IndexedEnsemble_TupleToListW r) ->
    IndexedEnsembles.UnConstrFreshIdx r (IndexedEnsembles.elementIndex el) ->
    BagSanityConditions (Ensembles.Add IndexedEnsembles.IndexedElement r el).
Proof.
  split; unfold TuplesF.functional, TuplesF.minFreshIndex; intros; intuition.
  - destruct t1; destruct t2; simpl in *; subst; f_equal.
    destruct H2; destruct H1; intuition.
    destruct H2; destruct H3; subst.
    + unfold TuplesF.tupl in *.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition.
      subst.
      destruct x; destruct x0; simpl in *; subst.
      apply Lift_Ensemble in H2; apply Lift_Ensemble in H1.
      pose proof (H _ _ H1 H2 (eq_refl _)); injections; eauto.
    + destruct H2.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      destruct x0; destruct el; simpl in *; subst.
      unfold TuplesF.UnConstrFreshIdx in H1.
      unfold IndexedEnsembles.UnConstrFreshIdx in H0.
      apply H0 in H1; simpl in *.
      omega.
    + destruct H1.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      destruct x; destruct el; simpl in *; subst.
      unfold IndexedEnsembles.UnConstrFreshIdx in H0.
      apply H0 in H2; simpl in *.
      omega.
    + destruct H2; destruct H1.
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      reflexivity.
  - exists (S (IndexedEnsembles.elementIndex el)); split.
    + unfold TuplesF.UnConstrFreshIdx in *; intros.
      destruct H1 as [? [? ? ] ].
      unfold RelatedIndexedTupleAndListW in *; simpl in *; intuition; subst.
      destruct element; simpl in *; subst.
      * destruct H1.
        destruct x; simpl in *.
        apply H0 in H1; simpl in *; omega.
        destruct H1; omega.
    + intros.
      inversion H1; subst.
      unfold TuplesF.UnConstrFreshIdx in *.
      assert (lt (TuplesF.elementIndex (IndexedElement_TupleToListW el)) (IndexedEnsembles.elementIndex el) ).
      eapply H2.
      econstructor; split.
      unfold Ensembles.Add.
      econstructor 2.
      reflexivity.
      unfold RelatedIndexedTupleAndListW; eauto.
      destruct el; simpl in *; omega.
      unfold TuplesF.UnConstrFreshIdx in *; intros.
      assert (lt (IndexedEnsembles.elementIndex el) idx').
      eapply (H2 {| TuplesF.elementIndex := _;
                    TuplesF.indexedElement := _ |}); simpl.
      unfold IndexedEnsemble_TupleToListW.
      simpl; eexists; split.
      econstructor 2.
      reflexivity.
      unfold RelatedIndexedTupleAndListW; simpl; split; eauto.
      omega.
Qed.

Ltac _compile_CallBagFind :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (Cons (NTSome (H := ?h) ?vdb) (ret (prim_fst ?db)) (fun _ => ?tenv), Cons NTNone ?bf _) =>
              match bf with
              | CallBagMethod Fin.F1 BagFind ?db ?kwd =>
                let vsnd := gensym "snd" in
                let vtmp := gensym "tmp" in
                eapply CompileSeq
                with ([[bf as retv]]
                        :: [[(NTSome (H := h) vdb)
                              ->> prim_fst (Refinements.UpdateIndexedRelation
                                            (QueryStructureSchema.QueryStructureSchemaRaw
                                               ProcessScheduler.SchedulerSchema)
                                            (icons3 ProcessScheduler.SearchUpdateTerm inil3)
                                            db Fin.F1 (fst retv)) as _]]
                        :: [[`vsnd ->> snd retv as s]]
                        :: tenv);
                [ match kwd with
                  | (Some ?v, (None, fun _ => true)) =>
                    let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                    match vkwd with
                    | Some ?vkwd => apply (WBagOfTuples2Compilation.CompileFindFirst_spec
                                            (* FIXME get (Fin.FS Fin.F1) generically *)
                                            (Fin.FS Fin.F1) (vkey := vkwd) _ (table := prim_fst db))
                    end
                  | (None, (Some ?v, fun _ => true)) =>
                    let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                    match vkwd with
                    | Some ?vkwd => apply (WBagOfTuples2Compilation.CompileFindSecond_spec
                                            (* FIXME get (Fin.F1) generically *)
                                            _ (Fin.F1) (vkey := vkwd) (table := prim_fst db))
                    end
                  end | ]
              end
            end).

Ltac _compile_length :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?pre, Cons ?k (ret (bool2w (EqNat.beq_nat (Datatypes.length (rev ?seq)) 0))) (fun _ => ?pre')) =>
              let vlst := find_fast (wrap (FacadeWrapper := WrapInstance (H := QS_WrapFiatWTupleList)) seq) ext in
              match vlst with
              | Some ?vlst => eapply (WTupleListCompilation.CompileEmpty_spec (idx := 3) (vlst := vlst))
              end
            end).


Ltac _compile_CallBagInsert := (* FIXME should do the insert in the second branch *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (Cons (NTSome (H := ?h) ?vrep) (ret ?db) (fun _ => ?tenv),
               Cons NTNone ?bm (fun a => Cons ?vret _ (fun _ => Cons (NTSome ?vrep') (ret a) (fun _ => ?tenv')))) =>
              unify vrep vrep';
                match bm with
                | (CallBagMethod _ BagInsert _ (ilist2.icons2 ?a (ilist2.icons2 ?b (ilist2.icons2 ?c ilist2.inil2)))) =>
                  let vtmp := gensym "tmp" in
                  let vtup := gensym "tup" in
                  (* match pre with *)
                  change (ilist2.icons2 a (ilist2.icons2 b (ilist2.icons2 c ilist2.inil2))) with (ListWToTuple [[[a; b; c]]]);
                    apply CompileSeq with (Cons (NTSome (H := h) vrep) (ret db)
                                                (fun _ => Cons (NTSome (H := WrapInstance (H := WTupleCompilation.FiatWrapper)) vtup) (ret ((ListWToTuple [[[a; b; c]]]): FiatWTuple 3)) (fun _ => tenv)));
                    [ | eapply CompileSeq; [ let vtmp := gensym "vtmp" in eapply (WBagOfTuples2Compilation.CompileInsert_spec (vtmp := vtmp)) | ] ]
                end
            end).


Ltac explode n :=
  match n with
  | 0 => idtac
  | S ?n =>
    compile_do_use_transitivity_to_handle_head_separately;
      [ | apply ProgOk_Chomp_Some; [ | intros; explode n ] ]
  end.

Ltac _compile_allocTuple :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:((pre, post)) with
            | (?pre, Cons ?k (ret ?tup) (fun _ => ?pre)) =>
              match type of tup with
              | FiatWTuple _ =>
                let v1 := gensym "v1" in
                let v2 := gensym "v2" in
                let v3 := gensym "v3" in
                let o1 := gensym "o1" in
                let o2 := gensym "o2" in
                let o3 := gensym "o3" in
                let vlen := gensym "vlen" in
                let vtmp := gensym "vtmp" in
                apply (WTupleCompilation.CompileNew_spec (v1 := "v1") (v2 := "v2") (v3 := "v3") (o1 := "o1") (o2 := "o2") (o3 := "o3") (vlen := "vlen") (vtmp := "vtmp")); try explode 6
              end
            end).

Ltac _compile_destructor_unsafe vtmp tenv tenv' ::=
     let vtmp2 := gensym "tmp'" in
     let vsize := gensym "size" in
     let vtest := gensym "test" in
     let vhead := gensym "head" in
     first [ unify tenv tenv';
             apply (WTupleListCompilation.CompileDeleteAny_spec
                      (N := 3) (vtmp := vtmp) (vtmp2 := vtmp2) (vsize := vsize)
                      (vtest := vtest) (vhead := vhead))
           | eapply CompileSeq;
             [ apply (WTupleListCompilation.CompileDeleteAny_spec
                        (N := 3) (vtmp := vtmp) (vtmp2 := vtmp2) (vsize := vsize)
                        (vtest := vtest) (vhead := vhead)) | ] ].

Lemma map_rev_def :
  forall {A B} f seq,
    @map A B f (rev seq) = revmap f seq.
Proof.
  intros; reflexivity.
Qed.

Ltac _compile_map ::= (* ‘_compile_map’ from the stdlib uses generic push-pop methods *)
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             let vhead := gensym "head" in
             let vhead' := gensym "head'" in
             let vtest := gensym "test" in
             let vtmp := gensym "tmp" in
             match constr:((pre, post)) with
             | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (revmap _ ?seq')) ?tenv') =>
               unify seq seq';
               apply (WTupleListCompilation.CompileMap_TuplesToWords
                        (N := 3) seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := vtmp))
             end).

Ltac _compile_get :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtmp := gensym "tmp" in
            match constr:((pre, post)) with
            | (Cons (NTSome (H:=?h) ?k) (ret ?tup) ?tenv, Cons (NTSome (H:=?h') ?k') (ret (GetAttributeRaw ?tup' ?idx')) _) =>
              unify tup tup';
                let vpos := gensym "pos" in
                eapply CompileSeq with (Cons (NTSome (H:=h) k) (ret tup)
                                             (fun a => Cons (NTSome (H:=h') k') (ret (ilist2.ith2 tup' idx'))
                                                         (fun _ => tenv a)));
                  [ apply (WTupleCompilation.CompileGet_spec (N := 3) tup' idx' (vpos := vpos)) |
                    let vtmp := gensym "tmp" in
                    let vsize := gensym "size" in
                    apply (WTupleCompilation.CompileDelete_spec (vtmp := vtmp) (vsize := vsize)) ]
            end).

Lemma GLabelMapFacts_map_add_1 :
  (* This is a hack to transform a rewrite into an apply (setoid_rewrite is too slow). *)
  forall (elt B : Type) (f : elt -> B) (k : GLabelMapFacts.M.key) (v : elt) (m : GLabelMapFacts.M.t elt) m0,
    GLabelMapFacts.M.Equal (GLabelMapFacts.M.map f m) m0 ->
    GLabelMapFacts.M.Equal (GLabelMapFacts.M.map f (m ### k ->> v)) (m0 ### k ->> f v).
Proof.
  intros * H; rewrite GLabelMapFacts.map_add, H; reflexivity.
Qed.

Require Import Fiat.CertifiedExtraction.PureFacadeLemmas.

Ltac GLabelMap_fast_apply_map :=
  (* This tactic simplifies an expression like [map f (add k1 v1 (add ...))]
     into [add k1 (f v1) (add ...)]. Using setoid_rewrite repeatedly was too
     slow, so it relies on a separate lemma and an evar to do its job. *)
  etransitivity;
  [ |
    match goal with
    | [  |- GLabelMap.Equal ?ev ?complex_expr ] =>
      match complex_expr with (* Not a lazy match: not all [GLabelMap.map]s can be removed *)
      | context Ctx [GLabelMap.map ?f ?m] =>
        lazymatch type of f with
        | ?elt -> ?elt' =>
          let m' := fresh in
          evar (m' : GLabelMap.t elt');
          (* This block is essentially [setoid_replace (GLabelMap.map f m) m'] with
               relation [@GLabelMap.Equal elt'], but it fails before calling the setoid
               machinery if the relation doesn't actually hold. *)
          let __eq := fresh in
          assert (@GLabelMap.Equal elt' (GLabelMap.map f m) m') as __eq;
          [ unfold m' in *; clear m'; try unfold m;
            solve [repeat apply GLabelMapFacts_map_add_1; apply GLabelMapFacts.map_empty] | ];
          (* Now that we have an equality between subterms, plug it in the larger term *)
          (* This because setoid_rewrite __eq took one hour *)
          let simpler_term := context Ctx[m'] in
          unify ev simpler_term;
          symmetry in __eq;
          repeat match goal with
                 | [  |- GLabelMap.Equal ?x ?x ] => reflexivity
                 | [  |- GLabelMap.Equal (GLabelMapFacts.UWFacts.WFacts.P.update _ _)
                                        (GLabelMapFacts.UWFacts.WFacts.P.update _ _) ] =>
                   apply GLabelMapFacts_UWFacts_WFacts_P_update_morphism
                 | _ => exact __eq
                 end
        end
      end
    end ].

Ltac _compile_cleanup_env_helper :=
  GLabelMap_fast_apply_map;
  GLabelMap_fast_apply_map;
  reflexivity.

Ltac __compile_cleanup_env :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match env with
            | GLabelMapFacts.UWFacts.WFacts.P.update _ _ =>
              eapply Proper_ProgOk; [ reflexivity | _compile_cleanup_env_helper | reflexivity.. | idtac ];
              match_ProgOk ltac:(fun prog pre post ext env => set env)
            end).

Ltac __compile_prepare_merged_env_for_compile_do_side_conditions :=
  lazymatch goal with
  | [ |- GLabelMap.MapsTo _ _ ?env ] =>
    lazymatch eval unfold env in env with
    | GLabelMapFacts.UWFacts.WFacts.P.update _ _ =>
      unfold env; apply GLabelMapFacts.UWFacts.WFacts.P.update_mapsto_iff; left
    end
  end.

Ltac __compile_pose_query_structure :=
  (* Removing this pose makes the [apply CompileTuples2_findFirst_spec] loop.
     No idea why. *)
  match goal with
  | [ r: IndexedQueryStructure _ _ |- _ ] =>
    match goal with
    | [ r' := _ : IndexedQueryStructure _ _ |- _ ] => fail 1
    | _ => pose r
    end
  end.

Ltac __compile_discharge_bag_side_conditions_step :=
  match goal with
  | _ => cleanup
  | _ => progress injections
  | _ => progress simpl in *
  | _ => progress computes_to_inv
  | _ => progress unfold CallBagMethod in *
  | _ => progress (find_if_inside; simpl in * )
  | [  |- BagSanityConditions (Ensembles.Add _ _ _) ] => apply BagSanityConditions_Add
  | [  |- BagSanityConditions _ ] => split; solve [intuition eauto]
  | _ => eassumption
  end.

Ltac __compile_discharge_bag_side_conditions_internal :=
  solve [repeat __compile_discharge_bag_side_conditions_step].

Ltac __compile_discharge_bag_side_conditions :=
  match goal with
  | [  |- TuplesF.functional _ ] => __compile_discharge_bag_side_conditions_internal
  | [  |- TuplesF.minFreshIndex _ _ ] => __compile_discharge_bag_side_conditions_internal
  | [  |- BagSanityConditions _ ] => __compile_discharge_bag_side_conditions_internal
  end.

Ltac __compile_unfold :=
     match goal with
     | _ => progress unfold If_Then_Else in *
     end.

Ltac __compile_clear_bodies_of_ax_spec :=
  repeat (unfold GenExports, map_aug_mod_name, aug_mod_name,
          GLabelMapFacts.uncurry; simpl);
  repeat lazymatch goal with
    | |- context[GenAxiomaticSpecs ?a0 ?a1 ?a2 ?a3 ?a4 ?a5 ?a6 ?a7] =>
      let a := fresh in
      pose (GenAxiomaticSpecs a0 a1 a2 a3 a4 a5 a6 a7) as a;
      change (GenAxiomaticSpecs a0 a1 a2 a3 a4 a5 a6 a7) with a;
      clearbody a
    end.

Ltac __compile_start_compiling_module imports :=
  lazymatch goal with
  | [  |- sigT (fun _ => BuildCompileUnit2TSpec  _ _ _ _ _ _ _ _ _ _ _ _ _ _ ) ] =>
    eexists;
    unfold DecomposeIndexedQueryStructure', DecomposeIndexedQueryStructurePre', DecomposeIndexedQueryStructurePost';
    eapply (BuildCompileUnit2T' imports); try apply eq_refl (* reflexivity throws an Anomaly *)
  | [  |- forall _: (Fin.t _), (sigT _)  ] =>
    __compile_clear_bodies_of_ax_spec;
    eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; repeat (apply Build_prim_prod || exact tt)
  end.

Ltac __compile_start_compiling_method :=
  lazymatch goal with
  | [  |- sigT (fun (_: Stmt) => _) ] =>
    eexists; repeat match goal with
                    | _ => progress simpl
                    | _ => progress intros
                    | [  |- _ /\ _ ] => split
                    end
  end.

Ltac __compile_decide_NoDup :=
  repeat lazymatch goal with
    | [  |- NoDup _ ] => econstructor
    | [  |- not (List.In _ _) ] => simpl; intuition congruence
    end.

Ltac __compile_start_compiling_step imports :=
  match goal with
  | [ H: BagSanityConditions _ |- _ ] => destruct H as [ ? [ ? ? ] ]
  | _ => __compile_start_compiling_module imports
  | _ => __compile_start_compiling_method
  | _ => __compile_discharge_bag_side_conditions
  | _ => __compile_decide_NoDup
  end.

Ltac __compile_method_step :=
  match goal with
  | _ => __compile_unfold
  | _ => __compile_cleanup_env
  | _ => __compile_pose_query_structure
  | _ => __compile_prepare_merged_env_for_compile_do_side_conditions
  | _ => __compile_discharge_bag_side_conditions
  | _ => _compile_step
  | _ => _compile_CallBagFind
  | _ => _compile_CallBagInsert
  | _ => _compile_length
  | _ => _compile_allocTuple
  | _ => _compile_get
  | _ => apply CompileConstantBool
  | _ => reflexivity
  | _ => progress simpl
  | _ => setoid_rewrite map_rev_def
  end.

Ltac _compile env :=
  repeat __compile_start_compiling_step env;
  repeat __compile_method_step.

Transparent Vector.to_list.

Definition QSEnv_Ax : GLabelMap.t (AxiomaticSpec QsADTs.ADTValue) :=
  (GLabelMap.empty _)
  ### ("ADT", "WordList_new") ->> (QsADTs.WordListADTSpec.New)
  ### ("ADT", "WordList_delete") ->> (QsADTs.WordListADTSpec.Delete)
  ### ("ADT", "WordList_pop") ->> (QsADTs.WordListADTSpec.Pop)
  ### ("ADT", "WordList_empty") ->> (QsADTs.WordListADTSpec.Empty)
  ### ("ADT", "WordList_push") ->> (QsADTs.WordListADTSpec.Push)
  ### ("ADT", "WordList_copy") ->> (QsADTs.WordListADTSpec.Copy)
  ### ("ADT", "WordList_rev") ->> (QsADTs.WordListADTSpec.Rev)
  ### ("ADT", "WordList_length") ->> (QsADTs.WordListADTSpec.Length)

  ### ("ADT", "WTuple_new") ->> (QsADTs.WTupleADTSpec.New)
  ### ("ADT", "WTuple_delete") ->> (QsADTs.WTupleADTSpec.Delete)
  ### ("ADT", "WTuple_copy") ->> (QsADTs.WTupleADTSpec.Copy)
  ### ("ADT", "WTuple_get") ->> (QsADTs.WTupleADTSpec.Get)
  ### ("ADT", "WTuple_put") ->> (QsADTs.WTupleADTSpec.Put)

  ### ("ADT", "WTupleList_new") ->> (QsADTs.WTupleListADTSpec.New)
  ### ("ADT", "WTupleList_delete") ->> (QsADTs.WTupleListADTSpec.Delete)
  ### ("ADT", "WTupleList_copy") ->> (QsADTs.WTupleListADTSpec.Copy)
  ### ("ADT", "WTupleList_pop") ->> (QsADTs.WTupleListADTSpec.Pop)
  ### ("ADT", "WTupleList_empty") ->> (QsADTs.WTupleListADTSpec.Empty)
  ### ("ADT", "WTupleList_push") ->> (QsADTs.WTupleListADTSpec.Push)
  ### ("ADT", "WTupleList_rev") ->> (QsADTs.WTupleListADTSpec.Rev)
  ### ("ADT", "WTupleList_length") ->> (QsADTs.WTupleListADTSpec.Length)

  ### ("ADT", "WBagOfTuples0_new") ->> (QsADTs.WBagOfTuples0ADTSpec.New)
  ### ("ADT", "WBagOfTuples0_insert") ->> (QsADTs.WBagOfTuples0ADTSpec.Insert)
  ### ("ADT", "WBagOfTuples0_enumerate") ->> (QsADTs.WBagOfTuples0ADTSpec.Enumerate)

  ### ("ADT", "WBagOfTuples1_new") ->> (QsADTs.WBagOfTuples1ADTSpec.New)
  ### ("ADT", "WBagOfTuples1_insert") ->> (QsADTs.WBagOfTuples1ADTSpec.Insert)
  ### ("ADT", "WBagOfTuples1_find") ->> (QsADTs.WBagOfTuples1ADTSpec.Find)
  ### ("ADT", "WBagOfTuples1_enumerate") ->> (QsADTs.WBagOfTuples1ADTSpec.Enumerate)

  ### ("ADT", "WBagOfTuples2_new") ->> (QsADTs.WBagOfTuples2ADTSpec.New)
  ### ("ADT", "WBagOfTuples2_insert") ->> (QsADTs.WBagOfTuples2ADTSpec.Insert)
  ### ("ADT", "WBagOfTuples2_findBoth") ->> (QsADTs.WBagOfTuples2ADTSpec.FindBoth)
  ### ("ADT", "WBagOfTuples2_findFirst") ->> (QsADTs.WBagOfTuples2ADTSpec.FindFirst)
  ### ("ADT", "WBagOfTuples2_findSecond") ->> (QsADTs.WBagOfTuples2ADTSpec.FindSecond)
  ### ("ADT", "WBagOfTuples2_enumerate") ->> (QsADTs.WBagOfTuples2ADTSpec.Enumerate).
