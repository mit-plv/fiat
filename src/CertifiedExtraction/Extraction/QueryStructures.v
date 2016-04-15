Require Import Fiat.ADT.Core.
Require Import Bedrock.Platform.Facade.DFModule.
Require Import Fiat.ADTNotation.
Require Import Bedrock.Platform.Facade.CompileUnit2.
Require Import Fiat.Common.i3list.
Require Import Fiat.Common.ilist3.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import CertifiedExtraction.ADT2CompileUnit.

Require Bedrock.Platform.Facade.examples.QsADTs.
Require Bedrock.Platform.Facade.examples.TuplesF.

(* Require Import Refactor.AllOfLength. *)
(* Require Import Refactor.Deprecated. *)
(* Require Import Refactor.Zip2. *)
(* Require Import Refactor.BinNatUtils. *)
(* Require Import Refactor.FiatBedrockLemmas. *)
(* Require Import Refactor.Basics. *)
(* Require Import Refactor.Decompose. *)
(* Require Import Refactor.TupleToListW. *)
(* Require Import Refactor.EnsemblesOfTuplesAndListW. *)

(* Require Import CertifiedExtraction.Extraction.External.Core. *)
(* Require Import Bedrock.Platform.Facade.examples.QsADTs. *)

Require Import Benchmarks.QueryStructureWrappers.
Require Import Refactor.CallRules.CallRules.
Require Import Refactor.TupleToListW.

Transparent CallBagMethod.
Arguments CallBagMethod : simpl never.
Arguments wrap : simpl never.
Arguments ListWToTuple: simpl never.

Require Import Refactor.Basics.
Require Import Refactor.TupleToListW.
Require Import Refactor.EnsemblesOfTuplesAndListW.

Lemma Lift_Ensemble :
  forall n r idx el,
    Ensembles.In (FiatElement n) r
                 {|
                   IndexedEnsembles.elementIndex := idx;
                   IndexedEnsembles.indexedElement := el |}
    <->
    Ensembles.In (BedrockElement) (IndexedEnsemble_TupleToListW r)
                 {|
                   TuplesF.elementIndex := idx;
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

Definition BagSanityConditions {N} tbl :=
  TuplesF.functional (IndexedEnsemble_TupleToListW (N := N) tbl)
  /\ exists idx, TuplesF.minFreshIndex (IndexedEnsemble_TupleToListW tbl) idx.

Lemma postConditionAdd:
  forall n (r : FiatBag n) el,
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
                eapply CompileSeq with ([[bf as retv]]
                                          :: [[(NTSome (H := h) vdb) <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                                 (QueryStructureSchema.QueryStructureSchemaRaw ProcessScheduler.SchedulerSchema)
                                                                                 (icons3 ProcessScheduler.SearchUpdateTerm inil3) db Fin.F1 (fst retv)) as _]]
                                          :: [[`vsnd <-- snd retv as s]]
                                          :: tenv);
                [ match kwd with
                  | (Some ?v, (None, fun _ => true)) =>
                    let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                    match vkwd with
                    | Some ?vkwd => apply (CompileTuples2_findFirst_spec (* FIXME get (Fin.FS Fin.F1) generically *)
                                            (Fin.FS Fin.F1) (vkey := vkwd) _ (table := prim_fst db))
                    end
                  | (None, (Some ?v, fun _ => true)) =>
                    let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                    match vkwd with
                    | Some ?vkwd => apply (CompileTuples2_findSecond_spec (* FIXME get (Fin.F1) generically *)
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
              let vlst := find_fast (wrap (FacadeWrapper := WrapInstance (H := QS_WrapTupleList)) seq) ext in
              match vlst with
              | Some ?vlst => eapply (CompileTupleList_Empty_spec (vlst := vlst))
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
                                                (fun _ => Cons (NTSome (H := WrapInstance (H := QS_WrapTuple)) vtup) (ret ((ListWToTuple [[[a; b; c]]]): FiatTuple 3)) (fun _ => tenv)));
                    [ | eapply CompileSeq; [ let vtmp := gensym "vtmp" in eapply (CompileTuples2_insert_spec (vtmp := vtmp)) | ] ]
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
              | FiatTuple _ =>
                let v1 := gensym "v1" in
                let v2 := gensym "v2" in
                let v3 := gensym "v3" in
                let o1 := gensym "o1" in
                let o2 := gensym "o2" in
                let o3 := gensym "o3" in
                let vlen := gensym "vlen" in
                let vtmp := gensym "vtmp" in
                apply (CompileTuple_new_spec (v1 := "v1") (v2 := "v2") (v3 := "v3") (o1 := "o1") (o2 := "o2") (o3 := "o3") (vlen := "vlen") (vtmp := "vtmp")); try explode 6
              end
            end).

Ltac _compile_destructor_unsafe vtmp tenv tenv' ::=
     let vtmp2 := gensym "tmp'" in
     let vsize := gensym "size" in
     let vtest := gensym "test" in
     let vhead := gensym "head" in
     first [ unify tenv tenv';
             apply (CompileTupleList_DeleteAny_spec (N := 3) (vtmp := vtmp) (vtmp2 := vtmp2) (vsize := vsize)
                                                    (vtest := vtest) (vhead := vhead))
           | eapply CompileSeq;
             [ apply (CompileTupleList_DeleteAny_spec (N := 3) (vtmp := vtmp) (vtmp2 := vtmp2) (vsize := vsize)
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
               apply (CompileMap_TuplesToWords (N := 3) seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := vtmp))
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
                  [ apply (CompileTuple_Get_spec (N := 3) tup' idx' (vpos := vpos)) |
                    let vtmp := gensym "tmp" in
                    let vsize := gensym "size" in
                    apply (CompileTuple_Delete_spec (vtmp := vtmp) (vsize := vsize)) ]
            end).

Add Parametric Morphism elt
  : (@GLabelMapFacts.UWFacts.WFacts.P.update elt)
    with signature
    (GLabelMap.Equal ==> GLabelMap.Equal ==> GLabelMap.Equal)
      as GLabelMapFacts_UWFacts_WFacts_P_update_morphisn.
Proof.
  apply GLabelMapFacts.UWFacts.WFacts.P.update_m.
Qed.


Add Parametric Morphism av
  : (@RunsTo av)
    with signature
    (GLabelMap.Equal ==> eq ==> StringMap.Equal ==> StringMap.Equal ==> impl)
      as Proper_RunsTo.
Proof.
  unfold impl; intros.
  revert y y1 y2 H0 H1 H.
  induction H2; intros.
  - econstructor; rewrite <- H0, <- H1; eauto.
  - econstructor 2; eauto.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 3; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 4; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H0; apply H.
  - econstructor 5; eauto.
    unfold is_true, eval_bool.
    setoid_rewrite <- H0; apply H.
    eapply IHRunsTo1; eauto.
    reflexivity.
    eapply IHRunsTo2; eauto.
    reflexivity.
  - econstructor 6; eauto.
    unfold is_false, eval_bool.
    setoid_rewrite <- H1; apply H.
    rewrite <- H1, <- H2; eauto.
  - econstructor 7;
    rewrite <- H2; eauto.
    rewrite <- H1; symmetry; eauto.
  - econstructor 8; eauto.
    rewrite <- H8; eauto.
    rewrite <- H6; eauto.
    rewrite <- H6; eauto.
    rewrite <- H7.
    subst st'; subst st'0; rewrite <- H6; eauto.
  - econstructor 9; eauto.
    rewrite <- H9; eauto.
    rewrite <- H7; eauto.
    rewrite <- H7; eauto.
    eapply IHRunsTo; eauto.
    reflexivity.
    reflexivity.
    subst st'; subst st'0; subst output; rewrite <- H8.
    rewrite <- H7; eauto.
Qed.

Add Parametric Morphism av
  : (@Safe av)
    with signature
    (GLabelMap.Equal ==> eq ==> StringMap.Equal ==> impl)
      as Proper_Safe.
Proof.
  unfold impl; intros.
  rewrite <- H0.
  apply Safe_coind with (R := fun st ext => Safe x st ext); eauto.
  - intros; inversion H2; subst; intuition.
    eapply H4.
    setoid_rewrite H; eauto.
  - intros; inversion H2; subst; intuition.
  - intros; inversion H2; substs; intuition.
    left; intuition eauto.
    subst loop; subst loop1; subst loop2.
    rewrite <- H4.
    eapply H8.
    rewrite H; eauto.
  - intros; inversion H2; substs; intuition.
    eauto.
  - intros; inversion H2; substs; intuition.
    + eexists; intuition eauto.
      left; eexists; intuition eauto.
      rewrite <- H; eauto.
    + eexists; intuition eauto.
      right; eexists; intuition eauto.
      rewrite <- H; eauto.
      eapply H12; eauto.
      rewrite H; eauto.
      eapply H12.
      rewrite H; eauto.
Qed.

Add Parametric Morphism av
  : (@ProgOk av)
with signature
(StringMap.Equal ==> GLabelMap.Equal ==> eq ==> eq ==> eq ==> impl)
  as Proper_ProgOk.
Proof.
  unfold impl; intros; intro; intros; split.
  setoid_rewrite <- H0.
  rewrite <- H in H2.
  eapply H1 in H2; intuition.
  rewrite <- H in H2.
  eapply H1 in H2; intuition.
  rewrite <- H.
  eapply H4.
  rewrite H0.
  eauto.
Qed.

Require Import Fiat.Examples.QueryStructure.ProcessScheduler.

Require Import
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.

Definition coDomainWrappers
           av {n n' : nat}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
  := forall midx : Fin.t n', CodWrapperT av (methCod (Vector.nth methSigs midx)).

Definition domainWrappers
           av {n n' : nat}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
  := forall midx : Fin.t n', DomWrapperT av (methDom (Vector.nth methSigs midx)).

Definition DecomposeRep_well_behaved
           av {n n' : nat}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (DecomposeRep : Rep adt -> list (Value av)) :=
  forall x x0 : Rep adt,
    is_same_types (DecomposeRep x0)
                  (DecomposeRep x) = true.

Eval simpl in
  (forall av env P rWrap cWrap dWrap prog,
      (LiftMethod (av := av) env P (DecomposeIndexedQueryStructure _ rWrap) cWrap dWrap prog (Methods PartialSchedulerImpl (Fin.FS (Fin.F1))))).

Definition UnitSigT (P: unit -> Type) :
  P tt -> sigT P :=
  fun s => existT P tt s.

Ltac _repeat_destruct :=
  match goal with
  | _ => apply UnitSigT
  | [  |- forall idx: Fin.t _, _ ] => eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; simpl
  | [  |- GoodWrapper _ _ ] => econstructor; reflexivity
  | [  |- prim_prod _ _ ] => split
  | [  |- prod _ _ ] => split
  | [  |- unit ] => constructor
  end.

Ltac repeat_destruct :=
  repeat _repeat_destruct.

Definition Scheduler_coDomainWrappers
  : coDomainWrappers QsADTs.ADTValue PartialSchedulerImpl.
Proof.
  unfold coDomainWrappers; simpl; repeat_destruct;
  eauto using Good_bool, Good_listW, Good_W.
Defined.

Definition Scheduler_DomainWrappers
  : domainWrappers QsADTs.ADTValue PartialSchedulerImpl.
Proof.
    unfold domainWrappers; simpl; repeat_destruct;
    eauto using Good_bool, Good_listW, Good_W.
Defined.

Definition QueryStructureRepWrapperT
           av (qs_schema : QueryStructureSchema.QueryStructureSchema)
           (qs_schema' := QueryStructureSchema.QueryStructureSchemaRaw
                            qs_schema)
           Index
  := @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema')
                 Schema.RawSchema
                 (fun ns =>
                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                 (fun ns
                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                    @IndexedEnsembles.IndexedEnsemble
                      (@RawTuple (Schema.rawSchemaHeading ns)))
                 (QueryStructureSchema.qschemaSchemas qs_schema') Index.

Definition Scheduler_RepWrapperT Index
  : QueryStructureRepWrapperT QsADTs.ADTValue SchedulerSchema Index.
Proof.
  unfold QueryStructureRepWrapperT; simpl; split.
  apply (@QS_WrapBag2 3 1 0).   (* FIXME generalize *)
  constructor.
Defined.

Definition Scheduler_DecomposeRep_well_behaved av qs_schema Index
(rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

  :=
  (fun r r' : IndexedQueryStructure qs_schema Index =>
     DecomposePrei3list_Agree _ _ rWrap
                              (id r) (id r')).

Definition DecomposeIndexedQueryStructure' av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  Decomposei3list _ _ rWrap (id r).

Definition DecomposeIndexedQueryStructurePost' av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r r' : IndexedQueryStructure qs_schema Index) :=
  DecomposePosti3list _ _ rWrap (id r) (id r').

Definition DecomposeIndexedQueryStructurePre' av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) :=
  DecomposePrei3list _ _ rWrap (id r).

Lemma GLabelMapFacts_map_add_1 :
  (* This is a hack to transform a rewrite into an apply (setoid-rewrite is too slow). *)
  forall (elt B : Type) (f : elt -> B) (k : GLabelMapFacts.M.key) (v : elt) (m : GLabelMapFacts.M.t elt) m0,
    GLabelMapFacts.M.Equal (GLabelMapFacts.M.map f m) m0 ->
    GLabelMapFacts.M.Equal (GLabelMapFacts.M.map f (m ### k ->> v)) (m0 ### k ->> f v).
Proof.
  intros * H; rewrite GLabelMapFacts.map_add, H; reflexivity.
Qed.

Ltac GLabelMap_fast_apply_map :=
  (* This tactic simplifies an expression like [map f (add k1 v1 (add ...))]
     into [add k1 (f v1) (add ...)]. Using setoid_rewrite repeatedly was too
     slow, so it relies on a separate lemma and an evar to do its job. *)
  match goal with (* Not a lazy match: not all [map]s can be removed *)
  | [  |- context[GLabelMap.map ?f ?m] ] =>
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
      setoid_rewrite __eq; clear __eq
    end
  end.

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
  | [  |- BagSanityConditions (Ensembles.Add _ _ _) ] => apply postConditionAdd
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
  ### ("ADT", "Tuple_new") ->> (QsADTs.Tuple_new)
  ### ("ADT", "Tuple_delete") ->> (QsADTs.Tuple_delete)
  ### ("ADT", "Tuple_copy") ->> ( QsADTs.Tuple_copy)
  ### ("ADT", "Tuple_get") ->> ( QsADTs.Tuple_get)
  ### ("ADT", "Tuple_set") ->> ( QsADTs.Tuple_set)

  ### ("ADT", "WordList_new") ->> ( QsADTs.WordList_new)
  ### ("ADT", "WordList_delete") ->> ( QsADTs.WordList_delete)
  ### ("ADT", "WordList_pop") ->> ( QsADTs.WordList_pop)
  ### ("ADT", "WordList_empty") ->> ( QsADTs.WordList_empty)
  ### ("ADT", "WordList_push") ->> ( QsADTs.WordList_push)
  ### ("ADT", "WordList_copy") ->> ( QsADTs.WordList_copy)
  ### ("ADT", "WordList_rev") ->> ( QsADTs.WordList_rev)
  ### ("ADT", "WordList_length") ->> ( QsADTs.WordList_length)

  ### ("ADT", "TupleList_new") ->> ( QsADTs.TupleList_new)
  ### ("ADT", "TupleList_delete") ->> ( QsADTs.TupleList_delete)
  ### ("ADT", "TupleList_copy") ->> ( QsADTs.TupleList_copy)
  ### ("ADT", "TupleList_pop") ->> ( QsADTs.TupleList_pop)
  ### ("ADT", "TupleList_empty") ->> ( QsADTs.TupleList_empty)
  ### ("ADT", "TupleList_push") ->> ( QsADTs.TupleList_push)
  ### ("ADT", "TupleList_rev") ->> ( QsADTs.TupleList_rev)
  ### ("ADT", "TupleList_length") ->> ( QsADTs.TupleList_length)

  ### ("ADT", "Tuples0_new") ->> ( QsADTs.Tuples0_new)
  ### ("ADT", "Tuples0_insert") ->> ( QsADTs.Tuples0_insert)
  ### ("ADT", "Tuples0_enumerate") ->> ( QsADTs.Tuples0_enumerate)

  ### ("ADT", "Tuples1_new") ->> ( QsADTs.Tuples1_new)
  ### ("ADT", "Tuples1_insert") ->> ( QsADTs.Tuples1_insert)
  ### ("ADT", "Tuples1_find") ->> ( QsADTs.Tuples1_find)
  ### ("ADT", "Tuples1_enumerate") ->> ( QsADTs.Tuples1_enumerate)

  ### ("ADT", "Tuples2_new") ->> ( QsADTs.Tuples2_new)
  ### ("ADT", "Tuples2_insert") ->> ( QsADTs.Tuples2_insert)
  ### ("ADT", "Tuples2_findBoth") ->> ( QsADTs.Tuples2_findBoth)
  ### ("ADT", "Tuples2_findFirst") ->> ( QsADTs.Tuples2_findFirst)
  ### ("ADT", "Tuples2_findSecond") ->> ( QsADTs.Tuples2_findSecond)
  ### ("ADT", "Tuples2_enumerate") ->> ( QsADTs.Tuples2_enumerate).
