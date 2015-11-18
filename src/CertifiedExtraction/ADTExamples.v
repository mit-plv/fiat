Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Examples
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Definition CodWrapperT av (Cod : option Type) :=
  match Cod with
  | None => unit
  | Some CodT => FacadeWrapper (Value av) CodT
  end.

Fixpoint DomWrapperT av (Dom : list Type) : Type :=
  match Dom with
  | nil => unit
  | cons DomT Dom' => prod (FacadeWrapper (Value av) DomT)
                           (DomWrapperT av Dom')
  end.

Definition nthArgName n := "arg" ++ (NumberToString n).
Definition nthRepName n := "rep" ++ (NumberToString n).

Fixpoint LiftMethod' (av : Type) (env : Env av) {Rep} {Cod} {Dom}
         (f : Rep -> Telescope av)
         {struct Dom}
  :=
  match Dom return
        CodWrapperT av Cod
        -> DomWrapperT av Dom
        -> Stmt
        -> Telescope av
        -> methodType' Rep Dom Cod
        -> Prop with
  | nil => match Cod return
                 CodWrapperT av Cod
                 -> DomWrapperT av nil
                 -> Stmt
                 -> Telescope av
                 -> methodType' Rep nil Cod
                 -> Prop with
           | None => fun cWrap dWrap prog pre meth =>
                       {{ pre }}
                         prog
                         {{ [[meth as database]] :: (f database) }} ∪ {{ StringMap.empty _ }} // env

           | Some CodT => fun cWrap dWrap prog pre meth =>
                            let v : FacadeWrapper (Value av) CodT := cWrap in
                            {{ pre }}
                              prog
                              {{[[meth as mPair]]
                                  :: [[`"ret" <-- snd mPair as _]]
                                  :: (f (fst mPair))}}  ∪ {{ StringMap.empty _ }} // env
           end
  | cons DomT Dom' =>
    fun cWrap dWrap prog tele meth =>
      forall d, let _ := fst dWrap in LiftMethod' env Dom' f cWrap (snd dWrap) prog ([[ (NTSome (nthArgName (List.length Dom'))) <-- d as _]] :: tele) (meth d)
  end.

Definition LiftMethod
           (av : Type)
           env
         {Rep}
         {Cod}
         {Dom}
         (f : Rep -> Telescope av)
         (cWrap : CodWrapperT av Cod)
         (dWrap : DomWrapperT av Dom)
         (prog : Stmt)
         (meth : methodType Rep Dom Cod)
  : Prop :=
  forall r, LiftMethod' env Dom f cWrap dWrap prog (f r) (meth r).
Arguments LiftMethod [_] _ {_ _ _} _ _ _ _ _ / .

Fixpoint RepWrapperT
           av
           {n}
           {A : Type}
           {B : A -> Type}
           (C : forall a, B a -> Type)
           (As : Vector.t A n)
           : ilist3 (B := B) As -> Type :=
  match As return ilist3 (B := B) As -> Type with
  | Vector.nil =>
    fun il => unit
  | Vector.cons a _ As' =>
    fun il =>
      prod (FacadeWrapper (Value av) (C a (prim_fst il)))
           (RepWrapperT av C _ (prim_snd il))
  end.

Fixpoint Decomposei3list
           av
           {n}
           {A}
           {B}
           {C}
           {As : Vector.t n A}
           {struct As}
  :
    forall (il : ilist3 (B := B) As),
      RepWrapperT av C As il
      -> i3list C il
      -> Telescope av :=
  match As return
        forall (il : ilist3 (B := B) As),
          RepWrapperT av C As il
          -> i3list C il
          -> Telescope av with
  | Vector.nil => fun as' rWrap r => Nil
  | Vector.cons a n' As' => fun as' rWrap r =>
                              let fWrap' := fst rWrap in
                              Cons (NTSome (nthRepName n')) (ret (prim_fst r)) (fun _ => Decomposei3list As' (prim_snd as') (snd rWrap) (prim_snd r))
  end.

Definition DecomposeIndexedQueryStructure av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index) : Telescope av :=
  Decomposei3list _ _ rWrap r.
Arguments DecomposeIndexedQueryStructure _ {_ _} _ _ /.
Arguments NumberToString _ / .

Eval simpl in
  (forall av env rWrap cWrap dWrap prog,
      (LiftMethod (av := av) env (DecomposeIndexedQueryStructure _ rWrap) cWrap dWrap prog (Methods PartialSchedulerImpl (Fin.FS (Fin.F1))))).

Require Import Bedrock.Platform.Facade.DFModule.
Require Import Fiat.ADTNotation.

Fixpoint NumUpTo n acc := 
  match n with
  | 0 => acc
  | S n' => NumUpTo n' (n' :: acc)
  end.

Definition BuildArgNames n m :=
  List.app (map nthArgName (NumUpTo n nil))
           (map nthRepName (NumUpTo m nil)).
Compute (BuildArgNames 3 5).

Definition Shelve {A} (a : A) := True.

Definition DFModuleEquiv
           av
           env
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (module : DFModule av)
           (consWrapper' : forall midx, CodWrapperT av (methCod (Vector.nth methSigs midx)))
           (domWrapper : forall midx, DomWrapperT av (methDom (Vector.nth methSigs midx)))
           (f : Core.Rep adt -> Telescope av)
           (DecomposeRepCount : nat)
  : Prop :=
  (* Environments match *)
  (* FIXME : (module.(Imports) = env) *)
  (* Method Correspondence *)
  (forall midx : Fin.t n',
      let meth := Vector.nth methSigs midx in 
      exists Fun,
        Fun.(Core).(RetVar) = "ret"
        /\ Fun.(Core).(ArgVars) = BuildArgNames (List.length (methDom meth)) DecomposeRepCount
        /\ LiftMethod env f (consWrapper' midx) (domWrapper midx) (Body (Core Fun))
                      (Methods adt midx)
        /\ (StringMap.MapsTo (methID meth) Fun module.(Funs))
        /\ Shelve Fun).

Definition BuildFacadeModuleT
           av
           (env : Env av)
           {A}
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : Core.ADT (BuildADTSig consSigs methSigs))
           (f : A -> _)
           g
  := {module : _ &
      {cWrap : _ &
       {dWrap : _ &
        {rWrap : _ & DFModuleEquiv env adt module cWrap dWrap (f rWrap) g } } } } .

Arguments nthRepName _ / .
Arguments nthArgName _ / .
Arguments BuildArgNames !n !m / .

Ltac makeEvar T k :=
  let x := fresh in evar (x : T); let y := eval unfold x in x in clear x; k y.

Ltac list_of_evar B n k :=
  match n with
  | 0 => k (@nil B)
  | S ?n' =>
    makeEvar B ltac:(fun b =>
                       list_of_evar
                         B n' ltac:(fun Bs => k (cons b Bs)))
  end.

Fixpoint BuildStringMap {A} (k : list string) (v : list A) : StringMap.t A :=
  match k, v with
  | cons k ks, cons v vs => StringMap.add k v (BuildStringMap ks vs)
  | _, _ => StringMap.empty A 
  end.
  
Definition BuildFacadeModule
           av
           (env : Env av)
  : BuildFacadeModuleT env PartialSchedulerImpl (DecomposeIndexedQueryStructure av)
                       (QueryStructureSchema.numQSschemaSchemas SchedulerSchema).
Proof.
  lazymatch goal with
    |- BuildFacadeModuleT _ ?adt _ _ =>
  let sig := match type of adt with Core.ADT ?sig => sig end in
    let methSigs := match sig with
                      DecADTSig ?DecSig => constr:(MethodNames DecSig) end in
    let methIdx := eval compute in (MethodIndex sig) in 
        match methIdx with
        | Fin.t ?n =>
          list_of_evar DFFun n ltac:(fun z => eexists {| Funs := BuildStringMap (Vector.fold_right cons methSigs nil) z |})
        end
  end.
  do 3 eexists.
  simpl; unfold DFModuleEquiv.
  eapply Fiat.Common.IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv.
  simpl; repeat split;
  eexists {| Core := {| Body := Assign "ret" (Const 0) |};
             compiled_syntax_ok := _ |};
  simpl; repeat (apply conj); try exact (eq_refl); try decide_mapsto_maybe_instantiate;

  try match goal with
  |- Shelve
      {|
        Core := {|
                 ArgVars := _;
                 RetVar := _;
                 Body := _;
                 args_no_dup := ?a;
                 ret_not_in_args := ?b;
                 no_assign_to_args := ?c;
                 args_name_ok := ?d;
                 ret_name_ok := ?e;
                 syntax_ok := ?f |};
        compiled_syntax_ok := ?g |} =>
  try unify a (eq_refl true);
    try unify b (eq_refl true);
    try unify c (eq_refl true);
    try unify d (eq_refl true);
    try unify e (eq_refl true);
    try unify f (eq_refl true);
    try unify g (eq_refl true);
    constructor        
    end.
  Show Existentials.
  
  Goal (exists x : (FacadeWrapper W W), Shelve x).
    eexists.
    match goal with
      |- @Shelve ?X ?x =>
      let x' := constr:(_ : X) in unify x' x
    end.
    
    simpl in e.
  Print is_syntax_ok.
  cbv [CompileDFacade.compile_op] in e.
  simpl in e.
  unfold FModule.is_syntax_ok in e.
  
  
  compute in e.
  compute in e.
simpl in e.
let a' := eval unfold e in e in
    unify a' (eq_refl true).
  reflexivity.
  Fo
  intros.
  
  instantiate (1 := Skip).
  
  eapply Fiat.Common.IterateBoundedIndex.Iterate_Ensemble_BoundedIndex.
  intros.
  eexists.
  split.
  Focus 2.

  Definition CompiledModule
  : BuildFacadeModule FixedAV adt.
Proof.

Definition BuildFacadeModule av
           {n n'}
           {Rep}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (consDefs : ilist (B := @consDef Rep) consSigs)
           (methDefs : ilist (B := @methDef Rep) methSigs)
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
  := {module : DFModule av |
            forall



     .
Proof.
  refine {| Imports := Imports;
            Funs := _;
            import_module_names_good := _ |}.
  refine (Vector.fold_left (fun acc el => (StringMap.add _ _ acc)) (StringMap.empty _) methSigs).
  exact (methID el).
  assert OperationalSpec.
  Print OperationalSpec.

  refine {| Core := {| ;
           compiled_syntax_ok := _ |}. FModule.is_syntax_ok
                                            (CompileDFacade.compile_op Core) = true }
  econstructor.

  Print methSig.
  refine StringMap.




Parameter TSearchTerm : Type.
Parameter TAcc : Type.
Definition av := (list W + TSearchTerm + TAcc)%type.

Definition MyEnvListsB : Env (list W + TSearchTerm + TAcc) :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("listW", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("listW", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("listW", "pop!") ->> (Axiomatic (List_pop W))
    ### ("listW", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("listW", "empty?") ->> (Axiomatic (List_empty W))
    ### ("search", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor TSearchTerm))
    ### ("acc", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor TAcc)).

(* Ltac compile_destructor := *)
(*   match_ProgOk *)
(*     ltac:(fun prog pre post ext env => *)
(*             let vtmp := gensym "tmp" in *)
(*             match constr:(pre, post) with *)
(*             | (Cons _ _ (fun _ => ?tenv), ?tenv) => *)
(*               apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) *)
(*             | (Cons _ ?v (fun _ => ?tenv), ?tenv') => *)
(*               match tenv' with *)
(*               | context[v] => fail 1 *)
(*               | _ => eapply CompileSeq; [ apply (CompileCallFacadeImplementationOfDestructor (vtmp := DummyArgument vtmp)) | ] *)
(*               end *)
(*             end. *)

Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation Fiat.QueryStructure.Automation.Common Fiat.QueryStructure.Specification.Representation.Schema.
Require Import Coq.Vectors.Fin.

(* Notation "'BIND' !! A !! B !! C" := (@Bind A B C) (at level 1). *)
(* Notation "x { A } <- y ; z" := (Bind y (fun x: A => z)) (at level 1). *)

Definition FinToWord {N: nat} (n: Fin.t N) :=
  Word.natToWord 32 (proj1_sig (Fin.to_nat n)).

Definition FitsInW {N: nat} (n: Fin.t N) :=
  Word.wordToNat (FinToWord n) = proj1_sig (Fin.to_nat n).

Set Printing All.
Set Printing Depth 1000.
Print PartialSchedulerImpl.
Unset Printing All.

Definition Type1 := IndexedQueryStructure
                     (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                     (@icons3 _
                              (fun sch : RawHeading => SearchUpdateTerms sch) heading 0
                              (VectorDef.nil RawHeading) SearchUpdateTerm
                              (@inil3 _ (fun sch : RawHeading => SearchUpdateTerms sch))).

Definition Type2 := (Type1 * list (Domain heading (@FS 2 (@FS 1 (@F1 0)))))%type.

Definition Method2 :=
          (fun
           (r_n : IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
           (d
            d0 : Word.word
                   (S
                      (S
                         (S
                            (S
                               (S
                                  (S
                                     (S
                                        (S
                                           (S
                                              (S
                                                 (S
                                                  (S
                                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))) =>
         @Bind
           (prod
              (@IndexedEnsembles.IndexedEnsemble
                 (@RawTuple
                    (@Build_RawHeading (S (S (S O)))
                       (Vector.cons Type W (S (S O))
                          (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
              (list
                 (@RawTuple
                    (@Build_RawHeading (S (S (S O)))
                       (Vector.cons Type W (S (S O))
                          (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))))
           (prod
              (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                    (VectorDef.nil RawHeading) SearchUpdateTerm
                    (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
           (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
              (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                 (VectorDef.nil RawHeading) SearchUpdateTerm
                 (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))
              (@F1 O)
              (@BagFind
                 (@Build_RawHeading (S (S (S O)))
                    (Vector.cons Type W (S (S O))
                       (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                 (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
                    (S O)
                    (Vector.cons RawSchema
                       (Build_RawSchema
                          (@Build_RawHeading (S (S (S O)))
                             (Vector.cons Type W (S (S O))
                                (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                          (@None
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                              Prop))
                          (@Some
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                              @RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                              Prop)
                             (@UniqueAttribute
                                (@BuildHeading (S (S (S O)))
                                   (Vector.cons Attribute
                                      (Build_Attribute
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString))) W)
                                      (S (S O))
                                      (Vector.cons Attribute
                                         (Build_Attribute
                                            (String
                                               (Ascii.Ascii true true false false true true true false)
                                               (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                            ProcessScheduler.State)
                                         (S O)
                                         (Vector.cons Attribute
                                            (Build_Attribute
                                               (String
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) W)
                                            O (Vector.nil Attribute)))))
                                (@BoundedLookup.Build_BoundedIndex string
                                   (S (S (S O)))
                                   (Vector.cons string
                                      (String (Ascii.Ascii false false false false true true true false)
                                         (String (Ascii.Ascii true false false true false true true false)
                                            (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                      (S (S O))
                                      (Vector.cons string
                                         (String (Ascii.Ascii true true false false true true true false)
                                            (String
                                               (Ascii.Ascii false false true false true true true false)
                                               (String
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                         (S O)
                                         (Vector.cons string
                                            (String
                                               (Ascii.Ascii true true false false false true true false)
                                               (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                            (Vector.nil string))))
                                   (String (Ascii.Ascii false false false false true true true false)
                                      (String (Ascii.Ascii true false false true false true true false)
                                         (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                   (@BoundedLookup.Build_IndexBound string
                                      (S (S (S O)))
                                      (String (Ascii.Ascii false false false false true true true false)
                                         (String (Ascii.Ascii true false false true false true true false)
                                            (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                      (Vector.cons string
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                         (S (S O))
                                         (Vector.cons string
                                            (String
                                               (Ascii.Ascii true true false false true true true false)
                                               (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                            (S O)
                                            (Vector.cons string
                                               (String
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                               (Vector.nil string))))
                                      (@F1 (S (S O)))
                                      (@eq_refl string
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString)))))))))
                       O (Vector.nil RawSchema))
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))) r_n
              (@pair (option (Domain heading (@F1 (S (S O)))))
                 (prod (option (Domain heading (@FS (S (S O)) (@F1 (S O))))) (@RawTuple heading -> bool))
                 (@Some (Domain heading (@F1 (S (S O)))) d)
                 (@pair (option (Domain heading (@FS (S (S O)) (@F1 (S O)))))
                    (@RawTuple heading -> bool) (@None (Domain heading (@FS (S (S O)) (@F1 (S O)))))
                    (fun _ : @RawTuple heading => true))))
           (fun
              a : prod
                    (@IndexedEnsembles.IndexedEnsemble
                       (@RawTuple
                          (@Build_RawHeading (S (S (S O)))
                             (Vector.cons Type W (S (S O))
                                (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                    (list
                       (@RawTuple
                          (@Build_RawHeading (S (S (S O)))
                             (Vector.cons Type W (S (S O))
                                (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) =>
            @Common.If_Then_Else
              (Comp
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool))
              (EqNat.beq_nat
                 (@Datatypes.length (@RawTuple heading)
                    (@rev (@RawTuple heading)
                       (@snd
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a)))
                 O)
              (@Bind
                 (@IndexedEnsembles.IndexedEnsemble
                    (@RawTuple
                       (@Build_RawHeading (S (S (S O)))
                          (Vector.cons Type W (S (S O))
                             (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
                 (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))
                    (@F1 O)
                    (@BagInsert
                       (@Build_RawHeading (S (S (S O)))
                          (Vector.cons Type W (S (S O))
                             (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                       (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
                          (S O)
                          (Vector.cons RawSchema
                             (Build_RawSchema
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))
                                (@None
                                   (@RawTuple
                                      (@Build_RawHeading
                                         (S (S (S O)))
                                         (Vector.cons
                                            Type W
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                                    Prop))
                                (@Some
                                   (@RawTuple
                                      (@Build_RawHeading
                                         (S (S (S O)))
                                         (Vector.cons
                                            Type W
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                                    @RawTuple
                                      (@Build_RawHeading
                                         (S (S (S O)))
                                         (Vector.cons
                                            Type W
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))) ->
                                    Prop)
                                   (@UniqueAttribute
                                      (@BuildHeading
                                         (S (S (S O)))
                                         (Vector.cons Attribute
                                            (Build_Attribute
                                               (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                               W) (S (S O))
                                            (Vector.cons Attribute
                                               (Build_Attribute
                                                  (String
                                                  (Ascii.Ascii true true false false true true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                                  ProcessScheduler.State)
                                               (S O)
                                               (Vector.cons Attribute
                                                  (Build_Attribute
                                                  (String
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) W)
                                                  O
                                                  (Vector.nil Attribute)))))
                                      (@BoundedLookup.Build_BoundedIndex string
                                         (S (S (S O)))
                                         (Vector.cons string
                                            (String
                                               (Ascii.Ascii false false false false true true true false)
                                               (String
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                            (S (S O))
                                            (Vector.cons string
                                               (String
                                                  (Ascii.Ascii true true false false true true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                               (S O)
                                               (Vector.cons string
                                                  (String
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                                  (Vector.nil string))))
                                         (String (Ascii.Ascii false false false false true true true false)
                                            (String
                                               (Ascii.Ascii true false false true false true true false)
                                               (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                         (@BoundedLookup.Build_IndexBound string
                                            (S (S (S O)))
                                            (String
                                               (Ascii.Ascii false false false false true true true false)
                                               (String
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                            (Vector.cons string
                                               (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))
                                               (S (S O))
                                               (Vector.cons string
                                                  (String
                                                  (Ascii.Ascii true true false false true true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false true false true true true false)
                                                  (String (Ascii.Ascii true false true false false true true false) EmptyString)))))
                                                  (S O)
                                                  (Vector.cons string
                                                  (String
                                                  (Ascii.Ascii true true false false false true true false)
                                                  (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String (Ascii.Ascii true false true false true true true false) EmptyString))) O
                                                  (Vector.nil string))))
                                            (@F1 (S (S O)))
                                            (@eq_refl string
                                               (String
                                                  (Ascii.Ascii false false false false true true true false)
                                                  (String
                                                  (Ascii.Ascii true false false true false true true false)
                                                  (String (Ascii.Ascii false false true false false true true false) EmptyString)))))))))
                             O (Vector.nil RawSchema))
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))))
                    (Refinements.UpdateIndexedRelation
                       (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n
                       (@F1 O)
                       (@fst
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a))
                    (@ilist2.icons2 Type (@id Type) W
                       (S (S O)) (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))) d
                       (@ilist2.icons2 Type (@id Type) ProcessScheduler.State
                          (S O) (Vector.cons Type W O (Vector.nil Type)) SLEEPING
                          (@ilist2.icons2 Type (@id Type) W O (Vector.nil Type) d0 (@ilist2.inil2 Type (@id Type))))))
                 (fun
                    u : @IndexedEnsembles.IndexedEnsemble
                          (@RawTuple
                             (@Build_RawHeading (S (S (S O)))
                                (Vector.cons Type W
                                   (S (S O))
                                   (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))) =>
                  @Return
                    (prod
                       (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
                    (@pair
                       (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool
                       (Refinements.UpdateIndexedRelation
                          (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                          (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                             (VectorDef.nil RawHeading) SearchUpdateTerm
                             (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))
                          (Refinements.UpdateIndexedRelation
                             (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                             (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                                (VectorDef.nil RawHeading) SearchUpdateTerm
                                (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n
                             (@F1 O)
                             (@fst
                                (@IndexedEnsembles.IndexedEnsemble
                                   (@RawTuple
                                      (@Build_RawHeading
                                         (S (S (S O)))
                                         (Vector.cons
                                            Type W
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                                (list
                                   (@RawTuple
                                      (@Build_RawHeading
                                         (S (S (S O)))
                                         (Vector.cons
                                            Type W
                                            (S (S O))
                                            (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                                a)) (@F1 O) u) true)))
              (@Return
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool)
                 (@pair
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))) bool
                    (Refinements.UpdateIndexedRelation
                       (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n
                       (@F1 O)
                       (@fst
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a))
                    false)))).

Definition MethodOfInterest :=
  (fun
              (r_n : IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
              (d : ProcessScheduler.State) =>
            @Bind (prod (@IndexedEnsembles.IndexedEnsemble (@RawTuple heading)) (list (@RawTuple heading)))
              (prod
                 (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                    (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                       (VectorDef.nil RawHeading) SearchUpdateTerm
                       (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
                 (list
                    (Word.word
                       (S
                          (S
                             (S
                                (S
                                   (S
                                      (S
                                         (S
                                            (S
                                               (S
                                                  (S
                                                  (S
                                                  (S
                                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))))
              (@CallBagMethod (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                 (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                    (VectorDef.nil RawHeading) SearchUpdateTerm
                    (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch)))
                 (@F1 O)
                 (@BagFind heading
                    (@ilist3_hd RawSchema (fun ns : RawSchema => SearchUpdateTerms (rawSchemaHeading ns))
                       (S O)
                       (Vector.cons RawSchema
                          (Build_RawSchema heading
                             (@None (@RawTuple heading -> Prop))
                             (@Some (@RawTuple heading -> @RawTuple heading -> Prop) (@UniqueAttribute heading0 BStringId0))) O
                          (Vector.nil RawSchema))
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))) r_n
                 (@pair (option (Domain heading (@F1 (S (S O)))))
                    (prod (option ProcessScheduler.State) (@RawTuple heading -> bool))
                    (@None (Domain heading (@F1 (S (S O)))))
                    (@pair (option ProcessScheduler.State)
                       (@RawTuple heading -> bool)
                       (@Some ProcessScheduler.State d)
                       (fun _ : @RawTuple heading => true))))
              (fun a : prod (@IndexedEnsembles.IndexedEnsemble (@RawTuple heading)) (list (@RawTuple heading)) =>
               @Return
                 (prod
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
                    (list W))
                 (@pair
                    (IndexedQueryStructure (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))))
                    (list W)
                    (Refinements.UpdateIndexedRelation
                       (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                       (@icons3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch) heading O
                          (VectorDef.nil RawHeading) SearchUpdateTerm
                          (@inil3 RawHeading (fun sch : RawHeading => SearchUpdateTerms sch))) r_n
                       (@F1 O)
                       (@fst
                          (@IndexedEnsembles.IndexedEnsemble
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                          (list
                             (@RawTuple
                                (@Build_RawHeading
                                   (S (S (S O)))
                                   (Vector.cons Type W
                                      (S (S O))
                                      (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type))))))) a))
                    (@map (@RawTuple heading) (Domain heading (@F1 (S (S O))))
                       (fun x : @RawTuple heading => @GetAttributeRaw heading x (@F1 (S (S O))))
                       (@rev (@RawTuple heading)
                          (@snd
                             (@IndexedEnsembles.IndexedEnsemble
                                (@RawTuple
                                   (@Build_RawHeading
                                      (S (S (S O)))
                                      (Vector.cons
                                         Type W (S (S O))
                                         (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                             (list
                                (@RawTuple
                                   (@Build_RawHeading
                                      (S (S (S O)))
                                      (Vector.cons
                                         Type W (S (S O))
                                         (Vector.cons Type ProcessScheduler.State (S O) (Vector.cons Type W O (Vector.nil Type)))))))
                             a)))))).

Print Type1.

Definition av' := (list W + Type1 +
                  (@IndexedEnsembles.IndexedEnsemble
                     (@RawTuple heading)) +
                  (list (@RawTuple heading)) +
                  (@RawTuple heading))%type.

Definition MyEnvListsC : Env av' :=
  (GLabelMap.empty (FuncSpec _))
    ### ("std", "rand") ->> (Axiomatic FRandom)
    ### ("listW", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list W) nil))
    ### ("listW", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons))
    ### ("listW", "pop!") ->> (Axiomatic (List_pop W))
    ### ("listW", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list W)))
    ### ("listW", "empty?") ->> (Axiomatic (List_empty W))
    ### ("listT", "nil") ->> (Axiomatic (FacadeImplementationOfConstructor (list (@RawTuple heading)) nil))
    ### ("listT", "push!") ->> (Axiomatic (FacadeImplementationOfMutation_ADT _ (list (@RawTuple heading)) cons))
    ### ("listT", "pop!") ->> (Axiomatic (List_pop (@RawTuple heading)))
    ### ("listT", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (list (@RawTuple heading))))
    ### ("listT", "empty?") ->> (Axiomatic (List_empty (@RawTuple heading)))
    ### ("IndexedEnsemble", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor IndexedEnsembles.IndexedEnsemble))
    ### ("RawTuple", "delete!") ->> (Axiomatic (FacadeImplementationOfDestructor (@RawTuple heading))).

Check MethodOfInterest.

Ltac _compile_CallGetAttribute :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (Cons (NTSome ?vsrc) (ret ?src) ?tenv,
               Cons (NTSome ?vtarget) (ret (GetAttributeRaw ?src ?index)) ?tenv') =>
              let vindex := gensym "index" in
              eapply CompileSeq with ([[`vindex <-- FinToWord index as _]]
                                        :: [[`vsrc <-- src as src]]
                                        :: (tenv src));
                [ | match_ProgOk
                      ltac:(fun prog' _ _ _ _ =>
                              unify prog' (Call vtarget ("ext", "GetAttribute")
                                                (vsrc :: vindex :: nil))) ]
            end).

Ltac _compile_CallBagFind :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             match constr:(pre, post) with
             | (Cons (NTSome ?vdb) (ret ?db) (fun _ => Cons (NTSome ?vd) (ret ?d) ?tenv),
                Cons NTNone (CallBagMethod ?id BagFind ?db (Some ?d, _)) ?tenv') =>
               let vsnd := gensym "snd" in
               let vtmp := gensym "tmp" in
               match post with
               | Cons NTNone ?bf _ =>
                 eapply CompileSeq with ([[bf as retv]]
                                           :: [[`vdb <-- Refinements.UpdateIndexedRelation
                                                (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                (icons3 SearchUpdateTerm inil3) db F1 (fst retv)
                                                as _]]
                                           :: [[`vsnd <-- snd retv as s]]
                                           :: [[`vd <-- d as _]]
                                           :: (tenv d));
                   [ match_ProgOk
                       ltac:(fun prog' _ _ _ _ =>
                               unify prog' (Call (DummyArgument vtmp) ("ext", "BagFind")
                                                 (vsnd :: vdb :: vd :: nil))) (* FIXME *) | ]
               end
             end).

Ltac _compile_CallBagInsert :=
  match_ProgOk
     ltac:(fun prog pre post ext env =>
             match constr:(pre, post) with
             | (Cons ?vdb (ret ?db) (fun _ => ?tenv),
                Cons NTNone ?bm (fun a => Cons ?vdb' (@?rel a) (fun _ => ?tenv'))) =>
               unify vdb vdb';
                 match constr:(vdb, bm, rel) with
                 | (NTSome ?vdb', CallBagMethod ?id BagInsert ?db _, (fun a => ret (Refinements.UpdateIndexedRelation _ _ ?db' ?id a))) =>
                   unify db db';
                     let vtmp := gensym "tmp" in
                     apply CompileSeq with (Cons NTNone bm (fun a => Cons vdb (rel a) (fun _ => tenv))); (* FIXME hardcoded var names *)
                       [ match_ProgOk
                           ltac:(fun prog' _ _ _ _ =>
                                   unify prog' (Call (DummyArgument "tmp") ("ext", "BagInsert") (vdb' :: "d" :: "d0" :: nil))) | ]
                 end
             end).

Arguments wrap : simpl never.

Example random_test_with_adt :
  Facade program implementing ( x <- Random;
                                ret (if IL.weqb x 0 then
                                       (Word.natToWord 32 1) :: nil
                                     else
                                       x :: nil)) with MyEnvW.
Proof.
  Time compile_step.
  repeat (_compile_step || _compile_random).
Defined.

Eval compute in (extract_facade random_test_with_adt).

(* Require Import Utf8 FIXME remove *)

Definition Remembered {A} (a : A) := a.

Ltac set_remember v :=
  let vv := fresh in
  change v with (Remembered v);
    set (vv := Remembered v) in *.

Ltac set_values tenv :=
  lazymatch tenv with
  | context[Cons _ ?v ?tail] =>
    try match v with
        | ret ?v  => set_remember v
        | _ => set_remember v
        end;
      try set_values tail
  | _ => idtac
  end.

Ltac unset_values :=
  repeat match goal with
         | [ H := Remembered _ |- _ ] => unfold H in *; clear H
         | _ => unfold Remembered in *
         end.

Example other_test_with_adt''':
  sigT (fun prog => forall (searchTerm: TSearchTerm) (init: TAcc),
            {{ [[`"search" <-- searchTerm as _]] :: [[`"init" <-- init as _]] :: (@Nil av) }}
              prog
            {{ [[`"ret" <~~  ( seq <- {s: list W | True };
                             fold_left (fun acc elem =>
                                          acc <- acc;
                                          { x: W | Word.wlt (Word.wplus acc elem) x })
                                       seq (ret (Word.natToWord 32 0: W))) as _]] :: (@Nil av) }} ∪ {{ StringMap.empty (Value av) }} // MyEnvListsB).
Proof.
  econstructor; intros.

  (* repeat setoid_rewrite SameValues_Fiat_Bind_TelEq. *)

  _compile.

  eapply ProgOk_Transitivity_Name' with "seq".
  instantiate (1 := Skip).       (* FIXME alloc *)
  admit.
  compile_miniChomp.

  _compile.
  compile_loop.

  _compile.
  _compile.
  _compile.

  compile_do_extend_scalar_lifetime.
  _compile.

  compile_miniChomp.
  _compile.

  instantiate (1 := Skip); admit.
Defined.

Eval compute in (extract_facade other_test_with_adt''').

Example other_test_with_adtB'' `{FacadeWrapper av (list W)}:
    sigT (fun prog => forall seq: list W, {{ [[`"arg1" <-- seq as _ ]] :: Nil }}
                                    prog
                                  {{ [[`"ret" <-- (List.fold_left (@Word.wminus 32) seq 0) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvLists).
Proof.
  econstructor; intros.
  Print Ltac compile_loop.
  repeat (compile_step || compile_loop).
  let fop := translate_op Word.wminus in
  apply (CompileBinopOrTest_right_inPlace fop); compile_do_side_conditions.
Defined.

Example compile2 :
  sigT (fun prog => forall r_n d d0,
            {{ [[`"r_n" <-- r_n as _ ]] :: [[`"d" <-- d as _]] :: [[`"d0" <-- d0 as _]] :: Nil }}
              prog
            {{ [[Method2 r_n d d0 as retv]] :: [[`"r_n" <-- fst retv as _]] :: [[`"ret" <-- bool2w (snd retv) as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvListsC).
Proof.
  eexists; intros.
  unfold Method2, Common.If_Then_Else.

  Time repeat _compile_step.
  admit.
  instantiate (1 := Call "test" ("list", "Empty") ("snd" :: nil)) (* FIXME *); admit.
  admit.
Time Defined.

Eval compute in (extract_facade compile2).

Print Method2.

Example compile :
  sigT (fun prog => forall (r_n : Type1) (d : W),
            {{ [[`"r_n" <-- r_n as _ ]] :: [[`"d" <-- d as _]] :: Nil }}
              prog
            {{ [[MethodOfInterest r_n d as retv]] :: [[`"r_n" <-- fst retv as _]] :: [[`"ret" <-- snd retv as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvListsC).
Proof.
  eexists; intros.
  unfold MethodOfInterest.

<<<<<<< HEAD
  Ltac _compile_CallBagFind ::=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons (NTSome ?vdb) (ret ?db) (fun _ => Cons (NTSome ?vd) (ret ?d) ?tenv),
                 Cons NTNone (CallBagMethod ?id BagFind ?db _) ?tenv') =>
                let vsnd := gensym "snd" in
                let vtmp := gensym "tmp" in
                match post with
                | Cons NTNone ?bf _ =>
                  eapply CompileSeq with ([[bf as retv]]
                                            :: [[`vdb <-- Refinements.UpdateIndexedRelation
                                                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                 (icons3 SearchUpdateTerm inil3) db F1 (fst retv)
                                                 as _]]
                                            :: [[`vsnd <-- snd retv as s]]
                                            :: [[`vd <-- d as _]]
                                            :: (tenv d));
                    [ match_ProgOk
                        ltac:(fun prog' _ _ _ _ =>
                                unify prog' (Call (DummyArgument vtmp) ("ext", "BagFind")
                                                  (vsnd :: vdb :: vd :: nil))) (* FIXME *) | ]
                end
              end).

  Lemma map_rev_def :
    forall {A B} f seq,
      @map A B f (rev seq) = revmap f seq.
  Proof.
    intros; reflexivity.
  Qed.

  Time repeat (_compile_step || setoid_rewrite map_rev_def).
=======
  _compile_step.
  _compile_step.
  _compile_step.

  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.


  Time repeat (_compile_step || change (ilist2.ilist2_hd (ilist2.icons2 head ilist2.inil2)) with head).
>>>>>>> 17599019f1b5c3b557c578f4ed472b99479cf9a4
  admit.
  admit.
Defined.

Opaque DummyArgument.
Definition compiled := Eval compute in (extract_facade compile).

Example other_test_with_adt''''' :
    sigT (fun prog => forall seq seq', {{ [[`"arg1" <-- seq as _ ]] :: [[`"arg2" <-- seq' as _]] :: Nil }}
                                 prog
                               {{ [[`"arg1" <-- (rev_append seq seq') as _]] :: Nil }} ∪ {{ StringMap.empty _ }} // MyEnvW).
Proof.
  econstructor; intros.
Abort.



  Lemma ProgOk_Transitivity_Cons_B :
    forall {av} env ext t1 t1' t2 prog1 prog2 k (v: Comp (Value av)),
      {{ t1 }}                            prog1     {{ [[Some k <~~ v as kk]] :: t1' kk }}     ∪ {{ ext }} // env ->
      {{ [[Some k <~~ v as kk]] :: t1' kk }} prog2     {{ [[Some k <~~ v as kk]] :: t2 kk }} ∪ {{ ext }} // env ->
      {{ t1 }}                      Seq prog1 prog2 {{ [[Some k <~~ v as kk]] :: t2 kk }} ∪ {{ ext }} // env.
  Proof.
    eauto using CompileSeq.
  Qed.

  (* This is a well-behaved version of ProgOk_Transitivity_Cons, but it is not
     very useful, as the side goal that it creates are in a form in which one
     would want to apply transitivity again. *)
  Lemma ProgOk_Transitivity_Cons_Drop :
    forall {av} env ext t1 t2 prog1 prog2 k (v: Comp (Value av)),
      {{ t1 }}                     prog1      {{ [[Some k <~~ v as _]]::(DropName k t1) }}     ∪ {{ ext }} // env ->
      {{ [[Some k <~~ v as _]]::(DropName k t1) }}      prog2      {{ [[Some k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env ->
      {{ t1 }}                Seq prog1 prog2 {{ [[Some k <~~ v as kk]]::t2 kk }} ∪ {{ ext }} // env.
  Proof.
    SameValues_Facade_t.
  Qed.
