Require Import Fiat.Examples.QueryStructure.ProcessScheduler.
Require Import Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.
Require Import Fiat.Common.i3list.
Require Import Fiat.ADT.Core.

Require Import
        CertifiedExtraction.Core
        CertifiedExtraction.FacadeUtils
        CertifiedExtraction.StringMapUtils
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.Extraction.

Definition CodWrapperT av (Cod : option Type) :=
  match Cod with
  | None => unit
  | Some CodT => FacadeWrapper (Value av) CodT
  end.

Definition GoodWrapper av A :=
  { H: FacadeWrapper (Value av) A & forall a1 a2: A, is_same_type (wrap a1) (wrap a2) }.

Fixpoint DomWrapperT av (Dom : list Type) : Type :=
  match Dom with
  | nil => unit
  | cons DomT Dom' => prod (GoodWrapper av DomT)
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
                         {{ [[`"ret" <-- Word.natToWord 32 0 as _]]
                              :: [[meth as database]] :: (f database) }} ∪ {{ StringMap.empty _ }} // env

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
      forall d, let _ := projT1 (fst dWrap) in LiftMethod' env Dom' f cWrap (snd dWrap) prog ([[ (NTSome (nthArgName (List.length Dom'))) <-- d as _]] :: tele) (meth d)
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
      prod (FacadeWrapper av (C a (prim_fst il)))
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

Arguments nthRepName _ / .
Arguments nthArgName _ / .
Arguments BuildArgNames !n !m / .

Fixpoint AxiomatizeMethodPre' (av : Type) (env : Env av) {Dom}
         {struct Dom}
  : DomWrapperT av Dom
    -> list (Value av)
    -> list (Value av) -> Prop
  :=
  match Dom return
        DomWrapperT av Dom
        -> list (Value av)
        -> list (Value av)
        -> Prop with
  | nil => fun dWrap args' args =>
             args = args'
  | cons DomT Dom' =>
    fun dWrap args' args =>
      let wrap' := projT1 (fst dWrap) in
      exists x : DomT, AxiomatizeMethodPre' env Dom' (snd dWrap) (wrap x :: args') args
  end.

Definition AxiomatizeMethodPre (av : Type) (env : Env av) {Rep} {Dom}
         (f : Rep -> list (Value av))
  : DomWrapperT av Dom
    -> list (Value av) -> Prop
  :=
    fun dWrap args => exists r, (AxiomatizeMethodPre' env Dom dWrap (f r) args).

Fixpoint AxiomatizeMethodPost' {Dom} {Cod} {Rep}
         (av : Type)
         (env : Env av)
         {struct Dom}
  : CodWrapperT av Cod
    -> DomWrapperT av Dom
    -> (Rep -> list ((Value av) * option av))
    -> methodType' Rep Dom Cod
    -> list ((Value av) * option av) -> Value av -> Prop
  :=
  match Dom return
        CodWrapperT av Cod
        -> DomWrapperT av Dom
        -> (Rep -> list ((Value av) * option av))
        -> methodType' Rep Dom Cod
        -> list ((Value av) * option av)
        -> Value av -> Prop with
  | nil => match Cod return
                   CodWrapperT av Cod
                   -> DomWrapperT av nil
                   -> (Rep -> list ((Value av) * option av))
                   -> methodType' Rep nil Cod
                   -> list ((Value av) * option av)
                   -> Value av -> Prop with
           | None => fun cWrap dWrap args' meth args ret =>
                       exists r', computes_to meth r'
                                  /\ args = args' r'
                                  /\ ret = wrap (Word.natToWord 32 0)
           | Some CodT => fun cWrap dWrap args' meth args ret =>
                            exists r' v', computes_to meth (r', v')
                                  /\ args = args' r'
                                  /\ ret = wrap (FacadeWrapper := cWrap) v'
           end
  | cons DomT Dom' =>
    fun cWrap dWrap args' meth args ret =>
      let wrap' := projT1 (fst dWrap) in
      exists x : DomT, AxiomatizeMethodPost' env cWrap (snd dWrap) (fun r' => (wrap x, None) :: args' r') (meth x) args ret
  end.

Definition AxiomatizeMethodPost
           (av : Type)
           (env : Env av)
           {Dom} {Cod} {Rep}
           (f : Rep -> Rep -> list ((Value av) * option av))
           (cWrap : CodWrapperT av Cod)
           (dWrap : DomWrapperT av Dom)
           (meth : methodType Rep Dom Cod)
           (args : list ((Value av) * option av))
           (ret : Value av)
  : Prop :=
  exists r, AxiomatizeMethodPost' env cWrap dWrap (f r) (meth r) args ret.

Fixpoint DecomposePosti3list
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
      -> i3list C il
      -> list (((Value av) * option av)) :=
  match As return
        forall (il : ilist3 (B := B) As),
          RepWrapperT av C As il
          -> i3list C il
          -> i3list C il
          -> list (((Value av) * option av)) with
  | Vector.nil => fun as' rWrap r r' => nil
  | Vector.cons a n' As' => fun as' rWrap r r' =>
                              let fWrap' := fst rWrap in
                              cons (ADT (wrap (prim_fst r)), Some (wrap (prim_fst r')))
                                   (DecomposePosti3list As' (prim_snd as') (snd rWrap)
                                                        (prim_snd r) (prim_snd r'))
  end.

Definition DecomposeIndexedQueryStructurePost av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r r' : IndexedQueryStructure qs_schema Index)
  : list (((Value av) * option av)) :=
  DecomposePosti3list _ _ rWrap r r'.

Fixpoint DecomposePrei3list
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
      -> list (Value av) :=
  match As return
        forall (il : ilist3 (B := B) As),
          RepWrapperT av C As il
          -> i3list C il
          -> list (Value av) with
  | Vector.nil => fun as' rWrap r => nil
  | Vector.cons a n' As' => fun as' rWrap r =>
                              let fWrap' := fst rWrap in
                              cons (wrap (prim_fst r))
                                   (DecomposePrei3list As' (prim_snd as') (snd rWrap)
                                                        (prim_snd r))
  end.

Definition DecomposeIndexedQueryStructurePre av qs_schema Index
           (rWrap : @RepWrapperT av (QueryStructureSchema.numRawQSschemaSchemas qs_schema)
                                 Schema.RawSchema
                                 (fun ns : Schema.RawSchema =>
                                    SearchUpdateTerms (Schema.rawSchemaHeading ns))
                                 (fun (ns : Schema.RawSchema)
                                      (_ : SearchUpdateTerms (Schema.rawSchemaHeading ns)) =>
                                    @IndexedEnsembles.IndexedEnsemble
                                      (@RawTuple (Schema.rawSchemaHeading ns)))
                                 (QueryStructureSchema.qschemaSchemas qs_schema) Index)

           (r : IndexedQueryStructure qs_schema Index)
  : list (Value av) :=
  DecomposePrei3list _ _ rWrap r.

Arguments AxiomatizeMethodPost _ _ _ _ _ _ _ _ _ _ _ / .
Arguments DecomposePosti3list _ _ _ _ _ _ _ _ _ _ / .
Arguments DecomposeIndexedQueryStructurePost _ _ _ _ _ _ / .
Arguments AxiomatizeMethodPre _ _ _ _ _ _ _ / .
Arguments DecomposePrei3list _ _ _ _ _ _ _ _ _ / .
Arguments DecomposeIndexedQueryStructurePre _ _ _ _ _ / .

Eval simpl in
  (forall av env rWrap cWrap dWrap l ret,
      (AxiomatizeMethodPost (av := av) env (DecomposeIndexedQueryStructurePost _ _ _ rWrap) cWrap dWrap (Methods PartialSchedulerImpl (Fin.FS (Fin.F1)))) l ret).

Eval simpl in
    (forall av env rWrap cWrap dWrap l l' ret,
        let Dom' := _ in
        (AxiomatizeMethodPost (av := av) env (DecomposeIndexedQueryStructurePost _ _ _ rWrap) cWrap dWrap (Dom := Dom') (Methods PartialSchedulerImpl (Fin.FS (Fin.F1)))) l' ret
    /\ (AxiomatizeMethodPre (av := av) env (DecomposeIndexedQueryStructurePre _ _ _ rWrap) dWrap l)).

Require Import Bedrock.Platform.Facade.CompileUnit2.

Definition GenAxiomaticSpecs
           av
           (env : Env av)
           {Cod}
           {Dom}
           {Rep}
           (cWrap : CodWrapperT av Cod)
           (dWrap : DomWrapperT av Dom)
           (meth : methodType Rep Dom Cod)
           (f : Rep -> list (Value av))
           (f' : Rep -> Rep -> list ((Value av) * option av))
           (_ : forall x x0, is_same_types (f x0) (f x) = true)
  : AxiomaticSpec av.
Proof.
  refine {| PreCond := AxiomatizeMethodPre env f dWrap;
            PostCond := AxiomatizeMethodPost env f' cWrap dWrap meth |}.
  clear dependent meth.
  clear dependent f'.

  unfold type_conforming.
  unfold AxiomatizeMethodPre in *.
  
  generalize dependent f.
  generalize dependent Rep.
  induction Dom; simpl; repeat cleanup.
  
  - eauto.
  - simpl in H0.
    eapply IHDom.
    Focus 2.
    Ltac helper :=
      match goal with
      | [ H: AxiomatizeMethodPre' ?env ?dom ?wrp (wrap (FacadeWrapper := ?fw) ?x :: ?f ?y) ?ls |-
          exists r: ?Tr, AxiomatizeMethodPre' ?env ?dom ?wrp' (?f' r) ?ls ] =>
        let tx := type of x in
        let ty := type of y in
        (exists (x, y); unify wrp wrp'; unify f' (fun x => wrap (FacadeWrapper := fw) (fst x) :: f (snd x)); exact H)
      end.

    helper.
    repeat cleanup.
    unfold is_same_types in *.
    simpl.
    rewrite H.
    rewrite (projT2 (fst (dWrap))).
    reflexivity.

    helper.

    eauto.
Defined.

Fixpoint BuildFinUpTo (n : nat) {struct n} : list (Fin.t n) :=
  match n return list (Fin.t n) with
  | 0  => nil
  | S n' => cons (@Fin.F1 _) (map (@Fin.FS _) (BuildFinUpTo n'))
  end.

Definition GenExports
           av
           (env : Env av)
           (n n' : nat)
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (consWrapper : (forall midx, CodWrapperT av (methCod (Vector.nth methSigs midx))))
           (domWrapper : (forall midx,  DomWrapperT av (methDom (Vector.nth methSigs midx))))
           (f : Core.Rep adt -> list (Value av))
           (f' : Core.Rep adt -> Core.Rep adt -> list ((Value av) * option av))
           (H : forall x x0, is_same_types (f x0) (f x) = true)
  : StringMap.t (AxiomaticSpec av) :=
  List.fold_left (fun acc el => StringMap.add (methID (Vector.nth methSigs el))
                                              (GenAxiomaticSpecs env (consWrapper el) (domWrapper el) (Methods adt el) f f' H) acc) (BuildFinUpTo n') (StringMap.empty _).

Definition CompileUnit2Equiv
           av
           (env : Env av)
           {A}
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (f : A -> _)
           g
           ax_mod_name'
           op_mod_name'
           cWrap
           dWrap
           rWrap
           {exports}
           (compileUnit : CompileUnit exports)
  :=
    DFModuleEquiv env adt compileUnit.(module) cWrap dWrap (f rWrap) g
    /\ compileUnit.(ax_mod_name) = ax_mod_name'
    /\ compileUnit.(op_mod_name) = op_mod_name'.

Definition BuildCompileUnit2T
           av
           (env : Env av)
           {A}
           {n n'}
           {consSigs : Vector.t consSig n}
           {methSigs : Vector.t methSig n'}
           (adt : DecoratedADT (BuildADTSig consSigs methSigs))
           (f : A -> _)
           f'
           f''
           g
           ax_mod_name'
           op_mod_name'
           cWrap
           dWrap
           rWrap
           H
           (exports := GenExports env adt cWrap dWrap f' f'' H) :=
  {compileUnit : CompileUnit exports & (CompileUnit2Equiv env adt f g ax_mod_name' op_mod_name' cWrap dWrap rWrap compileUnit) }.

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

Class SideStuff av {n n' : nat}
       {consSigs : Vector.t consSig n} {methSigs : Vector.t methSig n'}
       (adt : DecoratedADT (BuildADTSig consSigs methSigs))
       (f' : Rep adt -> list (Value av)) :=
  { coDomainWrappers : forall midx : Fin.t n', CodWrapperT av (methCod (Vector.nth methSigs midx));
    domainWrappers : forall midx : Fin.t n', DomWrapperT av (methDom (Vector.nth methSigs midx));
    f'_well_behaved : forall x x0 : Rep adt, is_same_types (f' x0) (f' x) = true }.

Require Import Benchmarks.QueryStructureWrappers.

(* FIXME move *)
Lemma bool2w_inj:
  forall v v' : bool, bool2w v = bool2w v' -> v = v'.
Proof.
  destruct v, v'; (discriminate || reflexivity).
Qed.

Instance FacadeWrapper_bool {T : Type} : FacadeWrapper (Value T) bool.
Proof.
  refine {| wrap v := SCA _ (bool2w v) |};
  abstract (intros * H; inversion H; eauto using bool2w_inj).
Defined.

Definition UnpairSigT {A B} (P: A * B -> Type) :
  sigT (fun a => sigT (fun b => P (a, b))) -> sigT P :=
  fun s => let (a, s) := s in
        let (b, s) := s in
        existT P (a, b) s.

Definition UnitSigT (P: unit -> Type) :
  P tt -> sigT P :=
  fun s => existT P tt s.

Ltac _repeat_destruct :=
  match goal with
  | _ => apply UnitSigT
  | _ => apply UnpairSigT; try refine (existT _ (QS_WrapBag2 0 1) _)
  | [  |- forall idx: Fin.t _, _ ] => eapply IterateBoundedIndex.Lookup_Iterate_Dep_Type; simpl
  | [  |- context[@SideStuff] ] => econstructor
  | [  |- GoodWrapper _ _ ] => econstructor; reflexivity
  | [  |- prim_prod _ _ ] => split
  | [  |- prod _ _ ] => split
  | [  |- unit ] => constructor
  end.

Ltac repeat_destruct :=
  repeat _repeat_destruct.

Definition SchedulerWrappers : { rWrap : _ & @SideStuff QsADTs.ADTValue _ _ _ _ PartialSchedulerImpl
                                                        (DecomposeIndexedQueryStructurePre QsADTs.ADTValue _ _ rWrap) }.
Proof.
  simpl;
  repeat_destruct;
  typeclasses eauto.
Defined.

Arguments domainWrappers {_ _ _ _ _ _ _} _ _.
Arguments coDomainWrappers {_ _ _ _ _ _ _} _ _.
Arguments f'_well_behaved {_ _ _ _ _ _ _} _ _ _.

Require Import Bedrock.Platform.Facade.examples.QsADTs.
Require Import Bedrock.Platform.Facade.examples.TuplesF.

Ltac fiat_t :=
  repeat (eapply BindComputes || apply PickComputes || apply ReturnComputes || simpl).

Lemma CompileTuples2_findFirst :
  forall vret vtable vkey fpointer (env: Env ADTValue) ext tenv N k1 k2
    (table: FiatBag (S N)) (key: W)
    (table':= ( results <- {l : list RawTuple | IndexedEnsembles.EnsembleIndexedListEquivalence (table) l};
               ret (table,
                    List.filter (fun tup : FiatTuple (S N) => ((if Word.weq (ilist2.ilist2_hd tup) key then true else false) && true)%bool) results)
               : Comp (_ * list (FiatTuple (S N))))),
    GLabelMap.MapsTo fpointer (Axiomatic Tuples2_findFirst) env ->
    Lifted_MapsTo ext tenv vtable (wrap (FacadeWrapper := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) table) ->
    Lifted_MapsTo ext tenv vkey (wrap key) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    NoDuplicates [[[vret; vtable; vkey]]] ->
    vret ∉ ext ->
    vtable ∉ ext ->
    functional (IndexedEnsemble_TupleToListW table) ->
    {{ tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ (@NTSome ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]] 
           :: [[ (@NTSome ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
           :: DropName vret (DropName vtable tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
  fiat_t.
  wipe.

  instantiate (1 := nil); admit.
  fiat_t.
  fiat_t.
  admit.

  repeat apply DropName_remove; eauto 1.
Qed.

Lemma Lifted_MapsTo_Ext:
  forall `{FacadeWrapper (Value av) A} ext k v tenv,
    StringMap.MapsTo k v ext ->
    @Lifted_MapsTo av ext tenv k (wrap v).
Proof.
  unfold Lifted_MapsTo, LiftPropertyToTelescope.
  SameValues_Facade_t.
Qed.

Lemma Lifted_MapsTo_SCA_not_mapsto_adt:
  forall {av} ext k (v: W) tenv,
    StringMap.MapsTo k (SCA _ v) ext ->
    @Lifted_not_mapsto_adt av ext tenv k.
Proof.
  unfold Lifted_not_mapsto_adt, LiftPropertyToTelescope; intros.
  SameValues_Facade_t.
Qed.

Ltac Lifted_t ::=
     repeat match goal with
            | _ => congruence
            | [  |- _ ∉ _ ] => decide_not_in
            | [  |- StringMap.MapsTo _ _ _ ] => decide_mapsto
            | [  |- NotInTelescope _ _ ] => decide_NotInTelescope
            | [  |- TelEq _ _ _ ] => reflexivity
            | [  |- Lifted_MapsTo _ (Cons (NTSome ?k) _ _) ?k' _ ] => apply Lifted_MapsTo_eq
            | [  |- Lifted_MapsTo _ (Cons (NTSome ?k) _ _) ?k' _ ] => apply Lifted_MapsTo_neq; [ congruence | ]
            | [ H: StringMap.MapsTo ?k _ ?ext |- Lifted_MapsTo ?ext _ ?k _ ] => apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate
            | [  |- Lifted_not_mapsto_adt _ (Cons (NTSome ?k) _ _) ?k' ] => apply Lifted_not_mapsto_adt_eq
            | [  |- Lifted_not_mapsto_adt _ (Cons (NTSome ?k) _ _) ?k' ] => apply Lifted_not_mapsto_adt_neq; [ congruence | ]
            | [  |- Lifted_not_mapsto_adt _ _ _ ] => apply Lifted_not_In_Telescope_not_in_Ext_not_mapsto_adt; [ decide_not_in | decide_NotInTelescope ]
            | [ H: StringMap.MapsTo ?k _ ?ext |- Lifted_not_mapsto_adt ?ext _ ?k ] => eapply Lifted_MapsTo_SCA_not_mapsto_adt; decide_mapsto_maybe_instantiate
            | [  |- Lifted_is_true _ _ _ ] => apply Lifted_is_true_eq_MapsTo (* Coercions make precise matching hard *)
            end.

Ltac _PreconditionSet_t_in H ::=
     cbv beta iota zeta delta [PreconditionSet PreconditionSet_helper NoDuplicates NoDuplicates_helper] in H; destruct_ands H.

Lemma CompileTuples2_findFirst_spec :
  forall vret vtable vkey fpointer (env: Env ADTValue) ext tenv N k1 k2
    (table: FiatBag (S N)) (key: W)
    (table':= ( results <- {l : list RawTuple | IndexedEnsembles.EnsembleIndexedListEquivalence (table) l};
               ret (table,
                    List.filter (fun tup : FiatTuple (S N) => ((if Word.weq (ilist2.ilist2_hd tup) key then true else false) && true)%bool) results)
               : Comp (_ * list (FiatTuple (S N))))),
    GLabelMap.MapsTo fpointer (Axiomatic Tuples2_findFirst) env ->
    StringMap.MapsTo vkey (wrap key) ext ->
    PreconditionSet tenv ext [[[vret; vtable]]] ->
    vret <> vkey ->
    vtable <> vkey ->
    functional (IndexedEnsemble_TupleToListW table) ->
    {{ [[ (@NTSome ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- table as _]] :: tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ (@NTSome ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]] 
           :: [[ (@NTSome ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
           :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply generalized CompileTuples2_findFirst; repeat (compile_do_side_conditions || Lifted_t || PreconditionSet_t).
  setoid_rewrite (DropName_NotInTelescope _ _ H11).
  rewrite DropName_Cons_None.
  setoid_rewrite (DropName_NotInTelescope _ _ H9).
  decide_TelEq_instantiate.
Qed.

Lemma CompileWordList_empty_helper:
  forall (N : nat) (lst : list (FiatTuple N)) (x1 : W),
    Programming.propToWord (map TupleToListW lst = nil) x1 -> ret (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) ↝ x1.
Proof.
  unfold Programming.propToWord, IF_then_else in *.
  destruct lst; simpl in *; destruct 1; repeat cleanup; try discriminate; fiat_t.
Qed.

Hint Resolve CompileWordList_empty_helper : call_helpers_db.

Lemma CompileTupleList_Empty:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key) (lst : list _),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) lst) ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fpointer (Axiomatic TupleList_empty) env ->
    {{ tenv }}
      Call vtest fpointer (vlst :: nil)
      {{ [[`vtest <-- (bool2w (EqNat.beq_nat (Datatypes.length lst) 0)) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  rewrite add_remove_comm by congruence.
  rewrite <- add_redundant_cancel by assumption.
  facade_eauto.
Qed.

Lemma CompileTupleList_Empty_spec:
  forall (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key) (lst : list _),
    vlst <> vtest ->
    vtest ∉ ext ->
    NotInTelescope vtest tenv ->
    StringMap.MapsTo vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) lst) ext ->
    GLabelMap.MapsTo fpointer (Axiomatic TupleList_empty) env ->
    {{ tenv }}
      Call vtest fpointer (vlst :: nil)
      {{ [[`vtest <-- (bool2w (EqNat.beq_nat (Datatypes.length (rev lst)) 0)) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite rev_length.
  apply generalized CompileTupleList_Empty; repeat (compile_do_side_conditions || Lifted_t).
Qed.

Ltac QS_t := match goal with
            | |- not_mapsto_adt _ _ = true => eapply not_In_Telescope_not_in_Ext_not_mapsto_adt; eassumption
            | _ => SameValues_Facade_t_step
            | _ => facade_cleanup_call
            | _ => LiftPropertyToTelescope_t
            | _ => PreconditionSet_t
            end.

Lemma CompileTuple_new_characterization:
  forall (vlen vtup : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue))
    (fnew : GLabelMap.key) (initial_state st' : State ADTValue) (w: W),
    StringMap.MapsTo vlen (wrap w) initial_state ->
    GLabelMap.MapsTo fnew (Axiomatic Tuple_new) env ->
    RunsTo env (Call vtup fnew [[[vlen]]]) initial_state st' ->
    exists x1, M.Equal st' ([vtup <-- ADT (Tuple x1)]::initial_state) /\ Datatypes.length x1 = Word.wordToNat w.
Proof.
  repeat QS_t.
  reflexivity.
Qed.

Lemma CompileTuple_set_characterization:
  forall (vlen vtmp vpos vtup v : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) N
    (fset : GLabelMap.key) (initial_state st' : State ADTValue) (tup: FiatTuple N) (val pos: W),
    StringMap.MapsTo v (wrap val) initial_state ->
    StringMap.MapsTo vpos (wrap pos) initial_state ->
    StringMap.MapsTo vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) initial_state ->
    GLabelMap.MapsTo fset (Axiomatic Tuple_set) env ->
    RunsTo env (Call vtmp fset [[[vtup;vpos;v]]]) initial_state st' ->
    M.Equal st' ([vtmp <-- SCAZero]::[vtup <-- ADT (Tuple (Array.upd (TupleToListW tup) pos val))]::initial_state).
Proof.
  repeat QS_t.
  reflexivity.
Qed.

Lemma CompileTuple_new :
  forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext
    (val1 val2 val3: W)
    (fnew fset : GLabelMap.key),
    NoDuplicates [[[v1;v2;v3;o1;o2;o3;vtup;vlen;vtmp]]] ->
    (* Lifted_MapsTo ext tenv v1 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) val1) -> *)
    (* Lifted_MapsTo ext tenv v2 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) val2) -> *)
    (* Lifted_MapsTo ext tenv v3 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) val3) -> *)
    (* Lifted_MapsTo ext tenv o1 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 0)) -> *)
    (* Lifted_MapsTo ext tenv o2 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 1)) -> *)
    (* Lifted_MapsTo ext tenv o3 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 2)) -> *)
    (* Lifted_MapsTo ext tenv vlen (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 3)) -> *)
    (* Lifted_not_mapsto_adt ext tenv vtup -> *)
    (* Lifted_not_mapsto_adt ext tenv vtmp -> *)
    StringMap.MapsTo v1 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) val1) ext ->
    StringMap.MapsTo v2 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) val2) ext ->
    StringMap.MapsTo v3 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) val3) ext ->
    StringMap.MapsTo o1 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 0)) ext ->
    StringMap.MapsTo o2 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 1)) ext ->
    StringMap.MapsTo o3 (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 2)) ext ->
    StringMap.MapsTo vlen (wrap (FacadeWrapper := @FacadeWrapper_SCA ADTValue) (Word.natToWord 32 3)) ext ->
    NotInTelescope vtup tenv ->
    NotInTelescope vtmp tenv ->
    vtup ∉ ext ->
    vtmp ∉ ext ->
    GLabelMap.MapsTo fnew (Axiomatic Tuple_new) env ->
    GLabelMap.MapsTo fset (Axiomatic Tuple_set) env ->
    {{ tenv }}
      (Seq (Call vtup fnew (vlen :: nil))
           (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                     (Call vtmp fset (vtup :: o3 :: v3 :: nil)))))
      {{ [[(NTSome (H := WrapInstance (H := QS_WrapTuple)) vtup) <-- ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: [[(NTSome (H := @FacadeWrapper_SCA ADTValue) vtmp) <-- (Word.natToWord 32 0) as _]]
           :: (DropName vtup (DropName vtmp tenv)) }} ∪ {{ ext }} // env.
Proof.
  Remove Hints Bool.trans_eq_bool.
  unfold ProgOk.
  repeat match goal with
         | _ => cleanup
         | |- Safe _ (Seq _ _) _ => econstructor
         | _ => eapply SameValues_MapsTo_Ext_State; eassumption
         | _ => eapply StringMap.add_1; [ congruence | ]
         | _ => eapply StringMap.add_2; [ PreconditionSet_t; congruence | ]
         | [ H: RunsTo _ _ _ _ |- Safe _ _ _ ] => eapply CompileTuple_new_characterization in H; try eassumption
         | [ H: RunsTo _ _ _ _ |- Safe _ _ _ ] => eapply CompileTuple_set_characterization in H; try eassumption
         | [ H: StringMap.Equal ?m1 ?m2 |- StringMap.MapsTo _ _ ?m1 ] => rewrite H
         end.
Admitted.

Ltac side_conditions_fast :=
  repeat match goal with
         | _ => apply CompileDeallocSCA_discretely; [ .. | apply ProgOk_Chomp_Some; intros ]
         | |- NotInTelescope _ _ => simpl; repeat (split; intro; [ congruence | intros ]); eassumption
         | [  |- _ ∉ _ ] => decide_not_in
         end.

Lemma CompileTuple_new_spec :
  forall (v1 v2 v3 o1 o2 o3 vlen vtup vtmp : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext
    (val1 val2 val3: W) setup
    (fnew fset : GLabelMap.key),
    NoDuplicates [[[v1;v2;v3;o1;o2;o3;vtup;vlen;vtmp]]] ->
    vlen ∉ ext -> NotInTelescope vlen tenv ->
    o3 ∉ ext -> NotInTelescope o3 tenv ->
    o2 ∉ ext -> NotInTelescope o2 tenv ->
    o1 ∉ ext -> NotInTelescope o1 tenv ->
    v3 ∉ ext -> NotInTelescope v3 tenv ->
    v2 ∉ ext -> NotInTelescope v2 tenv ->
    v1 ∉ ext -> NotInTelescope v1 tenv ->
    NotInTelescope vtup tenv -> NotInTelescope vtmp tenv ->
    vtup ∉ ext ->
    vtmp ∉ ext ->
    GLabelMap.MapsTo (elt:=FuncSpec ADTValue) fnew (Axiomatic Tuple_new) env ->
    GLabelMap.MapsTo (elt:=FuncSpec ADTValue) fset (Axiomatic Tuple_set) env ->
    {{ tenv }}
      setup
      {{ [[`v1 <-- val1 as _]]
           :: [[`v2 <-- val2 as _]]
           :: [[`v3 <-- val3 as _]]
           :: [[`o1 <-- (Word.natToWord 32 0) as _]]
           :: [[`o2 <-- (Word.natToWord 32 1) as _]]
           :: [[`o3 <-- (Word.natToWord 32 2) as _]]
           :: [[`vlen <-- (Word.natToWord 32 3) as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ tenv }}
      (Seq setup
           (Seq (Call vtup fnew (vlen :: nil))
                (Seq (Call vtmp fset (vtup :: o1 :: v1 :: nil))
                     (Seq (Call vtmp fset (vtup :: o2 :: v2 :: nil))
                          (Call vtmp fset (vtup :: o3 :: v3 :: nil))))))
      {{ [[`vtup <-- ListWToTuple [[[val1;val2;val3]]] : FiatTuple 3 as _]]
           :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R.
  hoare. hoare. PreconditionSet_t.
  side_conditions_fast.
  computes_to_inv; subst.
  apply generalized CompileTuple_new;
    repeat match goal with
           | _ => congruence
           | _ => decide_not_in
           | _ => decide_mapsto_maybe_instantiate
           | _ => compile_do_side_conditions
           end.
  apply ProgOk_Chomp_Some; try side_conditions_fast. intros.
  PreconditionSet_t; side_conditions_fast; apply CompileSkip.
Qed.

Ltac explode n :=
  match n with
  | 0 => idtac
  | S ?n =>
    compile_do_use_transitivity_to_handle_head_separately;
      [ | apply ProgOk_Chomp_Some; [ | intros; explode n ] ]
  end.

Lemma CompileTuple_Delete:
  forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N),
    vtup <> vtmp ->
    vtmp ∉ ext ->
    vtup ∉ ext ->
    (* vsize ∉ ext -> *)
    Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) ->
    Lifted_MapsTo ext tenv vsize (wrap (Word.natToWord 32 N)) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic Tuple_delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vtup :: vsize :: nil)
    {{ [[`vtmp <-- (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vtup tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuple_Delete_spec:
  forall (vtmp vtup vsize : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N),
    vtup <> vtmp ->
    vtup <> vsize ->
    vsize <> vtmp ->
    vtmp ∉ ext ->
    vtup ∉ ext ->
    vsize ∉ ext ->
    NotInTelescope vtmp tenv ->
    NotInTelescope vtup tenv ->
    NotInTelescope vsize tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic Tuple_delete) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTuple (N := N)))) vtup) <-- tup as _]] :: tenv }}
      (Seq (Assign vsize (Const (Word.natToWord 32 N))) (Call vtmp fpointer (vtup :: vsize :: nil)))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  hoare. apply CompileConstant; try compile_do_side_conditions.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros; computes_to_inv; subst; simpl.
  apply generalized CompileTuple_Delete; try (compile_do_side_conditions ||  Lifted_t).
  apply Lifted_MapsTo_Ext; compile_do_side_conditions.
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.
  Lemma CompileTuples2_insert :
    forall vret vtable vtuple fpointer (env: Env ADTValue) ext tenv N k1 k2 idx
      (table: FiatBag N) (tuple: FiatTuple N),
      GLabelMap.MapsTo fpointer (Axiomatic Tuples2_insert) env ->
      Lifted_MapsTo ext tenv vtable (wrap (FacadeWrapper := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) table) ->
      Lifted_MapsTo ext tenv vtuple (wrap tuple) ->
      Lifted_not_mapsto_adt ext tenv vret ->
      NoDuplicates [[[vret; vtable; vtuple]]] ->
      vret ∉ ext ->
      vtable ∉ ext ->
      vtuple ∉ ext ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      minFreshIndex (IndexedEnsemble_TupleToListW table) idx ->
      {{ tenv }}
        Call vret fpointer (vtable :: vtuple :: nil)
      {{ [[ ( freshIdx <- {freshIdx : nat | IndexedEnsembles.UnConstrFreshIdx table freshIdx};
              ret (Ensembles.Add IndexedEnsembles.IndexedElement table
                                 {| IndexedEnsembles.elementIndex := freshIdx;
                                    IndexedEnsembles.indexedElement := tuple |})) as rep ]]
           :: [[`vret <-- (Word.natToWord 32 0) as _ ]]
           :: [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vtable) <-- rep as _ ]]
           :: DropName vtable (DropName vret (DropName vtuple tenv)) }} ∪ {{ ext }} // env.
  Proof.
    repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
    facade_eauto.
    fiat_t.
    instantiate (1 := x10); admit.
    facade_eauto.
    facade_eauto.

    repeat f_equal.
    apply Ensembles.Extensionality_Ensembles. admit.
    repeat apply DropName_remove; eauto 1.
  Qed.

  Lemma CompileTuples2_insert_spec :
    forall vtmp vtable vtuple fpointer (env: Env ADTValue) ext tenv N k1 k2 idx
      (table: FiatBag N) (tuple: FiatTuple N),
      GLabelMap.MapsTo fpointer (Axiomatic Tuples2_insert) env ->
      NoDuplicates [[[vtmp; vtable; vtuple]]] ->
      vtmp ∉ ext ->
      vtable ∉ ext ->
      vtuple ∉ ext ->
      NotInTelescope vtmp tenv ->
      NotInTelescope vtuple tenv ->
      NotInTelescope vtable tenv ->
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      minFreshIndex (IndexedEnsemble_TupleToListW table) idx ->
      {{ [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vtable) <-- table as _ ]]
           :: [[ (NTSome (H := @WrapInstance _ _ QS_WrapTuple) vtuple) <-- tuple as _ ]]
           :: tenv }}
        Call vtmp fpointer (vtable :: vtuple :: nil)
      {{ [[ ( freshIdx <- {freshIdx : nat | IndexedEnsembles.UnConstrFreshIdx table freshIdx};
              ret (Ensembles.Add IndexedEnsembles.IndexedElement table
                                 {| IndexedEnsembles.elementIndex := freshIdx;
                                    IndexedEnsembles.indexedElement := tuple |})) as rep ]]
           :: [[ (NTSome (H := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) vtable) <-- rep as _ ]]
           :: tenv }} ∪ {{ ext }} // env.
  Proof.
    intros. PreconditionSet_t.
    apply ProgOk_Remove_Skip_R; hoare.
    apply generalized CompileTuples2_insert; repeat (compile_do_side_conditions || Lifted_t).
    eauto.
    apply ProgOk_Chomp_None; intros.
    repeat match goal with
           | [ H: NotInTelescope ?k ?tenv |- context[DropName ?k ?tenv] ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
           | _ => setoid_rewrite Propagate_anonymous_ret
           | _ => fold @DropName
           end.
    apply CompileDeallocSCA_discretely; repeat (compile_do_side_conditions || decide_NotInTelescope).
    apply CompileSkip.
  Qed.


Lemma CompileWordList_pop:
  forall (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) tenv ext
    (fpop : GLabelMap.key) head (tail : list W),
    vlst <> vhead ->
    vhead ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) (head :: tail)) ->
    Lifted_not_mapsto_adt ext tenv vhead ->
    GLabelMap.MapsTo fpop (Axiomatic WordList_pop) env ->
    {{ tenv }}
      Call vhead fpop (vlst :: nil)
    {{ [[`vhead <-- head as _]]::[[`vlst <-- tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileWordList_new:
  forall (vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) tenv ext
    (fnew : GLabelMap.key),
    vlst ∉ ext ->
    NotInTelescope vlst tenv ->
    GLabelMap.MapsTo fnew (Axiomatic WordList_new) env ->
    {{ tenv }}
      Call vlst fnew (nil)
    {{ [[(NTSome vlst (H := WrapInstance (H := QS_WrapWordList)))  <-- @nil W as _]]::tenv }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
  change (ADT (WordList [])) with (wrap (FacadeWrapper := WrapInstance (H := @QS_WrapWordList)) []).
  facade_eauto.
Qed.

(* Lemma CompileTupleList_op: *)
(*   forall {N} (vhead vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) tenv ext *)
(*     (fpop : GLabelMap.key) head (tail : list (FiatTuple N)), *)
(*     vlst <> vhead -> *)
(*     vhead ∉ ext -> *)
(*     vlst ∉ ext -> *)
(*     Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := QS_WrapTupleList)) (head :: tail)) -> *)
(*     Lifted_not_mapsto_adt ext tenv vhead -> *)
(*     GLabelMap.MapsTo fpop (Axiomatic TupleList_pop) env -> *)
(*     {{ tenv }} *)
(*       Call vhead fpop (vlst :: nil) *)
(*     {{ [[`vhead <-- head as _]]::[[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <-- tail as _]]::(DropName vlst (DropName vhead tenv)) }} ∪ {{ ext }} // env. *)
(* Proof. *)
(*   repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t); *)
(*   facade_eauto. *)
(* Qed. *)

Lemma ListEmpty_helper :
  forall {A} (seq: list A),
    (EqNat.beq_nat (Datatypes.length seq) 0) = match seq with
                                               | nil => true
                                               | _ :: _ => false
                                               end.
Proof.
  destruct seq; reflexivity.
Qed.

Lemma TupleListEmpty_alt_helper :
  forall {N} x w,
    Programming.propToWord (map (TupleToListW (N := N)) x = nil) w ->
    ret (bool2w match x with
                | nil => true
                | _ :: _ => false
                end) ↝ w.
Proof.
  intros * h.
  apply CompileWordList_empty_helper in h.
  rewrite <- ListEmpty_helper.
  assumption.
Qed.

Hint Resolve TupleListEmpty_alt_helper : call_helpers_db.

Lemma CompileTupleList_Empty_alt:
  forall {N} (vtest vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext
    (fempty : GLabelMap.key) (lst : Comp (list (FiatTuple N))),
    vlst <> vtest ->
    vtest ∉ ext ->
    Lifted_not_mapsto_adt ext tenv vtest ->
    GLabelMap.MapsTo fempty (Axiomatic TupleList_empty) env ->
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <~~ lst as _]] :: tenv }}
      Call vtest fempty (vlst :: nil)
    {{ [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <~~ lst as ls]] :: [[`vtest <-- (bool2w match ls with
                                                | nil => true
                                                | _ :: _ => false
                                                end) as _]] :: (DropName vtest tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t);
  facade_eauto.
Qed.

Lemma CompileTupleList_Delete:
  forall (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    Lifted_MapsTo ext tenv vlst (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTupleList (N := N)))) nil) ->
    Lifted_not_mapsto_adt ext tenv vtmp ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic TupleList_delete) env ->
    {{ tenv }}
      Call vtmp fpointer (vlst :: nil)
    {{ [[`vtmp <-- (Word.natToWord 32 0) as _]] :: (DropName vtmp (DropName vlst tenv)) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  facade_eauto.
Qed.

Lemma CompileTupleList_Delete_spec:
  forall {N} (vtmp vlst : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext
    (fpointer : GLabelMap.key),
    vlst <> vtmp ->
    vtmp ∉ ext ->
    vlst ∉ ext ->
    NotInTelescope vtmp tenv ->
    NotInTelescope vlst tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic TupleList_delete) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTupleList (N := N)))) vlst) <-- nil as _]] :: tenv }}
      (Call vtmp fpointer (vlst :: nil))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R; hoare.
  apply generalized CompileTupleList_Delete; try (compile_do_side_conditions ||  Lifted_t).
  repeat match goal with
         | [ H: NotInTelescope _ _ |- _ ] => setoid_rewrite (DropName_NotInTelescope _ _ H)
         | _ => setoid_rewrite Propagate_anonymous_ret
         end.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Qed.

Lemma CompileTupleList_LoopBase :
  forall {N A} `{FacadeWrapper (Value ADTValue) A} (lst: list (FiatTuple N)) init vhead vtest vlst vret fpop fempty fdealloc facadeBody env (ext: StringMap.t (Value ADTValue)) tenv (f: Comp A -> FiatTuple N -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic TupleList_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic TupleList_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic TupleList_delete) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil)))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  unfold DummyArgument; loop_t.

  rewrite TelEq_swap by loop_t;
    eapply (CompileTupleList_Empty_alt (N := N)); loop_t.

  2:eapply (CompileTupleList_Delete_spec (N := N)); loop_t.

  loop_t.
  generalize dependent init;
  induction lst; loop_t.

  move_to_front vtest;
    apply CompileWhileFalse_Loop; loop_t.
  simpl.

  eapply CompileWhileTrue; [ loop_t.. | ].

  apply generalized @CompileTupleList_pop; loop_t.
  rewrite <- GLabelMapFacts.find_mapsto_iff; assumption.
  
  move_to_front vlst; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vtest; apply ProgOk_Chomp_Some; loop_t.
  move_to_front vret; loop_t.
  computes_to_inv; subst; defunctionalize_evar; eauto.

  rewrite TelEq_swap.
  apply ProgOk_Remove_Skip_L; hoare.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.
  apply CompileTupleList_Empty_alt; loop_t.

  loop_t.
Qed.

Lemma CompileTupleList_Loop :
  forall {N A} `{FacadeWrapper (Value ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeBody facadeConclude
    env (ext: StringMap.t (Value ADTValue)) tenv tenv' (f: Comp A -> FiatTuple N -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic (TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  apply @CompileTupleList_LoopBase; eassumption.
Qed.

Lemma CompileTupleList_LoopAlloc :
  forall {N A} `{FacadeWrapper (Value ADTValue) A} lst init vhead vtest vlst vret fpop fempty fdealloc facadeInit facadeBody facadeConclude
    env (ext: StringMap.t (Value ADTValue)) tenv tenv' (f: Comp A -> (FiatTuple N) -> Comp A),
    GLabelMap.MapsTo fpop (Axiomatic (TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <~~ init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (acc: Comp A) (s: list (FiatTuple N)),
        {{ [[`vret <~~ acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <~~ (f acc head) as _]] :: tenv }} ∪
        {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <~~ (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  hoare. hoare.
  apply @CompileTupleList_Loop; try eassumption.
Qed.

Lemma CompileWordList_push :
  forall vret vhd vlst fpointer (env: Env ADTValue) ext tenv
    h (t: list W),
    GLabelMap.MapsTo fpointer (Axiomatic WordList_push) env ->
    Lifted_MapsTo ext tenv vhd (wrap h) ->
    Lifted_MapsTo ext tenv vlst (wrap t) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    vret <> vlst ->
    vret <> vhd ->
    vhd <> vlst ->
    vhd ∉ ext ->
    vlst ∉ ext ->
    vret ∉ ext ->
    {{ tenv }}
      Call vret fpointer (vlst :: vhd :: nil)
      {{ [[ `vret <-- (Word.natToWord 32 0) as _ ]] :: [[ `vlst <-- h :: t as _ ]] :: DropName vlst (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t).
  facade_eauto.
  facade_eauto.
  repeat apply DropName_remove; congruence.
Qed.

Lemma CompileWordList_push_spec :
  forall vtmp vhd vlst fpointer (env: Env ADTValue) ext tenv
    h (t: list W),
    GLabelMap.MapsTo fpointer (Axiomatic WordList_push) env ->
    PreconditionSet tenv ext [[[vtmp;vhd;vlst]]] ->
    {{ [[ `vlst <-- t as _ ]] :: [[ `vhd <-- h as _ ]] :: tenv }}
      Call vtmp fpointer (vlst :: vhd :: nil)
    {{ [[ `vlst <-- h :: t as _ ]] :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R. hoare. PreconditionSet_t.
  apply generalized CompileWordList_push; repeat (compile_do_side_conditions || Lifted_t).
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions; apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  move_to_front vhd; apply CompileDeallocSCA_discretely; try compile_do_side_conditions; apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply CompileSkip.
Qed.

Lemma CompileMap_TuplesToWords :
  forall {N} (lst: list (FiatTuple N)) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value ADTValue)) tenv tenv' (f: FiatTuple N -> W),
    GLabelMap.MapsTo fpop (Axiomatic (TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (TupleList_empty)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (WordList_new)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (TupleList_delete)) env ->
    GLabelMap.MapsTo fcons (Axiomatic (WordList_push)) env ->
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list (FiatTuple N)) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap (FacadeWrapper := WrapInstance (H := QS_WrapWordList)) s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileTupleList_LoopAlloc; eauto.
  PreconditionSet_t; eauto.

  eapply CompileWordList_new; compile_do_side_conditions.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.

  apply CompileWordList_push_spec; try compile_do_side_conditions.
Qed.

Lemma CompileTupleList_Loop_ret :
  forall {N A} `{FacadeWrapper (Value ADTValue) A}
    lst init facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatTuple N) -> A),
    GLabelMap.MapsTo fpop (Axiomatic TupleList_pop) env ->
    GLabelMap.MapsTo fempty (Axiomatic TupleList_empty) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic TupleList_delete) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    (forall head acc (s: list (FiatTuple N)),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vret <-- init as _]] :: [[(NTSome (H := WrapInstance (H := QS_WrapTupleList)) vlst) <-- lst as _]] :: tenv }}
      (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude)
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite ret_fold_fold_ret.
  eapply CompileSeq.
  apply CompileTupleList_LoopBase; try compile_do_side_conditions.
  2: apply ProkOk_specialize_to_ret; intros * h; apply ret_fold_fold_ret in h; computes_to_inv; subst; eauto.
  intros; rewrite SameValues_Fiat_Bind_TelEq.
  apply miniChomp'; intros; eauto.
Qed.

Lemma CompileTupleList_LoopAlloc_ret :
  forall {N A} `{FacadeWrapper (Value ADTValue) A}
    lst init facadeInit facadeBody facadeConclude vhead vtest vlst vret env (ext: StringMap.t (Value ADTValue)) tenv tenv' fpop fempty fdealloc (f: A -> (FiatTuple N) -> A),
    GLabelMap.MapsTo fpop (Axiomatic (TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (TupleList_delete)) env ->
    PreconditionSet tenv ext [[[vhead; vtest; vlst; vret]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      facadeInit
    {{ [[`vret <-- init as _]] :: [[`vlst <-- lst as _]] :: tenv }} ∪ {{ ext }} // env ->
    (forall head acc (s: list (FiatTuple N)),
        {{ [[`vret <-- acc as _]] :: [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vret <-- (f acc head) as _]] :: tenv }} ∪ {{ [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv }}
      facadeConclude
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq facadeInit (Seq (Seq (Fold vhead vtest vlst fpop fempty facadeBody) (Call (DummyArgument vtest) fdealloc (vlst :: nil))) facadeConclude))
    {{ [[`vret <-- (fold_left f lst init) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  eauto using @CompileSeq, @CompileTupleList_Loop_ret.
Qed.

Lemma CompileTupleList_DeleteAny_spec:
  forall {N} (vtmp vtmp2 vsize vtest vlst vhead : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext
    (fpop fempty fdealloc ftdealloc : GLabelMap.key) (seq: (list (FiatTuple N))),
    PreconditionSet tenv ext [[[vtmp; vtmp2; vsize; vhead; vtest; vlst]]] ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpop (Axiomatic (TupleList_pop)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (TupleList_empty)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (TupleList_delete)) env ->
    GLabelMap.MapsTo ftdealloc (Axiomatic (Tuple_delete)) env ->
    {{ [[ (NTSome (H := WrapInstance (H := (QS_WrapTupleList (N := N)))) vlst) <-- seq as _]] :: tenv }}
      (Seq (Assign vtmp (Const (Word.natToWord 32 0)))
           (Seq (Seq (Fold vhead vtest vlst fpop fempty (Seq (Assign vsize (Const (Word.natToWord 32 N)))
                                                             (Call vtmp2 ftdealloc [[[vhead; vsize]]])))
                     (Call (DummyArgument vtest) fdealloc [[[vlst]]]))
                Skip))
    {{ tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply ProgOk_Remove_Skip_R.
  apply CompileSeq with ([[ ` vtmp <-- fold_left (fun acc x => acc) seq (Word.natToWord 32 0) as _]]::tenv).
  eapply (CompileTupleList_LoopAlloc_ret (vhead := vhead) (vtest := vtest)); try compile_do_side_conditions.
  apply CompileConstant; try compile_do_side_conditions.
  intros. apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply (CompileTuple_Delete_spec (vtmp := vtmp2) (vsize := vsize)); try compile_do_side_conditions.
  apply CompileSkip.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply CompileSkip.
Defined.


Lemma CompileTuples2_findSecond :
  forall vret vtable vkey fpointer (env: Env ADTValue) ext tenv N k1 k2
    (table: FiatBag (S (S N))) (key: W)
    (table':= ( results <- {l : list RawTuple | IndexedEnsembles.EnsembleIndexedListEquivalence (table) l};
               ret (table,
                    List.filter (fun tup : FiatTuple (S (S N)) => ((if Word.weq (ilist2.ith2 tup (Fin.FS Fin.F1)) key then true else false) && true)%bool) results)
               : Comp (_ * list (FiatTuple (S (S N)))))),
    GLabelMap.MapsTo fpointer (Axiomatic Tuples2_findSecond) env ->
    Lifted_MapsTo ext tenv vtable (wrap (FacadeWrapper := @WrapInstance _ _ (QS_WrapBag2 k1 k2)) table) ->
    Lifted_MapsTo ext tenv vkey (wrap key) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    NoDuplicates [[[vret; vtable; vkey]]] ->
    vret ∉ ext ->
    vtable ∉ ext ->
    functional (IndexedEnsemble_TupleToListW table) ->
    {{ tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
      {{ [[ table' as retv ]]
           :: [[ (@NTSome ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]] 
           :: [[ (@NTSome ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
           :: DropName vret (DropName vtable tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).
  fiat_t.

  instantiate (1 := nil); admit.
  fiat_t.
  fiat_t.
  simpl. admit.

  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuples2_findSecond_spec :
  forall vret vtable vkey fpointer (env: Env ADTValue) ext tenv N k1 k2
    (table: FiatBag (S (S N))) (key: W)
    (table':= ( results <- {l : list RawTuple | IndexedEnsembles.EnsembleIndexedListEquivalence (table) l};
               ret (table,
                    List.filter (fun tup : FiatTuple (S (S N)) => ((if Word.weq (ilist2.ith2 tup (Fin.FS Fin.F1)) key then true else false) && true)%bool) results)
               : Comp (_ * list (FiatTuple (S (S N)))))),
    GLabelMap.MapsTo fpointer (Axiomatic Tuples2_findSecond) env ->
    StringMap.MapsTo vkey (wrap key) ext ->
    PreconditionSet tenv ext [[[vret; vtable]]] ->
    vret <> vkey ->
    vtable <> vkey ->
    functional (IndexedEnsemble_TupleToListW table) ->
    {{ [[ (@NTSome ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- table as _]] :: tenv }}
      Call vret fpointer (vtable :: vkey :: nil)
    {{ [[ table' as retv ]]
         :: [[ (@NTSome ADTValue _ vtable (@WrapInstance _ _ (QS_WrapBag2 k1 k2))) <-- fst retv as _ ]] 
         :: [[ (@NTSome ADTValue _ vret (@WrapInstance _ _ QS_WrapTupleList)) <-- snd retv as _ ]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  apply generalized CompileTuples2_findSecond; repeat (compile_do_side_conditions || Lifted_t || PreconditionSet_t).
  setoid_rewrite (DropName_NotInTelescope _ _ H11).
  rewrite DropName_Cons_None.
  setoid_rewrite (DropName_NotInTelescope _ _ H9).
  decide_TelEq_instantiate.
Qed.

Transparent CallBagMethod.
Arguments CallBagMethod : simpl never.
Arguments wrap : simpl never.
Arguments ListWToTuple: simpl never.

Ltac start_compiling_adt :=
  intros;
  unfold_and_subst;
  match goal with | [ H: Fin.t _ |- _ ] => revert H end;
  repeat_destruct;
  unfold If_Then_Else, heading in *;
  change (Vector.cons Type W 2 (Vector.cons Type ProcessScheduler.State 1 (Vector.cons Type W 0 (Vector.nil Type)))) with (MakeVectorOfW 3);
  change ({| NumAttr := 3; AttrList := MakeVectorOfW 3 |}) with (MakeWordHeading 3).

Ltac _compile_CallBagFind :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (Cons (NTSome (H := ?h) ?vdb) (ret (prim_fst ?db)) (fun _ => ?tenv), Cons NTNone ?bf _) =>
              match bf with
              | CallBagMethod Fin.F1 BagFind ?db ?kwd =>
                let vsnd := gensym "snd" in
                let vtmp := gensym "tmp" in
                eapply CompileSeq with ([[bf as retv]]
                                          :: [[(NTSome (H := h) vdb) <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                                 (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                                                 (icons3 SearchUpdateTerm inil3) db Fin.F1 (fst retv)) as _]]
                                          :: [[`vsnd <-- snd retv as s]]
                                          :: tenv);
                  [ match kwd with
                    | (Some ?v, (None, fun _ => true)) => 
                      let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                      match vkwd with
                      | Some ?vkwd => apply (CompileTuples2_findFirst_spec (vkey := vkwd))
                      end
                    | (None, (Some ?v, fun _ => true)) => 
                      let vkwd := find_fast (wrap (WrappingType := Value QsADTs.ADTValue) v) ext in
                      match vkwd with
                      | Some ?vkwd => apply (CompileTuples2_findSecond_spec (vkey := vkwd))
                      end
                    end | ]
              end
            end).

Ltac _compile_length :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
            | (?pre, Cons ?k (ret (bool2w (EqNat.beq_nat (Datatypes.length (rev ?seq)) 0))) (fun _ => ?pre')) =>
              let vlst := find_fast (wrap (FacadeWrapper := WrapInstance (H := QS_WrapTupleList)) seq) ext in
              match vlst with 
              | Some ?vlst => eapply (CompileTupleList_Empty_spec (vlst := vlst))
              end
            end).


Ltac _compile_CallBagInsert := (* FIXME should do the insert in the second branch *)
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
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

Ltac _compile_allocTuple :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            match constr:(pre, post) with
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

Lemma progOKs
  : forall (env := GLabelMap.empty _)
      (rWrap := projT1 SchedulerWrappers)
      (Scheduler_SideStuff := projT2 SchedulerWrappers)
      midx, {prog : _ & LiftMethod env (DecomposeIndexedQueryStructure _ rWrap)
                                   (coDomainWrappers Scheduler_SideStuff midx)
                                   (domainWrappers Scheduler_SideStuff midx)
                                   prog (Methods PartialSchedulerImpl midx)}.
Proof.
  start_compiling_adt.

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

  Lemma CompileConstantBool:
    forall {av} name env (b: bool) ext (tenv: Telescope av),
      name ∉ ext ->
      NotInTelescope name tenv ->
      {{ tenv }}
        (Assign name (Const (bool2w b)))
      {{ [[`name <-- b as _]]::tenv }} ∪ {{ ext }} // env.
  Proof.
    SameValues_Facade_t.
    change (wrap (bool2w b)) with (wrap (FacadeWrapper := (@FacadeWrapper_bool av)) b).
    facade_eauto.
  Qed.

  repeat match goal with
         | _ => _compile_step
         | _ => _compile_CallBagFind
         | _ => _compile_CallBagInsert
         | _ => _compile_length
         | _ => _compile_allocTuple
         | _ => apply CompileConstantBool
         | _ => simpl
         end.

  instantiate (1 := ("ADT", "Tuples2_findFirst")); admit.
  admit.
  instantiate (1 := ("ADT", "TupleList_empty")); admit.
  instantiate (1 := ("ADT", "Tuple_new")); admit.
  instantiate (1 := ("ADT", "Tuple_set")); admit.
  instantiate (1 := ("ADT", "Tuples2_insert")); admit.
  reflexivity.
  instantiate (1 := 0); admit.
  reflexivity.
  instantiate (1 := ("ADT", "TupleList_pop")); admit.
  instantiate (1 := ("ADT", "TupleList_empty")); admit.
  instantiate (1 := ("ADT", "TupleList_delete")); admit.
  instantiate (1 := ("ADT", "Tuple_delete")); admit.
  reflexivity.
  instantiate (1 := ("ADT", "TupleList_pop")); admit.
  instantiate (1 := ("ADT", "TupleList_empty")); admit.
  instantiate (1 := ("ADT", "TupleList_delete")); admit.
  instantiate (1 := ("ADT", "Tuple_delete")); admit.

  
  (* instantiate (1 := ("ADT", "Tuple_new")); admit. *)
  (* instantiate (1 := ("ADT", "Tuple_delete")); admit. *)
  (* instantiate (1 := ("ADT", "Tuple_copy")); admit. *)
  (* instantiate (1 := ("ADT", "Tuple_get")); admit. *)
  (* instantiate (1 := ("ADT", "Tuple_set")); admit. *)

  (* instantiate (1 := ("ADT", "WordList_new")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_delete")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_pop")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_empty")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_push")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_copy")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_rev")); admit. *)
  (* instantiate (1 := ("ADT", "WordList_length")); admit. *)

  (* instantiate (1 := ("ADT", "TupleList_new")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_delete")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_copy")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_pop")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_empty")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_push")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_rev")); admit. *)
  (* instantiate (1 := ("ADT", "TupleList_length")); admit. *)

  (* instantiate (1 := ("ADT", "Tuples0_new")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples0_insert")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples0_enumerate")); admit. *)

  (* instantiate (1 := ("ADT", "Tuples1_new")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples1_insert")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples1_find")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples1_enumerate")); admit. *)

  (* instantiate (1 := ("ADT", "Tuples2_new")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples2_insert")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples2_findBoth")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples2_findFirst")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples2_findSecond")); admit. *)
  (* instantiate (1 := ("ADT", "Tuples2_enumerate")); admit. *)

  repeat match goal with
         | _ => _compile_step
         | _ => _compile_CallBagFind
         | _ => _compile_CallBagInsert
         | _ => _compile_length
         | _ => _compile_allocTuple
         | _ => apply CompileConstantBool
         | _ => simpl
         end.

  instantiate (1 := ("ADT", "Tuples2_findSecond")); admit.

  admit.

  Lemma map_rev_def :
    forall {A B} f seq,
      @map A B f (rev seq) = revmap f seq.
  Proof.
    intros; reflexivity.
  Qed.


  setoid_rewrite map_rev_def.

  match goal with
    
  end

  
let vhead := gensym "vhead" in
let vhead' := gensym "vhead'" in
let vtest := gensym "vtest" in
let vtmp := gensym "vtmp" in
apply (CompileMap_TuplesToWords (N := 3) (snd v0) (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := vtmp)); _compile.

  apply Compile
  
  admit.
  admit.
Defined.

(* Set Printing All. *)
Set Printing Depth 1000.
Eval compute in (projT1 (progOKs Fin.F1)).
Extraction a.

(* HERE *)



Require Import
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.


Lemma CompileMap_SCA :
  forall {av A} `{FacadeWrapper av (list A)} `{FacadeWrapper av (list W)} `{FacadeWrapper (Value av) A}
    (lst: list A) vhead vhead' vtest vlst vret vtmp fpop fempty falloc fdealloc fcons facadeBody facadeCoda env (ext: StringMap.t (Value av)) tenv tenv' (f: A -> W),
    GLabelMap.MapsTo fpop (Axiomatic (List_pop A)) env ->
    GLabelMap.MapsTo fempty (Axiomatic (List_empty A)) env ->
    GLabelMap.MapsTo falloc (Axiomatic (FacadeImplementationOfConstructor (list W) nil)) env ->
    GLabelMap.MapsTo fdealloc (Axiomatic (FacadeImplementationOfDestructor (list A))) env ->
    GLabelMap.MapsTo fcons (Axiomatic (FacadeImplementationOfMutation_SCA (list W) cons)) env ->
    (* GLabelMap.MapsTo fdealloc_one (Axiomatic (FacadeImplementationOfDestructor A)) env -> *)
    PreconditionSet tenv ext [[[vhead; vhead'; vtest; vlst; vret; vtmp]]] ->
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv }}
      facadeCoda
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env ->
    (forall head (s: list A) (s': list W),
        {{ [[`vhead <-- head as _]] :: tenv }}
          facadeBody
        {{ [[`vhead' <-- f head as _]] :: tenv }} ∪
        {{ [vret <-- wrap s'] :: [vtest <-- wrap (bool2w false)] :: [vlst <-- wrap s] :: ext }} // env) ->
    {{ [[`vlst <-- lst as _]] :: tenv }}
      (Seq
         (Call vret falloc nil)
         (Seq
            (Seq
               (Fold vhead vtest vlst fpop fempty
                     (Seq facadeBody
                          (Call vtmp fcons (vret :: vhead' :: nil))))
               (Call vtest fdealloc (vlst :: nil)))
            facadeCoda))
    {{ [[`vret <-- (revmap f lst) as _]] :: tenv' }} ∪ {{ ext }} // env.
Proof.
  intros.
  setoid_rewrite <- revmap_fold_comp.
  apply CompileLoopAlloc; eauto.
  PreconditionSet_t; eauto.
  eapply (CompileCallFacadeImplementationOfConstructor (A := list W)); loop_t.
  setoid_rewrite revmap_fold_comp; eassumption.
  intros.
  rewrite SameValues_Fiat_Bind_TelEq.
  move_to_front vret.
  apply miniChomp'; intros.
  hoare.
  apply ProgOk_Chomp_Some; loop_t; defunctionalize_evar; eauto.
  apply CompileCallFacadeImplementationOfMutation_SCA; unfold DummyArgument; compile_do_side_conditions.
Qed.

(* NOTE: Could prove lemma for un-reved map using temp variable *)

























Definition CUnit (env := GLabelMap.empty _)
           (rWrap := projT1 SchedulerWrappers)
           (Scheduler_SideStuff := projT2 SchedulerWrappers)
  : BuildCompileUnit2T
      env PartialSchedulerImpl (DecomposeIndexedQueryStructure QsADTs.ADTValue)
      (DecomposeIndexedQueryStructurePre QsADTs.ADTValue _ _ rWrap)
      (DecomposeIndexedQueryStructurePost QsADTs.ADTValue _ _ rWrap)
      (QueryStructureSchema.numQSschemaSchemas SchedulerSchema)
      "foo"
      "bar"
      (Scheduler_SideStuff).(coDomainWrappers) (Scheduler_SideStuff).(domainWrappers)
      rWrap
      (Scheduler_SideStuff).(f'_well_behaved).
Proof.
  unfold rWrap, Scheduler_SideStuff; clear rWrap Scheduler_SideStuff.

  let sig := match type of PartialSchedulerImpl with Core.ADT ?sig => sig end in
  let methSigs := match sig with
                   DecADTSig ?DecSig => constr:(MethodNames DecSig) end in
  let methIdx := eval compute in (MethodIndex sig) in
      match methIdx with
      | Fin.t ?n =>
        list_of_evar DFFun n ltac:(fun z =>
                                     let map := constr:(BuildStringMap (Vector.fold_right cons methSigs nil) z) in
                                     let map' := (eval simpl in map) in
                                     eexists {| module := {| Funs := map'; Imports := GLabelMap.empty _ |} |})
      end.

  unfold CompileUnit2Equiv; repeat split.
  simpl; unfold DFModuleEquiv; simpl.
  eapply Fiat.Common.IterateBoundedIndex.Iterate_Ensemble_BoundedIndex_equiv.
  simpl; repeat split;
  eexists {| Core := {| Body := _ |};
             compiled_syntax_ok := _ |};
  
  simpl; repeat (apply conj); try exact (eq_refl); try decide_mapsto_maybe_instantiate; try eauto;

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
  intros; eapply (projT2 (progOKs Fin.F1)).
  intros; eapply (projT2 (progOKs (Fin.FS Fin.F1))).
  intros; eapply (projT2 (progOKs (Fin.FS (Fin.FS Fin.F1)))).
  Grab Existential Variables.

  Focus 10.

  Arguments ops_refines_axs {_} [_] _ _.

  simpl Funs.

  unfold GenExports. cbv [BuildFinUpTo].
  simpl.

  unfold ops_refines_axs.

  intros.

  StringMap_t.

  Ltac StringMap_iterate_over_specs :=
    match goal with
    | [ H: StringMap.MapsTo ?x _ (StringMap.add ?x' _ _) |- _ ] =>
      destruct (StringMap.E.eq_dec x x');
        [ subst; apply MapsTo_add_eq_inv in H; subst | apply StringMap.add_3 in H; try discriminate ]
    end.

  
  StringMap_iterate_over_specs.
  2:StringMap_iterate_over_specs.
  3:StringMap_iterate_over_specs.

  
  
  
  apply StringMap.add_ in H.
  
  match goal with
  | [  |- context[StringMap.map Core _ ] ] => cbv [StringMap.map StringMap.Raw.map]; simpl
  end.
  
  
  Notation op_refine 
  
  lazymatch goal with
  | [ |- appcontext[ops_refines_axs ?env] ] => set (en := env)
  end.
    unfold ops_refines_axs.
    intros * h.

    destruct (string_dec x "Spawn"); subst.
    simpl in h.
    cbv [StringMap.find StringMap.Raw.find] in h.
    simpl in h.
    match goal with
    | H: Some ?a = Some ?b |- _ => assert (a = b)
    end.
    Focus 2.
    clear h.
    unfold GenAxiomaticSpecs, AxiomatizeMethodPre, AxiomatizeMethodPost in H.
    simpl in H.
    simpl.
    cbv [StringMap.find StringMap.Raw.find].
    simpl.
    eexists ; split; try reflexivity.
    unfold op_refines_ax.
    simpl.
    repeat split.

    Focus 3.
    pose proof (projT2 (progOKs Fin.F1)).

    unfold GenExports.
    simpl.

    cbv [get_env].
    unfold GLabelMap.map, map_aug_mod_name.
    simpl.
    unfold GLabelMapFacts.UWFacts.WFacts.P.update, GLabelMapFacts.M.fold, GLabelMapFacts.M.add.
    simpl.
    unfold GLabelMapFacts.M.Raw.fold, GLabelMap.Raw.map. simpl.
    subst. 
    unfold AxSafe.
    simpl; intros.
    repeat cleanup.
    simpl in H0; specialize (H0 x0 x1 x2).
    unfold ProgOk in H0.
    assert (st ≲ [[ ` "arg" <-- x2 as _]]::[[ ` "arg0" <-- x1 as _]]::[[ ` "rep" <-- prim_fst x0 as _]]::Nil ∪ ∅).
    simpl.
    rewrite H1.
    StringMap_t.
    eexists; repeat split; eauto.
    admit.
    admit.
    Focus 3.
    unfold AxRunsTo.
    rewrite <- H.
    simpl.
    unfold AxSafe; intros.
    eexists; eexists; repeat split.
    Focus 3.
    rewrite H1.
    StringMap_t.
    
    
    Print Safe.
    match goal with
    | [ |- Safe ?M _ _] => set (M' := M); clearbody M'
    end.
    

  - 
     
    unfold ; simpl.
    specialize (H0 x0 x1 x2).
    AxSa
    simpl ax
    Show Existentials.
    simpl.
    Safe
    unfold GLabelMapFacts.UWFacts.WFacts.P.update
        (GLabelMap.map (Axiomatic (ADTValue:=QsADTs.ADTValue))
           (map_aug_mod_name
aug_mod
    Focus
    simpl.

    Print RawHeading.
    repeat match goal with
           | |- context[@RawTuple ?hd] => let num := (eval simpl in (NumAttr hd)) in
                                        let pr := constr:(eq_refl hd : hd = (MakeWordHeading num)) in
                                        change hd with (MakeWordHeading num)
           end.                 (* FIXME *)
    
    Ltac _compile_CallBagFind_internal :=
      match_ProgOk
        ltac:(fun prog pre post ext env =>
                match constr:(pre, post) with
                | (Cons (NTSome ?vdb) (ret (prim_fst ?db)) (fun _ => ?tenv), Cons NTNone ?bf _) =>
                  match bf with
                  | CallBagMethod Fin.F1 BagFind ?db (Some ?v, (None, fun _ => true)) =>
                    let vsnd := gensym "snd" in
                    let vtmp := gensym "tmp" in
                    let vkwd := find_fast (wrap v) ext in
                    match vkwd with
                      Some ?vkwd =>
                      let stmt := constr:(Call (DummyArgument vtmp) ("ext", "BagFind") (vsnd :: vdb :: vkwd :: nil)) in
                      let T_bf := type of bf in
                      let T_bf := (eval simpl in T_bf) in
                      let wp := fresh "wrapper" in
                      match T_bf with
                      | Comp (_ * ?t) => evar (wp : FacadeWrapper QsADTs.ADTValue t)
                      end;
                        eapply CompileSeq with ([[bf as retv]]
                                                  :: [[`vdb <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                         (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                                         (icons3 SearchUpdateTerm inil3) db Fin.F1 (fst retv))
                                                       as _]]
                                                  :: [[`vsnd <-- snd retv as s]]
                                                  :: tenv);
                        [ try match_ProgOk ltac:(fun prog' _ _ _ _ => unify prog' stmt) | ]
                    end
                  end
                end).

    _compile_CallBagFind_internal.
      simpl.
      (* FIXME make prim_fst opaque? *)
      repeat match goal with
      | [  |- appcontext [?v] ] =>
        match v with
          | NTSome _ => set v
        end
             end.
      simpl.
      Show Existentials.
      evar (wrapper : FacadeWrapper QsADTs.ADTValue T0).
      simpl in T.

      
      Goal FacadeWrapper (list RawTuple
      Print Ltac find_fast.

      

    Ltac _compile_CallBagFind_internal :=
      match_ProgOk
        ltac:(fun prog pre post ext env =>
                match constr:(pre, post) with
                | (Cons (NTSome ?vdb) (ret (prim_fst ?db)) (fun _ => Cons (NTSome ?vd) (ret ?d) ?tenv), Cons NTNone ?bf _) =>
                  let vsnd := gensym "snd" in
                  let vtmp := gensym "tmp" in
                  let stmt := constr:(Call (DummyArgument vtmp) ("ext", "BagFind") (vsnd :: vdb :: vd :: nil)) in
                  apply CompileSeq with ([[bf as retv]]
                                           :: [[`vdb <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                  (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                                  (icons3 SearchUpdateTerm inil3) db Fin.F1 (fst retv))
                                                as _]]
                                           :: [[`vsnd <-- snd retv as s]]
                                           :: [[`vd <-- d as _]]
                                           :: (tenv d));
                    [ try match_ProgOk ltac:(fun prog' _ _ _ _ => unify prog' stmt) | ]
                end).

    Ltac _compile_CallBagFind :=
      first [_compile_CallBagFind_internal
            | match_ProgOk
                ltac:(fun prog pre post ext env =>
                        match constr:post with
                        | Cons NTNone (CallBagMethod ?id BagFind ?db (Some ?d, _)) ?tenv' =>
                          match pre with
                          | context[Cons (NTSome ?vdb) (ret (prim_fst db)) _] =>
                            match pre with
                            | context[Cons (NTSome ?vd) (ret d) ?tenv] =>
                              move_to_front vd; move_to_front vdb;
                              _compile_CallBagFind_internal
                            end
                          end
                        end)].

  _compile_CallBagFind.

  clear.
  admit.

  repeat match goal with
         | [ H: _ |- _ ] => clear dependent H
         end.
  unfold If_Then_Else.
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
  instantiate (1 := Call (DummyArgument "tmp") ("List", "empty?") ("rep" :: nil)).
  admit.
  repeat match goal with
         | [ H: _ |- _ ] => clear dependent H
         end.
  (* Typeclasses Opaque CallBagMethod. *)
  (* Opaque Refinements.UpdateIndexedRelation. *)
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.
  _compile_step.

  Ltac _compile_CallBagInsert_Internal :=
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons ?vdb (ret (prim_fst ?db)) (fun _ => ?tenv),
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

    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons ?vdb (ret (prim_fst ?db)) (fun _ => ?tenv),
                 Cons NTNone ?bm (fun a => Cons ?vdb' (@?rel a) (fun _ => ?tenv'))) =>
                replace vdb with vdb' by admit;
                pose vdb; pose vdb'
                (* unify vdb vdb' *)
                  (* match constr:(vdb, bm, rel) with *)
                  (* | (NTSome ?vdb', CallBagMethod ?id BagInsert ?db _, (fun a => ret (Refinements.UpdateIndexedRelation _ _ ?db' ?id a))) => *)
                  (*   unify db db'; *)
                  (*     let vtmp := gensym "tmp" in *)
                  (*     apply CompileSeq with (Cons NTNone bm (fun a => Cons vdb (rel a) (fun _ => tenv))); (* FIXME hardcoded var names *) *)
                  (*       [ match_ProgOk *)
                  (*           ltac:(fun prog' _ _ _ _ => *)
                  (*                   unify prog' (Call (DummyArgument "tmp") ("ext", "BagInsert") (vdb' :: "d" :: "d0" :: nil))) | ] *)
                  (* end *)
              end).


    compute in n.
    compute in n0.

    replace n with n0 by admit.
    unfold n, n0; clear n n0.

    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:(pre, post) with
              | (Cons ?vdb (ret (prim_fst ?db)) (fun _ => ?tenv),
                 Cons NTNone ?bm (fun a => Cons ?vdb' (@?rel a) (fun _ => ?tenv'))) =>
                pose vdb; pose vdb'

                  (* match constr:(vdb, bm, rel) with *)
                  (* | (NTSome ?vdb', CallBagMethod ?id BagInsert ?db _, (fun a => ret (Refinements.UpdateIndexedRelation _ _ ?db' ?id a))) => *)
                  (*   unify db db'; *)
                  (*     let vtmp := gensym "tmp" in *)
                  (*     apply CompileSeq with (Cons NTNone bm (fun a => Cons vdb (rel a) (fun _ => tenv))); (* FIXME hardcoded var names *) *)
                  (*       [ match_ProgOk *)
                  (*           ltac:(fun prog' _ _ _ _ => *)
                  (*                   unify prog' (Call (DummyArgument "tmp") ("ext", "BagInsert") (vdb' :: "d" :: "d0" :: nil))) | ] *)
                  (* end *)
              end).
    
    f_equal.
    
  _compile_CallBagInsert_Internal.
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
  Print Ltac _compile_prepare_chomp.
  match_ProgOk
    ltac:(fun prog pre post ext env => __compile_prepare_chomp pre post).

  
  _compile_step.
  _compile_step.
  _compile_step.
  
    
    match_ProgOk
      ltac:(fun prog pre post ext env =>
              match constr:post with
              | Cons NTNone (CallBagMethod ?id BagFind ?db (Some ?d, _)) ?tenv' =>
                match pre with
                | context[Cons (NTSome (H := ?H) ?vdb) (ret (prim_fst db)) _] =>
                  match pre with
                  | context[Cons (NTSome (H := ?H2) ?vd) (ret d) ?tenv] =>
                    let vsnd := gensym "snd" in
                    let vtmp := gensym "tmp" in
                    match post with
                    | Cons NTNone ?bf _ =>
                      let stmt := constr:(Call (DummyArgument vtmp) ("ext", "BagFind") (vsnd :: vdb :: vd :: nil)) in
                      pose stmt;
                        move_to_front "arg0";
                        move_to_front "rep";
                        apply CompileSeq with ([[bf as retv]]
                                                 :: [[(NTSome (H := H) vdb) <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                                        (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                                                        (icons3 SearchUpdateTerm inil3) db Fin.F1 (fst retv))
                                                      as _]]
                                                 :: [[(NTSome (H := (X _)) vsnd) <-- snd retv as s]]
                                                 :: [[(NTSome (H := H2) vd) <-- d as _]]
                                                 :: (tenv d));
                        [ try match_ProgOk ltac:(fun prog' _ _ _ _ => unify prog' stmt) (* FIXME fails bc of evars *) | ]
                          
                    end
                  end
                end
              end).

  instantiate (1 := Call "blah" ("blah", "blah") [[[ "hi" ]]]).
    assert True.
    clear H t r d d0 rWrap.
    clear.
    assert (s = s).

    instantiate (4 := s).
    clear.
    clear t.
    Set Printing All.
    idtac.
    admit.
  Print Ltac _compile_CallBagFind.


                     _ _ adt.



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
  eexists {| Core := {| Body := _ |};
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

  intros.

  Definition FinToWord {N: nat} (n: Fin.t N) :=
    Word.natToWord 32 (proj1_sig (Fin.to_nat n)).

  Definition FitsInW {N: nat} (n: Fin.t N) :=
    Word.wordToNat (FinToWord n) = proj1_sig (Fin.to_nat n).

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
              match constr:post with
              | Cons NTNone (CallBagMethod ?id BagFind ?db (Some ?d, _)) ?tenv' =>
                match pre with
                | context[Cons (NTSome ?vdb) (ret (prim_fst db)) _] =>
                  match pre with
                  | context[Cons (NTSome ?vd) (ret d) ?tenv] =>
                    let vsnd := gensym "snd" in
                    let vtmp := gensym "tmp" in
                    match post with
                    | Cons NTNone ?bf _ =>
                      let stmt := constr:(Call (DummyArgument vtmp) ("ext", "BagFind") (vsnd :: vdb :: vd :: nil)) in
                      pose stmt;
                        move_to_front "arg0";
                        move_to_front "rep";
                        eapply CompileSeq with ([[bf as retv]]
                                                  :: [[`vdb <-- prim_fst (Refinements.UpdateIndexedRelation
                                                                         (QueryStructureSchema.QueryStructureSchemaRaw SchedulerSchema)
                                                                         (icons3 SearchUpdateTerm inil3) db Fin.F1 (fst retv))
                                                       as _]]
                                                  :: [[`vsnd <-- snd retv as s]]
                                                  :: [[`vd <-- d as _]]
                                                  :: (tenv d));
                        [ try match_ProgOk ltac:(fun prog' _ _ _ _ => unify prog' stmt) (* FIXME fails bc of evars *) | ]
                    end
                  end
                end
              end).


  _compile.
  _compile_CallBagFind.
  (* unfold CallBagMethod.         (* FIXME *) *)

  (* apply ProgOk_Chomp_None. FIXME evars *)

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
  := {module : DFModule ADTValue |
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
Definition ADTValue := (list W + TSearchTerm + TAcc)%type.

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

Example other_test_with_adtB'' `{FacadeWrapper ADTValue (list W)}:
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
