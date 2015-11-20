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


  Lemma map_rev_def :
    forall {A B} f seq,
      @map A B f (rev seq) = revmap f seq.
  Proof.
    intros; reflexivity.
  Qed.

  Ltac _compile_map ::=
       match_ProgOk
       ltac:(fun prog pre post ext env =>
               let vhead := gensym "head" in
               let vhead' := gensym "head'" in
               let vtest := gensym "test" in
               let vtmp := gensym "tmp" in
               match constr:(pre, post) with
               | (Cons (NTSome ?vseq) (ret ?seq) ?tenv, Cons (NTSome ?vret) (ret (revmap _ ?seq')) ?tenv') =>
                 unify seq seq';
                   apply (CompileMap_TuplesToWords (N := 3) seq (vhead := vhead) (vhead' := vhead') (vtest := vtest) (vtmp := vtmp))
               end).


  Lemma CompileTuple_Get_helper :
    forall N (idx: (Fin.t N)), (@Vector.nth Type (NumAttr (MakeWordHeading N)) (AttrList (MakeWordHeading N)) idx) = W.
  Proof.
    induction idx; eauto.
  Defined.

    Lemma CompileTuple_get_helper:
      forall (N : nat) (idx : Fin.t N),
        BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
        IL.goodSize (` (Fin.to_nat idx)).
    Proof.
      intros *.
      pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
      apply NPeano.Nat.le_exists_sub in h; repeat cleanup.
      assert (IL.goodSize N) as h.
      eassumption.
      rewrite H0 in h.
      eapply Arrays.goodSize_plus_r.
      rewrite NPeano.Nat.add_succ_r in h.
      rewrite <- NPeano.Nat.add_succ_l in h.
      eassumption.
    Defined.

Lemma CompileTuple_get_helper':
    forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      Word.wlt (Word.natToWord 32 (` (Fin.to_nat idx))) (IL.natToW (Datatypes.length (TupleToListW tup))).
  Proof.
    intros. rewrite TupleToListW_length by assumption.
    rewrite Word.wordToNat_natToWord_idempotent by assumption.
    pose proof (proj2_sig (Fin.to_nat idx)) as h; simpl in h.
    apply Arrays.lt_goodSize; try eassumption.
    apply CompileTuple_get_helper; assumption.
  Qed.

  Hint Resolve CompileTuple_get_helper' : call_helpers_db.
      
  Lemma CompileTuple_get_helper'':
    forall (N : nat) (tup : FiatTuple N) (idx : Fin.t N),
      BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
      (match CompileTuple_Get_helper idx in (_ = W) return (Vector.nth (MakeVectorOfW N) idx -> W) with
       | eq_refl => fun t : Vector.nth (MakeVectorOfW N) idx => t
       end (ilist2.ith2 tup idx)) = Array.sel (TupleToListW tup) (Word.natToWord 32 (` (Fin.to_nat idx))).
  Proof.
    unfold Array.sel.
    intros.
    rewrite Word.wordToNat_natToWord_idempotent by (apply (CompileTuple_get_helper idx); assumption).
    induction idx; simpl; try rewrite IHidx.
    - reflexivity.
    - destruct tup; simpl.
      unfold TupleToListW, ilist2.ilist2_hd, ilist2.ilist2_tl; simpl.
      destruct (Fin.to_nat idx); simpl; reflexivity.
    - apply BinNat.N.lt_succ_l.
      rewrite Nnat.Nat2N.inj_succ in H.
      assumption.
  Qed.

Lemma CompileTuple_Get:
  forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
    vtup <> vret ->
    vret ∉ ext ->
    Lifted_MapsTo ext tenv vtup (wrap (FacadeWrapper := WrapInstance (H := (QS_WrapTuple (N := N)))) tup) ->
    Lifted_MapsTo ext tenv vpos (wrap (Word.natToWord 32 (proj1_sig (Fin.to_nat idx)))) ->
    Lifted_not_mapsto_adt ext tenv vret ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic Tuple_get) env ->
    {{ tenv }}
      Call vret fpointer (vtup :: vpos :: nil)
      {{ [[(NTSome (H := FacadeWrapper_SCA) vret) <--
                                                 (match CompileTuple_Get_helper idx in _ = W return _ -> W with
                                                  | eq_refl => fun t => t
                                                  end) (ilist2.ith2 tup idx) as _]]
           :: (DropName vret tenv) }} ∪ {{ ext }} // env.
Proof.
  repeat (SameValues_Facade_t_step || facade_cleanup_call || LiftPropertyToTelescope_t || PreconditionSet_t).

  facade_eauto.
  rewrite <- CompileTuple_get_helper'' by congruence; reflexivity.
  rewrite <- remove_add_comm by congruence.
  setoid_rewrite <- add_redundant_cancel; try eassumption.
  repeat apply DropName_remove; eauto 1.
Qed.

Lemma CompileTuple_Get_spec:
  forall (vret vtup vpos : StringMap.key) (env : GLabelMap.t (FuncSpec ADTValue)) (tenv: Telescope ADTValue) ext N
    (fpointer : GLabelMap.key) (tup : FiatTuple N) (idx: Fin.t N),
    PreconditionSet tenv ext [[[vtup; vret; vpos]]] ->
    vret ∉ ext ->
    vtup ∉ ext ->
    NotInTelescope vret tenv ->
    BinNat.N.lt (BinNat.N.of_nat N) (Word.Npow2 32) ->
    GLabelMap.MapsTo fpointer (Axiomatic Tuple_get) env ->
    {{ [[ `vtup <-- tup as _ ]] :: tenv }}
      (Seq (Assign vpos (Const (Word.natToWord 32 (proj1_sig (Fin.to_nat idx))))) (Call vret fpointer (vtup :: vpos :: nil)))
    {{ [[ `vtup <-- tup  as _]]
         :: [[(NTSome (H := FacadeWrapper_SCA) vret) <-- (match CompileTuple_Get_helper idx in _ = W return _ -> W with
                                                      | eq_refl => fun t => t
                                                      end) (ilist2.ith2 tup idx) as _]]
         :: tenv }} ∪ {{ ext }} // env.
Proof.
  intros.
  hoare.
  apply CompileConstant; try compile_do_side_conditions.
  apply CompileDeallocSCA_discretely; try compile_do_side_conditions.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.
  apply ProgOk_Chomp_Some; try compile_do_side_conditions; intros.

  remember (match CompileTuple_Get_helper idx in (_ = W) return (Vector.nth (AttrList (MakeWordHeading N)) idx -> W) with
      | eq_refl => fun t : Vector.nth (AttrList (MakeWordHeading N)) idx => t
            end (ilist2.ith2 tup idx)). (* Otherwise Coq crashes *)
  setoid_replace tenv with (DropName vret tenv) using relation (@TelStrongEq ADTValue) at 2.
  computes_to_inv;
    subst; apply CompileTuple_Get; repeat (PreconditionSet_t || compile_do_side_conditions || decide_not_in || Lifted_t).
  apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
  apply Lifted_MapsTo_Ext; decide_mapsto_maybe_instantiate.
  symmetry; apply DropName_NotInTelescope; assumption.
Qed.

Ltac _compile_get :=
  match_ProgOk
    ltac:(fun prog pre post ext env =>
            let vtmp := gensym "tmp" in
            match constr:(pre, post) with
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

Print Env.
Definition QSEnv : Env ADTValue :=
  (GLabelMap.empty _)
  ### ("ADT", "Tuple_new") ->> (Axiomatic Tuple_new)
  ### ("ADT", "Tuple_delete") ->> (Axiomatic Tuple_delete)
  ### ("ADT", "Tuple_copy") ->> (Axiomatic Tuple_copy)
  ### ("ADT", "Tuple_get") ->> (Axiomatic Tuple_get)
  ### ("ADT", "Tuple_set") ->> (Axiomatic Tuple_set)

  ### ("ADT", "WordList_new") ->> (Axiomatic WordList_new)
  ### ("ADT", "WordList_delete") ->> (Axiomatic WordList_delete)
  ### ("ADT", "WordList_pop") ->> (Axiomatic WordList_pop)
  ### ("ADT", "WordList_empty") ->> (Axiomatic WordList_empty)
  ### ("ADT", "WordList_push") ->> (Axiomatic WordList_push)
  ### ("ADT", "WordList_copy") ->> (Axiomatic WordList_copy)
  ### ("ADT", "WordList_rev") ->> (Axiomatic WordList_rev)
  ### ("ADT", "WordList_length") ->> (Axiomatic WordList_length)

  ### ("ADT", "TupleList_new") ->> (Axiomatic TupleList_new)
  ### ("ADT", "TupleList_delete") ->> (Axiomatic TupleList_delete)
  ### ("ADT", "TupleList_copy") ->> (Axiomatic TupleList_copy)
  ### ("ADT", "TupleList_pop") ->> (Axiomatic TupleList_pop)
  ### ("ADT", "TupleList_empty") ->> (Axiomatic TupleList_empty)
  ### ("ADT", "TupleList_push") ->> (Axiomatic TupleList_push)
  ### ("ADT", "TupleList_rev") ->> (Axiomatic TupleList_rev)
  ### ("ADT", "TupleList_length") ->> (Axiomatic TupleList_length)

  ### ("ADT", "Tuples0_new") ->> (Axiomatic Tuples0_new)
  ### ("ADT", "Tuples0_insert") ->> (Axiomatic Tuples0_insert)
  ### ("ADT", "Tuples0_enumerate") ->> (Axiomatic Tuples0_enumerate)

  ### ("ADT", "Tuples1_new") ->> (Axiomatic Tuples1_new)
  ### ("ADT", "Tuples1_insert") ->> (Axiomatic Tuples1_insert)
  ### ("ADT", "Tuples1_find") ->> (Axiomatic Tuples1_find)
  ### ("ADT", "Tuples1_enumerate") ->> (Axiomatic Tuples1_enumerate)

  ### ("ADT", "Tuples2_new") ->> (Axiomatic Tuples2_new)
  ### ("ADT", "Tuples2_insert") ->> (Axiomatic Tuples2_insert)
  ### ("ADT", "Tuples2_findBoth") ->> (Axiomatic Tuples2_findBoth)
  ### ("ADT", "Tuples2_findFirst") ->> (Axiomatic Tuples2_findFirst)
  ### ("ADT", "Tuples2_findSecond") ->> (Axiomatic Tuples2_findSecond)
  ### ("ADT", "Tuples2_enumerate") ->> (Axiomatic Tuples2_enumerate).

Ltac _qs_step :=
  match goal with
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

Ltac _compile :=
  repeat _qs_step.

Lemma progOKs
  : forall (env := QSEnv)
      (rWrap := projT1 SchedulerWrappers)
      (Scheduler_SideStuff := projT2 SchedulerWrappers)
      midx, {prog : _ & LiftMethod env (DecomposeIndexedQueryStructure _ rWrap)
                                   (coDomainWrappers Scheduler_SideStuff midx)
                                   (domainWrappers Scheduler_SideStuff midx)
                                   prog (Methods PartialSchedulerImpl midx)}.
Proof.
  start_compiling_adt.
  
  _compile.

  admit.
  instantiate (1 := 0); admit.
  
  _compile.
  admit.

  _compile.
  admit.
Defined.

(* The three methods: *)

Eval compute in (projT1 (progOKs (Fin.F1))).
Eval compute in (projT1 (progOKs (Fin.FS Fin.F1))).
Eval compute in (projT1 (progOKs (Fin.FS (Fin.FS Fin.F1)))).

Require Import
        CertifiedExtraction.Extraction.Internal
        CertifiedExtraction.Extraction.External.Core
        CertifiedExtraction.Extraction.External.Loops
        CertifiedExtraction.Extraction.External.GenericADTMethods
        CertifiedExtraction.Extraction.External.FacadeADTs.


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
    
    